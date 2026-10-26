import V185TrunkScan23Chunk0028

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_172152 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_172152 : Nat := 118140960795 + 172152 * 2 ^ 59
def prefixEnd_172152 : Nat := 4983230072969 + 3 ^ 40 * 172152 * 2
def baseEnd_172152 : Nat := 88396721632915688208293

theorem tailTrace_172152 : CollatzResearch.WordTrace tailWord_172152 prefixEnd_172152 88396721632915688208293 := by
  unfold tailWord_172152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139449636165090032979355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4185932848220120043972473 3139449636165090032979355)
  ·
    refine ⟨4709174454247635049469033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3139449636165090032979355 4709174454247635049469033)
    ·
      refine ⟨3531880840685726287101775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4709174454247635049469033 3531880840685726287101775)
      ·
        refine ⟨5297821261028589430652663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531880840685726287101775 5297821261028589430652663)
        ·
          refine ⟨7946731891542884145978995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5297821261028589430652663 7946731891542884145978995)
          ·
            refine ⟨11920097837314326218968493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7946731891542884145978995 11920097837314326218968493)
            ·
              refine ⟨4470036688992872332113185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11920097837314326218968493 4470036688992872332113185)
              ·
                refine ⟨3352527516744654249084889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470036688992872332113185 3352527516744654249084889)
                ·
                  refine ⟨2514395637558490686813667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3352527516744654249084889 2514395637558490686813667)
                  ·
                    refine ⟨3771593456337736030220501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2514395637558490686813667 3771593456337736030220501)
                    ·
                      refine ⟨88396721632915688208293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3771593456337736030220501 88396721632915688208293)
                      ·
                        rfl

theorem cell23_172152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_172152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172152 prefixEnd_172152 := by exact prefixLift 172152
  have htrace : WordTrace (prefixWord ++ tailWord_172152) baseStart_172152 baseEnd_172152 := by
    simpa [prefixWord, tailWord_172152, baseEnd_172152] using wordTrace_append hprefix tailTrace_172152
  have hstable : (prefixWord ++ tailWord_172152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172152).length < 2 ^ (prefixWord ++ tailWord_172152).sum := by decide
  have hdescent : baseEnd_172152 < baseStart_172152 := by decide
  rcases family_descends (prefixWord ++ tailWord_172152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172189 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 3, 6]
def baseStart_172189 : Nat := 118140960795 + 172189 * 2 ^ 59
def prefixEnd_172189 : Nat := 4983230072969 + 3 ^ 40 * 172189 * 2
def baseEnd_172189 : Nat := 29471906805710681148541

theorem tailTrace_172189 : CollatzResearch.WordTrace tailWord_172189 prefixEnd_172189 29471906805710681148541 := by
  unfold tailWord_172189
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280248773196135385055621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4186832515464090256703747 6280248773196135385055621)
  ·
    refine ⟨1177546644974275384697929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6280248773196135385055621 1177546644974275384697929)
    ·
      refine ⟨883159983730706538523447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1177546644974275384697929 883159983730706538523447)
      ·
        refine ⟨1324739975596059807785171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883159983730706538523447 1324739975596059807785171)
        ·
          refine ⟨1987109963394089711677757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324739975596059807785171 1987109963394089711677757)
          ·
            refine ⟨745166236272783641879159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1987109963394089711677757 745166236272783641879159)
            ·
              refine ⟨1117749354409175462818739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745166236272783641879159 1117749354409175462818739)
              ·
                refine ⟨1676624031613763194228109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117749354409175462818739 1676624031613763194228109)
                ·
                  refine ⟨628734011855161197835541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1676624031613763194228109 628734011855161197835541)
                  ·
                    refine ⟨29471906805710681148541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 628734011855161197835541 29471906805710681148541)
                    ·
                      rfl

theorem cell23_172189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_172189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172189 prefixEnd_172189 := by exact prefixLift 172189
  have htrace : WordTrace (prefixWord ++ tailWord_172189) baseStart_172189 baseEnd_172189 := by
    simpa [prefixWord, tailWord_172189, baseEnd_172189] using wordTrace_append hprefix tailTrace_172189
  have hstable : (prefixWord ++ tailWord_172189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172189).length < 2 ^ (prefixWord ++ tailWord_172189).sum := by decide
  have hdescent : baseEnd_172189 < baseStart_172189 := by decide
  rcases family_descends (prefixWord ++ tailWord_172189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172193 : List Nat := [1, 2, 3, 3, 1, 3, 3, 1, 1, 5]
def baseStart_172193 : Nat := 118140960795 + 172193 * 2 ^ 59
def prefixEnd_172193 : Nat := 4983230072969 + 3 ^ 40 * 172193 * 2
def baseEnd_172193 : Nat := 29472591446583342598535

theorem tailTrace_172193 : CollatzResearch.WordTrace tailWord_172193 prefixEnd_172193 29472591446583342598535 := by
  unfold tailWord_172193
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280394665181644068201233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4186929776787762712134155 6280394665181644068201233)
  ·
    refine ⟨4710295998886233051150925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6280394665181644068201233 4710295998886233051150925)
    ·
      refine ⟨1766360999582337394181597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4710295998886233051150925 1766360999582337394181597)
      ·
        refine ⟨662385374843376522818099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1766360999582337394181597 662385374843376522818099)
        ·
          refine ⟨993578062265064784227149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662385374843376522818099 993578062265064784227149)
          ·
            refine ⟨372591773349399294085181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 993578062265064784227149 372591773349399294085181)
            ·
              refine ⟨139721915006024735281943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372591773349399294085181 139721915006024735281943)
              ·
                refine ⟨209582872509037102922915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139721915006024735281943 209582872509037102922915)
                ·
                  refine ⟨314374308763555654384373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209582872509037102922915 314374308763555654384373)
                  ·
                    refine ⟨29472591446583342598535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 314374308763555654384373 29472591446583342598535)
                    ·
                      rfl

theorem cell23_172193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_172193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172193 prefixEnd_172193 := by exact prefixLift 172193
  have htrace : WordTrace (prefixWord ++ tailWord_172193) baseStart_172193 baseEnd_172193 := by
    simpa [prefixWord, tailWord_172193, baseEnd_172193] using wordTrace_append hprefix tailTrace_172193
  have hstable : (prefixWord ++ tailWord_172193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172193).length < 2 ^ (prefixWord ++ tailWord_172193).sum := by decide
  have hdescent : baseEnd_172193 < baseStart_172193 := by decide
  rcases family_descends (prefixWord ++ tailWord_172193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172309 : List Nat := [1, 3, 2, 1, 2, 1, 2, 2, 9]
def baseStart_172309 : Nat := 118140960795 + 172309 * 2 ^ 59
def prefixEnd_172309 : Nat := 4983230072969 + 3 ^ 40 * 172309 * 2
def baseEnd_172309 : Nat := 9830815343963508216119

theorem tailTrace_172309 : CollatzResearch.WordTrace tailWord_172309 prefixEnd_172309 9830815343963508216119 := by
  unfold tailWord_172309
  simp only [CollatzResearch.WordTrace]
  refine ⟨6284625532761395879423981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4189750355174263919615987 6284625532761395879423981)
  ·
    refine ⟨2356734574785523454783993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6284625532761395879423981 2356734574785523454783993)
    ·
      refine ⟨1767550931089142591087995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2356734574785523454783993 1767550931089142591087995)
      ·
        refine ⟨2651326396633713886631993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767550931089142591087995 2651326396633713886631993)
        ·
          refine ⟨1988494797475285414973995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651326396633713886631993 1988494797475285414973995)
          ·
            refine ⟨2982742196212928122460993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988494797475285414973995 2982742196212928122460993)
            ·
              refine ⟨2237056647159696091845745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2982742196212928122460993 2237056647159696091845745)
              ·
                refine ⟨1677792485369772068884309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2237056647159696091845745 1677792485369772068884309)
                ·
                  refine ⟨9830815343963508216119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1677792485369772068884309 9830815343963508216119)
                  ·
                    rfl

theorem cell23_172309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 9].length) (baseStart_172309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172309 prefixEnd_172309 := by exact prefixLift 172309
  have htrace : WordTrace (prefixWord ++ tailWord_172309) baseStart_172309 baseEnd_172309 := by
    simpa [prefixWord, tailWord_172309, baseEnd_172309] using wordTrace_append hprefix tailTrace_172309
  have hstable : (prefixWord ++ tailWord_172309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172309).length < 2 ^ (prefixWord ++ tailWord_172309).sum := by decide
  have hdescent : baseEnd_172309 < baseStart_172309 := by decide
  rcases family_descends (prefixWord ++ tailWord_172309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172320 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2]
def baseStart_172320 : Nat := 118140960795 + 172320 * 2 ^ 59
def prefixEnd_172320 : Nat := 4983230072969 + 3 ^ 40 * 172320 * 2
def baseEnd_172320 : Nat := 88482986382871030907521

theorem tailTrace_172320 : CollatzResearch.WordTrace tailWord_172320 prefixEnd_172320 88482986382871030907521 := by
  unfold tailWord_172320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3142513367860772379037207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4190017823814363172049609 3142513367860772379037207)
  ·
    refine ⟨4713770051791158568555811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3142513367860772379037207 4713770051791158568555811)
    ·
      refine ⟨7070655077686737852833717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4713770051791158568555811 7070655077686737852833717)
      ·
        refine ⟨662873913533131673703161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7070655077686737852833717 662873913533131673703161)
        ·
          refine ⟨497155435149848755277371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662873913533131673703161 497155435149848755277371)
          ·
            refine ⟨745733152724773132916057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497155435149848755277371 745733152724773132916057)
            ·
              refine ⟨559299864543579849687043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745733152724773132916057 559299864543579849687043)
              ·
                refine ⟨838949796815369774530565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559299864543579849687043 838949796815369774530565)
                ·
                  refine ⟨157303086902881832724481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 838949796815369774530565 157303086902881832724481)
                  ·
                    refine ⟨117977315177161374543361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157303086902881832724481 117977315177161374543361)
                    ·
                      refine ⟨88482986382871030907521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117977315177161374543361 88482986382871030907521)
                      ·
                        rfl

theorem cell23_172320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_172320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172320 prefixEnd_172320 := by exact prefixLift 172320
  have htrace : WordTrace (prefixWord ++ tailWord_172320) baseStart_172320 baseEnd_172320 := by
    simpa [prefixWord, tailWord_172320, baseEnd_172320] using wordTrace_append hprefix tailTrace_172320
  have hstable : (prefixWord ++ tailWord_172320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172320).length < 2 ^ (prefixWord ++ tailWord_172320).sum := by decide
  have hdescent : baseEnd_172320 < baseStart_172320 := by decide
  rcases family_descends (prefixWord ++ tailWord_172320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172337 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 2, 2, 2]
def baseStart_172337 : Nat := 118140960795 + 172337 * 2 ^ 59
def prefixEnd_172337 : Nat := 4983230072969 + 3 ^ 40 * 172337 * 2
def baseEnd_172337 : Nat := 88491715553997464394943

theorem tailTrace_172337 : CollatzResearch.WordTrace tailWord_172337 prefixEnd_172337 88491715553997464394943 := by
  unfold tailWord_172337
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285646776659956661443265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4190431184439971107628843 6285646776659956661443265)
  ·
    refine ⟨4714235082494967496082449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6285646776659956661443265 4714235082494967496082449)
    ·
      refine ⟨3535676311871225622061837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4714235082494967496082449 3535676311871225622061837)
      ·
        refine ⟨1325878616951709608273189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3535676311871225622061837 1325878616951709608273189)
        ·
          refine ⟨248602240678445551551223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1325878616951709608273189 248602240678445551551223)
          ·
            refine ⟨372903361017668327326835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248602240678445551551223 372903361017668327326835)
            ·
              refine ⟨559355041526502490990253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372903361017668327326835 559355041526502490990253)
              ·
                refine ⟨209758140572438434121345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559355041526502490990253 209758140572438434121345)
                ·
                  refine ⟨157318605429328825591009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 209758140572438434121345 157318605429328825591009)
                  ·
                    refine ⟨117988954071996619193257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157318605429328825591009 117988954071996619193257)
                    ·
                      refine ⟨88491715553997464394943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 117988954071996619193257 88491715553997464394943)
                      ·
                        rfl

theorem cell23_172337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_172337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172337 prefixEnd_172337 := by exact prefixLift 172337
  have htrace : WordTrace (prefixWord ++ tailWord_172337) baseStart_172337 baseEnd_172337 := by
    simpa [prefixWord, tailWord_172337, baseEnd_172337] using wordTrace_append hprefix tailTrace_172337
  have hstable : (prefixWord ++ tailWord_172337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172337).length < 2 ^ (prefixWord ++ tailWord_172337).sum := by decide
  have hdescent : baseEnd_172337 < baseStart_172337 := by decide
  rcases family_descends (prefixWord ++ tailWord_172337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172376 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_172376 : Nat := 118140960795 + 172376 * 2 ^ 59
def prefixEnd_172376 : Nat := 4983230072969 + 3 ^ 40 * 172376 * 2
def baseEnd_172376 : Nat := 88511741299522811807263

theorem tailTrace_172376 : CollatzResearch.WordTrace tailWord_172376 prefixEnd_172376 88511741299522811807263 := by
  unfold tailWord_172376
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143534611759333161056491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4191379482345777548075321 3143534611759333161056491)
  ·
    refine ⟨4715301917638999741584737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3143534611759333161056491 4715301917638999741584737)
    ·
      refine ⟨3536476438229249806188553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4715301917638999741584737 3536476438229249806188553)
      ·
        refine ⟨2652357328671937354641415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3536476438229249806188553 2652357328671937354641415)
        ·
          refine ⟨3978535993007906031962123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652357328671937354641415 3978535993007906031962123)
          ·
            refine ⟨5967803989511859047943185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3978535993007906031962123 5967803989511859047943185)
            ·
              refine ⟨4475852992133894285957389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5967803989511859047943185 4475852992133894285957389)
              ·
                refine ⟨1678444872050210357234021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4475852992133894285957389 1678444872050210357234021)
                ·
                  refine ⟨314708413509414441981379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678444872050210357234021 314708413509414441981379)
                  ·
                    refine ⟨472062620264121662972069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314708413509414441981379 472062620264121662972069)
                    ·
                      refine ⟨88511741299522811807263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 472062620264121662972069 88511741299522811807263)
                      ·
                        rfl

theorem cell23_172376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_172376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172376 prefixEnd_172376 := by exact prefixLift 172376
  have htrace : WordTrace (prefixWord ++ tailWord_172376) baseStart_172376 baseEnd_172376 := by
    simpa [prefixWord, tailWord_172376, baseEnd_172376] using wordTrace_append hprefix tailTrace_172376
  have hstable : (prefixWord ++ tailWord_172376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172376).length < 2 ^ (prefixWord ++ tailWord_172376).sum := by decide
  have hdescent : baseEnd_172376 < baseStart_172376 := by decide
  rcases family_descends (prefixWord ++ tailWord_172376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172393 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 2, 4, 2]
def baseStart_172393 : Nat := 118140960795 + 172393 * 2 ^ 59
def prefixEnd_172393 : Nat := 4983230072969 + 3 ^ 40 * 172393 * 2
def baseEnd_172393 : Nat := 88520470470649245294685

theorem tailTrace_172393 : CollatzResearch.WordTrace tailWord_172393 prefixEnd_172393 88520470470649245294685 := by
  unfold tailWord_172393
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287689264457078225481833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4191792842971385483654555 6287689264457078225481833)
  ·
    refine ⟨4715766948342808669111375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6287689264457078225481833 4715766948342808669111375)
    ·
      refine ⟨7073650422514213003667063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4715766948342808669111375 7073650422514213003667063)
      ·
        refine ⟨10610475633771319505500595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7073650422514213003667063 10610475633771319505500595)
        ·
          refine ⟨15915713450656979258250893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610475633771319505500595 15915713450656979258250893)
          ·
            refine ⟨5968392543996367221844085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15915713450656979258250893 5968392543996367221844085)
            ·
              refine ⟨559536800999659427047883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5968392543996367221844085 559536800999659427047883)
              ·
                refine ⟨839305201499489140571825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559536800999659427047883 839305201499489140571825)
                ·
                  refine ⟨629478901124616855428869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839305201499489140571825 629478901124616855428869)
                  ·
                    refine ⟨118027293960865660392913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629478901124616855428869 118027293960865660392913)
                    ·
                      refine ⟨88520470470649245294685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118027293960865660392913 88520470470649245294685)
                      ·
                        rfl

theorem cell23_172393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 4, 2].length) (baseStart_172393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172393 prefixEnd_172393 := by exact prefixLift 172393
  have htrace : WordTrace (prefixWord ++ tailWord_172393) baseStart_172393 baseEnd_172393 := by
    simpa [prefixWord, tailWord_172393, baseEnd_172393] using wordTrace_append hprefix tailTrace_172393
  have hstable : (prefixWord ++ tailWord_172393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172393).length < 2 ^ (prefixWord ++ tailWord_172393).sum := by decide
  have hdescent : baseEnd_172393 < baseStart_172393 := by decide
  rcases family_descends (prefixWord ++ tailWord_172393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172413 : List Nat := [1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_172413 : Nat := 118140960795 + 172413 * 2 ^ 59
def prefixEnd_172413 : Nat := 4983230072969 + 3 ^ 40 * 172413 * 2
def baseEnd_172413 : Nat := 88530740083739167044593

theorem tailTrace_172413 : CollatzResearch.WordTrace tailWord_172413 prefixEnd_172413 88530740083739167044593 := by
  unfold tailWord_172413
  simp only [CollatzResearch.WordTrace]
  refine ⟨6288418724384621641209893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4192279149589747760806595 6288418724384621641209893)
  ·
    refine ⟨1179078510822116557726855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6288418724384621641209893 1179078510822116557726855)
    ·
      refine ⟨1768617766233174836590283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179078510822116557726855 1768617766233174836590283)
      ·
        refine ⟨2652926649349762254885425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768617766233174836590283 2652926649349762254885425)
        ·
          refine ⟨1989694987012321691164069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2652926649349762254885425 1989694987012321691164069)
          ·
            refine ⟨373067810064810317093263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1989694987012321691164069 373067810064810317093263)
            ·
              refine ⟨559601715097215475639895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373067810064810317093263 559601715097215475639895)
              ·
                refine ⟨839402572645823213459843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559601715097215475639895 839402572645823213459843)
                ·
                  refine ⟨1259103858968734820189765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839402572645823213459843 1259103858968734820189765)
                  ·
                    refine ⟨236081973556637778785581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1259103858968734820189765 236081973556637778785581)
                    ·
                      refine ⟨88530740083739167044593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 236081973556637778785581 88530740083739167044593)
                      ·
                        rfl

theorem cell23_172413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_172413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172413 prefixEnd_172413 := by exact prefixLift 172413
  have htrace : WordTrace (prefixWord ++ tailWord_172413) baseStart_172413 baseEnd_172413 := by
    simpa [prefixWord, tailWord_172413, baseEnd_172413] using wordTrace_append hprefix tailTrace_172413
  have hstable : (prefixWord ++ tailWord_172413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172413).length < 2 ^ (prefixWord ++ tailWord_172413).sum := by decide
  have hdescent : baseEnd_172413 < baseStart_172413 := by decide
  rcases family_descends (prefixWord ++ tailWord_172413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172450 : List Nat := [3, 3, 1, 2, 1, 1, 5, 1, 6]
def baseStart_172450 : Nat := 118140960795 + 172450 * 2 ^ 59
def prefixEnd_172450 : Nat := 4983230072969 + 3 ^ 40 * 172450 * 2
def baseEnd_172450 : Nat := 9838859874217280253547

theorem tailTrace_172450 : CollatzResearch.WordTrace tailWord_172450 prefixEnd_172450 9838859874217280253547 := by
  unfold tailWord_172450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572442056312644240076701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4193178816833717973537869 1572442056312644240076701)
  ·
    refine ⟨589665771117241590028763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1572442056312644240076701 589665771117241590028763)
    ·
      refine ⟨884498656675862385043145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589665771117241590028763 884498656675862385043145)
      ·
        refine ⟨663373992506896788782359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 884498656675862385043145 663373992506896788782359)
        ·
          refine ⟨995060988760345183173539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663373992506896788782359 995060988760345183173539)
          ·
            refine ⟨1492591483140517774760309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995060988760345183173539 1492591483140517774760309)
            ·
              refine ⟨139930451544423541383779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1492591483140517774760309 139930451544423541383779)
              ·
                refine ⟨209895677316635312075669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139930451544423541383779 209895677316635312075669)
                ·
                  refine ⟨9838859874217280253547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 209895677316635312075669 9838859874217280253547)
                  ·
                    rfl

theorem cell23_172450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_172450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172450 prefixEnd_172450 := by exact prefixLift 172450
  have htrace : WordTrace (prefixWord ++ tailWord_172450) baseStart_172450 baseEnd_172450 := by
    simpa [prefixWord, tailWord_172450, baseEnd_172450] using wordTrace_append hprefix tailTrace_172450
  have hstable : (prefixWord ++ tailWord_172450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172450).length < 2 ^ (prefixWord ++ tailWord_172450).sum := by decide
  have hdescent : baseEnd_172450 < baseStart_172450 := by decide
  rcases family_descends (prefixWord ++ tailWord_172450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172453 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 3, 5, 2]
def baseStart_172453 : Nat := 118140960795 + 172453 * 2 ^ 59
def prefixEnd_172453 : Nat := 4983230072969 + 3 ^ 40 * 172453 * 2
def baseEnd_172453 : Nat := 88551279309919010544409

theorem tailTrace_172453 : CollatzResearch.WordTrace tailWord_172453 prefixEnd_172453 88551279309919010544409 := by
  unfold tailWord_172453
  simp only [CollatzResearch.WordTrace]
  refine ⟨6289877644239708472666013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4193251762826472315110675 6289877644239708472666013)
  ·
    refine ⟨2358704116589890677249755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6289877644239708472666013 2358704116589890677249755)
    ·
      refine ⟨3538056174884836015874633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358704116589890677249755 3538056174884836015874633)
      ·
        refine ⟨2653542131163627011905975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3538056174884836015874633 2653542131163627011905975)
        ·
          refine ⟨3980313196745440517858963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653542131163627011905975 3980313196745440517858963)
          ·
            refine ⟨5970469795118160776788445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980313196745440517858963 5970469795118160776788445)
            ·
              refine ⟨2238926173169310291295667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5970469795118160776788445 2238926173169310291295667)
              ·
                refine ⟨3358389259753965436943501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238926173169310291295667 3358389259753965436943501)
                ·
                  refine ⟨1259395972407737038853813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3358389259753965436943501 1259395972407737038853813)
                  ·
                    refine ⟨118068372413225347392545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1259395972407737038853813 118068372413225347392545)
                    ·
                      refine ⟨88551279309919010544409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118068372413225347392545 88551279309919010544409)
                      ·
                        rfl

theorem cell23_172453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_172453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172453 prefixEnd_172453 := by exact prefixLift 172453
  have htrace : WordTrace (prefixWord ++ tailWord_172453) baseStart_172453 baseEnd_172453 := by
    simpa [prefixWord, tailWord_172453, baseEnd_172453] using wordTrace_append hprefix tailTrace_172453
  have hstable : (prefixWord ++ tailWord_172453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172453).length < 2 ^ (prefixWord ++ tailWord_172453).sum := by decide
  have hdescent : baseEnd_172453 < baseStart_172453 := by decide
  rcases family_descends (prefixWord ++ tailWord_172453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172496 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_172496 : Nat := 118140960795 + 172496 * 2 ^ 59
def prefixEnd_172496 : Nat := 4983230072969 + 3 ^ 40 * 172496 * 2
def baseEnd_172496 : Nat := 88573358978062342306711

theorem tailTrace_172496 : CollatzResearch.WordTrace tailWord_172496 prefixEnd_172496 88573358978062342306711 := by
  unfold tailWord_172496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3145722991541963408240671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4194297322055951210987561 3145722991541963408240671)
  ·
    refine ⟨4718584487312945112361007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3145722991541963408240671 4718584487312945112361007)
    ·
      refine ⟨7077876730969417668541511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4718584487312945112361007 7077876730969417668541511)
      ·
        refine ⟨10616815096454126502812267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7077876730969417668541511 10616815096454126502812267)
        ·
          refine ⟨15925222644681189754218401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10616815096454126502812267 15925222644681189754218401)
          ·
            refine ⟨11943916983510892315663801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15925222644681189754218401 11943916983510892315663801)
            ·
              refine ⟨8957937737633169236747851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11943916983510892315663801 8957937737633169236747851)
              ·
                refine ⟨13436906606449753855121777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8957937737633169236747851 13436906606449753855121777)
                ·
                  refine ⟨10077679954837315391341333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13436906606449753855121777 10077679954837315391341333)
                  ·
                    refine ⟨472391247882999158969125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10077679954837315391341333 472391247882999158969125)
                    ·
                      refine ⟨88573358978062342306711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 472391247882999158969125 88573358978062342306711)
                      ·
                        rfl

theorem cell23_172496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_172496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172496 prefixEnd_172496 := by exact prefixLift 172496
  have htrace : WordTrace (prefixWord ++ tailWord_172496) baseStart_172496 baseEnd_172496 := by
    simpa [prefixWord, tailWord_172496, baseEnd_172496] using wordTrace_append hprefix tailTrace_172496
  have hstable : (prefixWord ++ tailWord_172496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172496).length < 2 ^ (prefixWord ++ tailWord_172496).sum := by decide
  have hdescent : baseEnd_172496 < baseStart_172496 := by decide
  rcases family_descends (prefixWord ++ tailWord_172496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172513 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 4]
def baseStart_172513 : Nat := 118140960795 + 172513 * 2 ^ 59
def prefixEnd_172513 : Nat := 4983230072969 + 3 ^ 40 * 172513 * 2
def baseEnd_172513 : Nat := 88582088149188775794133

theorem tailTrace_172513 : CollatzResearch.WordTrace tailWord_172513 prefixEnd_172513 88582088149188775794133 := by
  unfold tailWord_172513
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292066024022338719850193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4194710682681559146566795 6292066024022338719850193)
  ·
    refine ⟨4719049518016754039887645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6292066024022338719850193 4719049518016754039887645)
    ·
      refine ⟨1769643569256282764957867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4719049518016754039887645 1769643569256282764957867)
      ·
        refine ⟨2654465353884424147436801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769643569256282764957867 2654465353884424147436801)
        ·
          refine ⟨1990849015413318110577601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2654465353884424147436801 1990849015413318110577601)
          ·
            refine ⟨1493136761559988582933201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990849015413318110577601 1493136761559988582933201)
            ·
              refine ⟨1119852571169991437199901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493136761559988582933201 1119852571169991437199901)
              ·
                refine ⟨419944714188746788949963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119852571169991437199901 419944714188746788949963)
                ·
                  refine ⟨629917071283120183424945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419944714188746788949963 629917071283120183424945)
                  ·
                    refine ⟨472437803462340137568709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629917071283120183424945 472437803462340137568709)
                    ·
                      refine ⟨88582088149188775794133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 472437803462340137568709 88582088149188775794133)
                      ·
                        rfl

theorem cell23_172513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_172513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172513 prefixEnd_172513 := by exact prefixLift 172513
  have htrace : WordTrace (prefixWord ++ tailWord_172513) baseStart_172513 baseEnd_172513 := by
    simpa [prefixWord, tailWord_172513, baseEnd_172513] using wordTrace_append hprefix tailTrace_172513
  have hstable : (prefixWord ++ tailWord_172513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172513).length < 2 ^ (prefixWord ++ tailWord_172513).sum := by decide
  have hdescent : baseEnd_172513 < baseStart_172513 := by decide
  rcases family_descends (prefixWord ++ tailWord_172513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172520 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_172520 : Nat := 118140960795 + 172520 * 2 ^ 59
def prefixEnd_172520 : Nat := 4983230072969 + 3 ^ 40 * 172520 * 2
def baseEnd_172520 : Nat := 88585682513770248406601

theorem tailTrace_172520 : CollatzResearch.WordTrace tailWord_172520 prefixEnd_172520 88585682513770248406601 := by
  unfold tailWord_172520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146160667498489457677507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4194880889997985943570009 3146160667498489457677507)
  ·
    refine ⟨4719241001247734186516261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146160667498489457677507 4719241001247734186516261)
    ·
      refine ⟨884857687733950159971799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4719241001247734186516261 884857687733950159971799)
      ·
        refine ⟨1327286531600925239957699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884857687733950159971799 1327286531600925239957699)
        ·
          refine ⟨1990929797401387859936549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327286531600925239957699 1990929797401387859936549)
          ·
            refine ⟨373299337012760223738103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1990929797401387859936549 373299337012760223738103)
            ·
              refine ⟨559949005519140335607155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373299337012760223738103 559949005519140335607155)
              ·
                refine ⟨839923508278710503410733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559949005519140335607155 839923508278710503410733)
                ·
                  refine ⟨314971315604516438779025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839923508278710503410733 314971315604516438779025)
                  ·
                    refine ⟨236228486703387329084269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314971315604516438779025 236228486703387329084269)
                    ·
                      refine ⟨88585682513770248406601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 236228486703387329084269 88585682513770248406601)
                      ·
                        rfl

theorem cell23_172520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_172520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172520 prefixEnd_172520 := by exact prefixLift 172520
  have htrace : WordTrace (prefixWord ++ tailWord_172520) baseStart_172520 baseEnd_172520 := by
    simpa [prefixWord, tailWord_172520, baseEnd_172520] using wordTrace_append hprefix tailTrace_172520
  have hstable : (prefixWord ++ tailWord_172520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172520).length < 2 ^ (prefixWord ++ tailWord_172520).sum := by decide
  have hdescent : baseEnd_172520 < baseStart_172520 := by decide
  rcases family_descends (prefixWord ++ tailWord_172520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172551 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_172551 : Nat := 118140960795 + 172551 * 2 ^ 59
def prefixEnd_172551 : Nat := 4983230072969 + 3 ^ 40 * 172551 * 2
def baseEnd_172551 : Nat := 88601600414059627118959

theorem tailTrace_172551 : CollatzResearch.WordTrace tailWord_172551 prefixEnd_172551 88601600414059627118959 := by
  unfold tailWord_172551
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293451997884671209733507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4195634665256447473155671 6293451997884671209733507)
  ·
    refine ⟨9440177996827006814600261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6293451997884671209733507 9440177996827006814600261)
    ·
      refine ⟨1770033374405063777737549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9440177996827006814600261 1770033374405063777737549)
      ·
        refine ⟨663762515401898916651581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1770033374405063777737549 663762515401898916651581)
        ·
          refine ⟨248910943275712093744343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 663762515401898916651581 248910943275712093744343)
          ·
            refine ⟨373366414913568140616515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248910943275712093744343 373366414913568140616515)
            ·
              refine ⟨560049622370352210924773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373366414913568140616515 560049622370352210924773)
              ·
                refine ⟨105009304194441039548395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 560049622370352210924773 105009304194441039548395)
                ·
                  refine ⟨157513956291661559322593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105009304194441039548395 157513956291661559322593)
                  ·
                    refine ⟨118135467218746169491945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157513956291661559322593 118135467218746169491945)
                    ·
                      refine ⟨88601600414059627118959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118135467218746169491945 88601600414059627118959)
                      ·
                        rfl

theorem cell23_172551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_172551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172551 prefixEnd_172551 := by exact prefixLift 172551
  have htrace : WordTrace (prefixWord ++ tailWord_172551) baseStart_172551 baseEnd_172551 := by
    simpa [prefixWord, tailWord_172551, baseEnd_172551] using wordTrace_append hprefix tailTrace_172551
  have hstable : (prefixWord ++ tailWord_172551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172551).length < 2 ^ (prefixWord ++ tailWord_172551).sum := by decide
  have hdescent : baseEnd_172551 < baseStart_172551 := by decide
  rcases family_descends (prefixWord ++ tailWord_172551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172557 : List Nat := [1, 7, 1, 1, 1, 1, 3, 8]
def baseStart_172557 : Nat := 118140960795 + 172557 * 2 ^ 59
def prefixEnd_172557 : Nat := 4983230072969 + 3 ^ 40 * 172557 * 2
def baseEnd_172557 : Nat := 3281654862888392727553

theorem tailTrace_172557 : CollatzResearch.WordTrace tailWord_172557 prefixEnd_172557 3281654862888392727553 := by
  unfold tailWord_172557
  simp only [CollatzResearch.WordTrace]
  refine ⟨6293670835862934234451925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4195780557241956156301283 6293670835862934234451925)
  ·
    refine ⟨147507910215537521119967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6293670835862934234451925 147507910215537521119967)
    ·
      refine ⟨221261865323306281679951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147507910215537521119967 221261865323306281679951)
      ·
        refine ⟨331892797984959422519927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221261865323306281679951 331892797984959422519927)
        ·
          refine ⟨497839196977439133779891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331892797984959422519927 497839196977439133779891)
          ·
            refine ⟨746758795466158700669837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497839196977439133779891 746758795466158700669837)
            ·
              refine ⟨280034548299809512751189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 746758795466158700669837 280034548299809512751189)
              ·
                refine ⟨3281654862888392727553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 280034548299809512751189 3281654862888392727553)
                ·
                  rfl

theorem cell23_172557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 8].length) (baseStart_172557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172557 prefixEnd_172557 := by exact prefixLift 172557
  have htrace : WordTrace (prefixWord ++ tailWord_172557) baseStart_172557 baseEnd_172557 := by
    simpa [prefixWord, tailWord_172557, baseEnd_172557] using wordTrace_append hprefix tailTrace_172557
  have hstable : (prefixWord ++ tailWord_172557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172557).length < 2 ^ (prefixWord ++ tailWord_172557).sum := by decide
  have hdescent : baseEnd_172557 < baseStart_172557 := by decide
  rcases family_descends (prefixWord ++ tailWord_172557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172577 : List Nat := [1, 2, 3, 2, 2, 1, 2, 4, 1, 3, 2]
def baseStart_172577 : Nat := 118140960795 + 172577 * 2 ^ 59
def prefixEnd_172577 : Nat := 4983230072969 + 3 ^ 40 * 172577 * 2
def baseEnd_172577 : Nat := 88614950911076525393839

theorem tailTrace_172577 : CollatzResearch.WordTrace tailWord_172577 prefixEnd_172577 88614950911076525393839 := by
  unfold tailWord_172577
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294400295790477650179985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4196266863860318433453323 6294400295790477650179985)
  ·
    refine ⟨4720800221842858237634989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6294400295790477650179985 4720800221842858237634989)
    ·
      refine ⟨1770300083191071839113121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4720800221842858237634989 1770300083191071839113121)
      ·
        refine ⟨1327725062393303879334841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770300083191071839113121 1327725062393303879334841)
        ·
          refine ⟨995793796794977909501131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327725062393303879334841 995793796794977909501131)
          ·
            refine ⟨1493690695192466864251697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995793796794977909501131 1493690695192466864251697)
            ·
              refine ⟨1120268021394350148188773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493690695192466864251697 1120268021394350148188773)
              ·
                refine ⟨210050254011440652785395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1120268021394350148188773 210050254011440652785395)
                ·
                  refine ⟨315075381017160979178093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210050254011440652785395 315075381017160979178093)
                  ·
                    refine ⟨118153267881435367191785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315075381017160979178093 118153267881435367191785)
                    ·
                      refine ⟨88614950911076525393839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118153267881435367191785 88614950911076525393839)
                      ·
                        rfl

theorem cell23_172577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_172577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172577 prefixEnd_172577 := by exact prefixLift 172577
  have htrace : WordTrace (prefixWord ++ tailWord_172577) baseStart_172577 baseEnd_172577 := by
    simpa [prefixWord, tailWord_172577, baseEnd_172577] using wordTrace_append hprefix tailTrace_172577
  have hstable : (prefixWord ++ tailWord_172577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172577).length < 2 ^ (prefixWord ++ tailWord_172577).sum := by decide
  have hdescent : baseEnd_172577 < baseStart_172577 := by decide
  rcases family_descends (prefixWord ++ tailWord_172577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172593 : List Nat := [1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 5]
def baseStart_172593 : Nat := 118140960795 + 172593 * 2 ^ 59
def prefixEnd_172593 : Nat := 4983230072969 + 3 ^ 40 * 172593 * 2
def baseEnd_172593 : Nat := 88623166601548462793765

theorem tailTrace_172593 : CollatzResearch.WordTrace tailWord_172593 prefixEnd_172593 88623166601548462793765 := by
  unfold tailWord_172593
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294983863732512382762433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4196655909155008255174955 6294983863732512382762433)
  ·
    refine ⟨4721237897799384287071825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6294983863732512382762433 4721237897799384287071825)
    ·
      refine ⟨3540928423349538215303869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4721237897799384287071825 3540928423349538215303869)
      ·
        refine ⟨1327848158756076830738951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3540928423349538215303869 1327848158756076830738951)
        ·
          refine ⟨1991772238134115246108427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327848158756076830738951 1991772238134115246108427)
          ·
            refine ⟨2987658357201172869162641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991772238134115246108427 2987658357201172869162641)
            ·
              refine ⟨2240743767900879651871981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987658357201172869162641 2240743767900879651871981)
              ·
                refine ⟨840278912962829869451993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240743767900879651871981 840278912962829869451993)
                ·
                  refine ⟨630209184722122402088995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 840278912962829869451993 630209184722122402088995)
                  ·
                    refine ⟨945313777083183603133493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630209184722122402088995 945313777083183603133493)
                    ·
                      refine ⟨88623166601548462793765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 945313777083183603133493 88623166601548462793765)
                      ·
                        rfl

theorem cell23_172593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_172593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172593 prefixEnd_172593 := by exact prefixLift 172593
  have htrace : WordTrace (prefixWord ++ tailWord_172593) baseStart_172593 baseEnd_172593 := by
    simpa [prefixWord, tailWord_172593, baseEnd_172593] using wordTrace_append hprefix tailTrace_172593
  have hstable : (prefixWord ++ tailWord_172593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172593).length < 2 ^ (prefixWord ++ tailWord_172593).sum := by decide
  have hdescent : baseEnd_172593 < baseStart_172593 := by decide
  rcases family_descends (prefixWord ++ tailWord_172593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172594 : List Nat := [3, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2]
def baseStart_172594 : Nat := 118140960795 + 172594 * 2 ^ 59
def prefixEnd_172594 : Nat := 4983230072969 + 3 ^ 40 * 172594 * 2
def baseEnd_172594 : Nat := 88623680082202958881261

theorem tailTrace_172594 : CollatzResearch.WordTrace tailWord_172594 prefixEnd_172594 88623680082202958881261 := by
  unfold tailWord_172594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573755084182222388387209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4196680224485926369032557 1573755084182222388387209)
  ·
    refine ⟨1180316313136666791290407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1573755084182222388387209 1180316313136666791290407)
    ·
      refine ⟨1770474469705000186935611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180316313136666791290407 1770474469705000186935611)
      ·
        refine ⟨2655711704557500280403417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770474469705000186935611 2655711704557500280403417)
        ·
          refine ⟨1991783778418125210302563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655711704557500280403417 1991783778418125210302563)
          ·
            refine ⟨2987675667627187815453845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991783778418125210302563 2987675667627187815453845)
            ·
              refine ⟨140047296920024428849399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2987675667627187815453845 140047296920024428849399)
              ·
                refine ⟨210070945380036643274099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140047296920024428849399 210070945380036643274099)
                ·
                  refine ⟨315106418070054964911149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210070945380036643274099 315106418070054964911149)
                  ·
                    refine ⟨118164906776270611841681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315106418070054964911149 118164906776270611841681)
                    ·
                      refine ⟨88623680082202958881261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118164906776270611841681 88623680082202958881261)
                      ·
                        rfl

theorem cell23_172594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2].length) (baseStart_172594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172594 prefixEnd_172594 := by exact prefixLift 172594
  have htrace : WordTrace (prefixWord ++ tailWord_172594) baseStart_172594 baseEnd_172594 := by
    simpa [prefixWord, tailWord_172594, baseEnd_172594] using wordTrace_append hprefix tailTrace_172594
  have hstable : (prefixWord ++ tailWord_172594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172594).length < 2 ^ (prefixWord ++ tailWord_172594).sum := by decide
  have hdescent : baseEnd_172594 < baseStart_172594 := by decide
  rcases family_descends (prefixWord ++ tailWord_172594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172607 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 4, 2, 2]
def baseStart_172607 : Nat := 118140960795 + 172607 * 2 ^ 59
def prefixEnd_172607 : Nat := 4983230072969 + 3 ^ 40 * 172607 * 2
def baseEnd_172607 : Nat := 88630355330711408018701

theorem tailTrace_172607 : CollatzResearch.WordTrace tailWord_172607 prefixEnd_172607 88630355330711408018701 := by
  unfold tailWord_172607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295494485681792773772075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4196996323787861849181383 6295494485681792773772075)
  ·
    refine ⟨9443241728522689160658113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6295494485681792773772075 9443241728522689160658113)
    ·
      refine ⟨7082431296392016870493585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9443241728522689160658113 7082431296392016870493585)
      ·
        refine ⟨5311823472294012652870189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7082431296392016870493585 5311823472294012652870189)
        ·
          refine ⟨1991933802110254744826321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5311823472294012652870189 1991933802110254744826321)
          ·
            refine ⟨1493950351582691058619741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1991933802110254744826321 1493950351582691058619741)
            ·
              refine ⟨560231381843509146982403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493950351582691058619741 560231381843509146982403)
              ·
                refine ⟨840347072765263720473605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560231381843509146982403 840347072765263720473605)
                ·
                  refine ⟨157565076143486947588801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 840347072765263720473605 157565076143486947588801)
                  ·
                    refine ⟨118173807107615210691601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 157565076143486947588801 118173807107615210691601)
                    ·
                      refine ⟨88630355330711408018701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118173807107615210691601 88630355330711408018701)
                      ·
                        rfl

theorem cell23_172607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_172607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172607 prefixEnd_172607 := by exact prefixLift 172607
  have htrace : WordTrace (prefixWord ++ tailWord_172607) baseStart_172607 baseEnd_172607 := by
    simpa [prefixWord, tailWord_172607, baseEnd_172607] using wordTrace_append hprefix tailTrace_172607
  have hstable : (prefixWord ++ tailWord_172607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172607).length < 2 ^ (prefixWord ++ tailWord_172607).sum := by decide
  have hdescent : baseEnd_172607 < baseStart_172607 := by decide
  rcases family_descends (prefixWord ++ tailWord_172607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172613 : List Nat := [1, 3, 1, 1, 1, 5, 1, 3, 7]
def baseStart_172613 : Nat := 118140960795 + 172613 * 2 ^ 59
def prefixEnd_172613 : Nat := 4983230072969 + 3 ^ 40 * 172613 * 2
def baseEnd_172613 : Nat := 9848159579404264949297

theorem tailTrace_172613 : CollatzResearch.WordTrace tailWord_172613 prefixEnd_172613 9848159579404264949297 := by
  unfold tailWord_172613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295713323660055798490493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4197142215773370532326995 6295713323660055798490493)
  ·
    refine ⟨2360892496372520924433935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6295713323660055798490493 2360892496372520924433935)
    ·
      refine ⟨3541338744558781386650903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360892496372520924433935 3541338744558781386650903)
      ·
        refine ⟨5312008116838172079976355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3541338744558781386650903 5312008116838172079976355)
        ·
          refine ⟨7968012175257258119964533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312008116838172079976355 7968012175257258119964533)
          ·
            refine ⟨747001141430367948746675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7968012175257258119964533 747001141430367948746675)
            ·
              refine ⟨1120501712145551923120013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747001141430367948746675 1120501712145551923120013)
              ·
                refine ⟨420188142054581971170005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1120501712145551923120013 420188142054581971170005)
                ·
                  refine ⟨9848159579404264949297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 420188142054581971170005 9848159579404264949297)
                  ·
                    rfl

theorem cell23_172613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 3, 7].length) (baseStart_172613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172613 prefixEnd_172613 := by exact prefixLift 172613
  have htrace : WordTrace (prefixWord ++ tailWord_172613) baseStart_172613 baseEnd_172613 := by
    simpa [prefixWord, tailWord_172613, baseEnd_172613] using wordTrace_append hprefix tailTrace_172613
  have hstable : (prefixWord ++ tailWord_172613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172613).length < 2 ^ (prefixWord ++ tailWord_172613).sum := by decide
  have hdescent : baseEnd_172613 < baseStart_172613 := by decide
  rcases family_descends (prefixWord ++ tailWord_172613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172643 : List Nat := [1, 1, 1, 5, 1, 2, 1, 3, 1, 7]
def baseStart_172643 : Nat := 118140960795 + 172643 * 2 ^ 59
def prefixEnd_172643 : Nat := 4983230072969 + 3 ^ 40 * 172643 * 2
def baseEnd_172643 : Nat := 29549613544757755722845

theorem tailTrace_172643 : CollatzResearch.WordTrace tailWord_172643 prefixEnd_172643 29549613544757755722845 := by
  unfold tailWord_172643
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296807513551370922082583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4197871675700913948055055 6296807513551370922082583)
  ·
    refine ⟨9445211270327056383123875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6296807513551370922082583 9445211270327056383123875)
    ·
      refine ⟨14167816905490584574685813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445211270327056383123875 14167816905490584574685813)
      ·
        refine ⟨1328232834889742303876795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14167816905490584574685813 1328232834889742303876795)
        ·
          refine ⟨1992349252334613455815193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328232834889742303876795 1992349252334613455815193)
          ·
            refine ⟨1494261939250960091861395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992349252334613455815193 1494261939250960091861395)
            ·
              refine ⟨2241392908876440137792093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494261939250960091861395 2241392908876440137792093)
              ·
                refine ⟨840522340828665051672035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2241392908876440137792093 840522340828665051672035)
                ·
                  refine ⟨1260783511242997577508053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840522340828665051672035 1260783511242997577508053)
                  ·
                    refine ⟨29549613544757755722845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1260783511242997577508053 29549613544757755722845)
                    ·
                      rfl

theorem cell23_172643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 7].length) (baseStart_172643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172643 prefixEnd_172643 := by exact prefixLift 172643
  have htrace : WordTrace (prefixWord ++ tailWord_172643) baseStart_172643 baseEnd_172643 := by
    simpa [prefixWord, tailWord_172643, baseEnd_172643] using wordTrace_append hprefix tailTrace_172643
  have hstable : (prefixWord ++ tailWord_172643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172643).length < 2 ^ (prefixWord ++ tailWord_172643).sum := by decide
  have hdescent : baseEnd_172643 < baseStart_172643 := by decide
  rcases family_descends (prefixWord ++ tailWord_172643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172693 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_172693 : Nat := 118140960795 + 172693 * 2 ^ 59
def prefixEnd_172693 : Nat := 4983230072969 + 3 ^ 40 * 172693 * 2
def baseEnd_172693 : Nat := 88674514666998071543305

theorem tailTrace_172693 : CollatzResearch.WordTrace tailWord_172693 prefixEnd_172693 88674514666998071543305 := by
  unfold tailWord_172693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6298631163370229461402733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4199087442246819640935155 6298631163370229461402733)
  ·
    refine ⟨2361986686263836048026025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6298631163370229461402733 2361986686263836048026025)
    ·
      refine ⟨1771490014697877036019519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2361986686263836048026025 1771490014697877036019519)
      ·
        refine ⟨2657235022046815554029279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771490014697877036019519 2657235022046815554029279)
        ·
          refine ⟨3985852533070223331043919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657235022046815554029279 3985852533070223331043919)
          ·
            refine ⟨5978778799605334996565879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985852533070223331043919 5978778799605334996565879)
            ·
              refine ⟨8968168199408002494848819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978778799605334996565879 8968168199408002494848819)
              ·
                refine ⟨13452252299112003742273229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8968168199408002494848819 13452252299112003742273229)
                ·
                  refine ⟨5044594612167001403352461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13452252299112003742273229 5044594612167001403352461)
                  ·
                    refine ⟨1891722979562625526257173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5044594612167001403352461 1891722979562625526257173)
                    ·
                      refine ⟨88674514666998071543305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1891722979562625526257173 88674514666998071543305)
                      ·
                        rfl

theorem cell23_172693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_172693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172693 prefixEnd_172693 := by exact prefixLift 172693
  have htrace : WordTrace (prefixWord ++ tailWord_172693) baseStart_172693 baseEnd_172693 := by
    simpa [prefixWord, tailWord_172693, baseEnd_172693] using wordTrace_append hprefix tailTrace_172693
  have hstable : (prefixWord ++ tailWord_172693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172693).length < 2 ^ (prefixWord ++ tailWord_172693).sum := by decide
  have hdescent : baseEnd_172693 < baseStart_172693 := by decide
  rcases family_descends (prefixWord ++ tailWord_172693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172767 : List Nat := [1, 1, 2, 3, 2, 4, 1, 3, 1, 5]
def baseStart_172767 : Nat := 118140960795 + 172767 * 2 ^ 59
def prefixEnd_172767 : Nat := 4983230072969 + 3 ^ 40 * 172767 * 2
def baseEnd_172767 : Nat := 29570837411810260672655

theorem tailTrace_172767 : CollatzResearch.WordTrace tailWord_172767 prefixEnd_172767 29570837411810260672655 := by
  unfold tailWord_172767
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301330165102140099596555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4200886776734760066397703 6301330165102140099596555)
  ·
    refine ⟨9451995247653210149394833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6301330165102140099596555 9451995247653210149394833)
    ·
      refine ⟨7088996435739907612046125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9451995247653210149394833 7088996435739907612046125)
      ·
        refine ⟨2658373663402465354517297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7088996435739907612046125 2658373663402465354517297)
        ·
          refine ⟨1993780247551849015887973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2658373663402465354517297 1993780247551849015887973)
          ·
            refine ⟨373833796415971690478995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1993780247551849015887973 373833796415971690478995)
            ·
              refine ⟨560750694623957535718493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373833796415971690478995 560750694623957535718493)
              ·
                refine ⟨210281510483984075894435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 560750694623957535718493 210281510483984075894435)
                ·
                  refine ⟨315422265725976113841653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210281510483984075894435 315422265725976113841653)
                  ·
                    refine ⟨29570837411810260672655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 315422265725976113841653 29570837411810260672655)
                    ·
                      rfl

theorem cell23_172767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_172767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172767 prefixEnd_172767 := by exact prefixLift 172767
  have htrace : WordTrace (prefixWord ++ tailWord_172767) baseStart_172767 baseEnd_172767 := by
    simpa [prefixWord, tailWord_172767, baseEnd_172767] using wordTrace_append hprefix tailTrace_172767
  have hstable : (prefixWord ++ tailWord_172767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172767).length < 2 ^ (prefixWord ++ tailWord_172767).sum := by decide
  have hdescent : baseEnd_172767 < baseStart_172767 := by decide
  rcases family_descends (prefixWord ++ tailWord_172767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172781 : List Nat := [1, 5, 1, 2, 1, 1, 1, 6, 1, 1, 3]
def baseStart_172781 : Nat := 118140960795 + 172781 * 2 ^ 59
def prefixEnd_172781 : Nat := 4983230072969 + 3 ^ 40 * 172781 * 2
def baseEnd_172781 : Nat := 88719700964593727242901

theorem tailTrace_172781 : CollatzResearch.WordTrace tailWord_172781 prefixEnd_172781 88719700964593727242901 := by
  unfold tailWord_172781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301840787051420490606197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4201227191367613660404131 6301840787051420490606197)
  ·
    refine ⟨590797573786070670994331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6301840787051420490606197 590797573786070670994331)
    ·
      refine ⟨886196360679106006491497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590797573786070670994331 886196360679106006491497)
      ·
        refine ⟨664647270509329504868623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886196360679106006491497 664647270509329504868623)
        ·
          refine ⟨996970905763994257302935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664647270509329504868623 996970905763994257302935)
          ·
            refine ⟨1495456358645991385954403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996970905763994257302935 1495456358645991385954403)
            ·
              refine ⟨2243184537968987078931605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495456358645991385954403 2243184537968987078931605)
              ·
                refine ⟨105149275217296269324919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2243184537968987078931605 105149275217296269324919)
                ·
                  refine ⟨157723912825944403987379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105149275217296269324919 157723912825944403987379)
                  ·
                    refine ⟨236585869238916605981069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 157723912825944403987379 236585869238916605981069)
                    ·
                      refine ⟨88719700964593727242901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 236585869238916605981069 88719700964593727242901)
                      ·
                        rfl

theorem cell23_172781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_172781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172781 prefixEnd_172781 := by exact prefixLift 172781
  have htrace : WordTrace (prefixWord ++ tailWord_172781) baseStart_172781 baseEnd_172781 := by
    simpa [prefixWord, tailWord_172781, baseEnd_172781] using wordTrace_append hprefix tailTrace_172781
  have hstable : (prefixWord ++ tailWord_172781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172781).length < 2 ^ (prefixWord ++ tailWord_172781).sum := by decide
  have hdescent : baseEnd_172781 < baseStart_172781 := by decide
  rcases family_descends (prefixWord ++ tailWord_172781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172788 : List Nat := [2, 6, 1, 1, 2, 1, 3, 1, 6]
def baseStart_172788 : Nat := 118140960795 + 172788 * 2 ^ 59
def prefixEnd_172788 : Nat := 4983230072969 + 3 ^ 40 * 172788 * 2
def baseEnd_172788 : Nat := 9858143925463911095041

theorem tailTrace_172788 : CollatzResearch.WordTrace tailWord_172788 prefixEnd_172788 9858143925463911095041 := by
  unfold tailWord_172788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151048049013030343055509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4201397398684040457407345 3151048049013030343055509)
  ·
    refine ⟨147705377297485797330727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3151048049013030343055509 147705377297485797330727)
    ·
      refine ⟨221558065946228695996091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 147705377297485797330727 221558065946228695996091)
      ·
        refine ⟨332337098919343043994137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221558065946228695996091 332337098919343043994137)
        ·
          refine ⟨249252824189507282995603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332337098919343043994137 249252824189507282995603)
          ·
            refine ⟨373879236284260924493405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249252824189507282995603 373879236284260924493405)
            ·
              refine ⟨140204713606597846685027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 373879236284260924493405 140204713606597846685027)
              ·
                refine ⟨210307070409896770027541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140204713606597846685027 210307070409896770027541)
                ·
                  refine ⟨9858143925463911095041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 210307070409896770027541 9858143925463911095041)
                  ·
                    rfl

theorem cell23_172788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_172788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172788 prefixEnd_172788 := by exact prefixLift 172788
  have htrace : WordTrace (prefixWord ++ tailWord_172788) baseStart_172788 baseEnd_172788 := by
    simpa [prefixWord, tailWord_172788, baseEnd_172788] using wordTrace_append hprefix tailTrace_172788
  have hstable : (prefixWord ++ tailWord_172788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172788).length < 2 ^ (prefixWord ++ tailWord_172788).sum := by decide
  have hdescent : baseEnd_172788 < baseStart_172788 := by decide
  rcases family_descends (prefixWord ++ tailWord_172788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172804 : List Nat := [2, 3, 2, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_172804 : Nat := 118140960795 + 172804 * 2 ^ 59
def prefixEnd_172804 : Nat := 4983230072969 + 3 ^ 40 * 172804 * 2
def baseEnd_172804 : Nat := 88731511019647137255295

theorem tailTrace_172804 : CollatzResearch.WordTrace tailWord_172804 prefixEnd_172804 88731511019647137255295 := by
  unfold tailWord_172804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151339832984047709346733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4201786443978730279128977 3151339832984047709346733)
  ·
    refine ⟨1181752437369017891005025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3151339832984047709346733 1181752437369017891005025)
    ·
      refine ⟨886314328026763418253769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1181752437369017891005025 886314328026763418253769)
      ·
        refine ⟨664735746020072563690327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886314328026763418253769 664735746020072563690327)
        ·
          refine ⟨997103619030108845535491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664735746020072563690327 997103619030108845535491)
          ·
            refine ⟨1495655428545163268303237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997103619030108845535491 1495655428545163268303237)
            ·
              refine ⟨280435392852218112806857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1495655428545163268303237 280435392852218112806857)
              ·
                refine ⟨210326544639163584605143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280435392852218112806857 210326544639163584605143)
                ·
                  refine ⟨315489816958745376907715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210326544639163584605143 315489816958745376907715)
                  ·
                    refine ⟨473234725438118065361573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 315489816958745376907715 473234725438118065361573)
                    ·
                      refine ⟨88731511019647137255295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 473234725438118065361573 88731511019647137255295)
                      ·
                        rfl

theorem cell23_172804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_172804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172804 prefixEnd_172804 := by exact prefixLift 172804
  have htrace : WordTrace (prefixWord ++ tailWord_172804) baseStart_172804 baseEnd_172804 := by
    simpa [prefixWord, tailWord_172804, baseEnd_172804] using wordTrace_append hprefix tailTrace_172804
  have hstable : (prefixWord ++ tailWord_172804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172804).length < 2 ^ (prefixWord ++ tailWord_172804).sum := by decide
  have hdescent : baseEnd_172804 < baseStart_172804 := by decide
  rcases family_descends (prefixWord ++ tailWord_172804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172810 : List Nat := [3, 1, 2, 2, 1, 2, 3, 9]
def baseStart_172810 : Nat := 118140960795 + 172810 * 2 ^ 59
def prefixEnd_172810 : Nat := 4983230072969 + 3 ^ 40 * 172810 * 2
def baseEnd_172810 : Nat := 3286466366799041251121

theorem tailTrace_172810 : CollatzResearch.WordTrace tailWord_172810 prefixEnd_172810 3286466366799041251121 := by
  unfold tailWord_172810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575724625986589610852971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4201932335964238962274589 1575724625986589610852971)
  ·
    refine ⟨2363586938979884416279457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575724625986589610852971 2363586938979884416279457)
    ·
      refine ⟨1772690204234913312209593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2363586938979884416279457 1772690204234913312209593)
      ·
        refine ⟨1329517653176184984157195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1772690204234913312209593 1329517653176184984157195)
        ·
          refine ⟨1994276479764277476235793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329517653176184984157195 1994276479764277476235793)
          ·
            refine ⟨1495707359823208107176845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994276479764277476235793 1495707359823208107176845)
            ·
              refine ⟨560890259933703040191317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1495707359823208107176845 560890259933703040191317)
              ·
                refine ⟨3286466366799041251121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 560890259933703040191317 3286466366799041251121)
                ·
                  rfl

theorem cell23_172810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 9].length) (baseStart_172810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172810 prefixEnd_172810 := by exact prefixLift 172810
  have htrace : WordTrace (prefixWord ++ tailWord_172810) baseStart_172810 baseEnd_172810 := by
    simpa [prefixWord, tailWord_172810, baseEnd_172810] using wordTrace_append hprefix tailTrace_172810
  have hstable : (prefixWord ++ tailWord_172810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172810).length < 2 ^ (prefixWord ++ tailWord_172810).sum := by decide
  have hdescent : baseEnd_172810 < baseStart_172810 := by decide
  rcases family_descends (prefixWord ++ tailWord_172810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172858 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3]
def baseStart_172858 : Nat := 118140960795 + 172858 * 2 ^ 59
def prefixEnd_172858 : Nat := 4983230072969 + 3 ^ 40 * 172858 * 2
def baseEnd_172858 : Nat := 88759238974989925980047

theorem tailTrace_172858 : CollatzResearch.WordTrace tailWord_172858 prefixEnd_172858 88759238974989925980047 := by
  unfold tailWord_172858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1576162301943115660289807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4203099471848308427439485 1576162301943115660289807)
  ·
    refine ⟨2364243452914673490434711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1576162301943115660289807 2364243452914673490434711)
    ·
      refine ⟨3546365179372010235652067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364243452914673490434711 3546365179372010235652067)
      ·
        refine ⟨5319547769058015353478101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546365179372010235652067 5319547769058015353478101)
        ·
          refine ⟨124676900837297234847143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5319547769058015353478101 124676900837297234847143)
          ·
            refine ⟨187015351255945852270715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124676900837297234847143 187015351255945852270715)
            ·
              refine ⟨280523026883918778406073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187015351255945852270715 280523026883918778406073)
              ·
                refine ⟨210392270162939083804555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280523026883918778406073 210392270162939083804555)
                ·
                  refine ⟨315588405244408625706833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210392270162939083804555 315588405244408625706833)
                  ·
                    refine ⟨236691303933306469280125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315588405244408625706833 236691303933306469280125)
                    ·
                      refine ⟨88759238974989925980047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 236691303933306469280125 88759238974989925980047)
                      ·
                        rfl

theorem cell23_172858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_172858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172858 prefixEnd_172858 := by exact prefixLift 172858
  have htrace : WordTrace (prefixWord ++ tailWord_172858) baseStart_172858 baseEnd_172858 := by
    simpa [prefixWord, tailWord_172858, baseEnd_172858] using wordTrace_append hprefix tailTrace_172858
  have hstable : (prefixWord ++ tailWord_172858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172858).length < 2 ^ (prefixWord ++ tailWord_172858).sum := by decide
  have hdescent : baseEnd_172858 < baseStart_172858 := by decide
  rcases family_descends (prefixWord ++ tailWord_172858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172860 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_172860 : Nat := 118140960795 + 172860 * 2 ^ 59
def prefixEnd_172860 : Nat := 4983230072969 + 3 ^ 40 * 172860 * 2
def baseEnd_172860 : Nat := 88760265936298918155037

theorem tailTrace_172860 : CollatzResearch.WordTrace tailWord_172860 prefixEnd_172860 88760265936298918155037 := by
  unfold tailWord_172860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152361076882608491366017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4203148102510144655154689 3152361076882608491366017)
  ·
    refine ⟨2364270807661956368524513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3152361076882608491366017 2364270807661956368524513)
    ·
      refine ⟨1773203105746467276393385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2364270807661956368524513 1773203105746467276393385)
      ·
        refine ⟨1329902329309850457295039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773203105746467276393385 1329902329309850457295039)
        ·
          refine ⟨1994853493964775685942559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329902329309850457295039 1994853493964775685942559)
          ·
            refine ⟨2992280240947163528913839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994853493964775685942559 2992280240947163528913839)
            ·
              refine ⟨4488420361420745293370759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992280240947163528913839 4488420361420745293370759)
              ·
                refine ⟨6732630542131117940056139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488420361420745293370759 6732630542131117940056139)
                ·
                  refine ⟨10098945813196676910084209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6732630542131117940056139 10098945813196676910084209)
                  ·
                    refine ⟨7574209359897507682563157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10098945813196676910084209 7574209359897507682563157)
                    ·
                      refine ⟨88760265936298918155037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 7574209359897507682563157 88760265936298918155037)
                      ·
                        rfl

theorem cell23_172860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_172860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172860 prefixEnd_172860 := by exact prefixLift 172860
  have htrace : WordTrace (prefixWord ++ tailWord_172860) baseStart_172860 baseEnd_172860 := by
    simpa [prefixWord, tailWord_172860, baseEnd_172860] using wordTrace_append hprefix tailTrace_172860
  have hstable : (prefixWord ++ tailWord_172860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172860).length < 2 ^ (prefixWord ++ tailWord_172860).sum := by decide
  have hdescent : baseEnd_172860 < baseStart_172860 := by decide
  rcases family_descends (prefixWord ++ tailWord_172860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172917 : List Nat := [1, 3, 4, 1, 1, 2, 1, 1, 9]
def baseStart_172917 : Nat := 118140960795 + 172917 * 2 ^ 59
def prefixEnd_172917 : Nat := 4983230072969 + 3 ^ 40 * 172917 * 2
def baseEnd_172917 : Nat := 9865503814845021682475

theorem tailTrace_172917 : CollatzResearch.WordTrace tailWord_172917 prefixEnd_172917 9865503814845021682475 := by
  unfold tailWord_172917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306801114558715717557005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4204534076372477145038003 6306801114558715717557005)
  ·
    refine ⟨2365050417959518394083877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6306801114558715717557005 2365050417959518394083877)
    ·
      refine ⟨443446953367409698890727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2365050417959518394083877 443446953367409698890727)
      ·
        refine ⟨665170430051114548336091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443446953367409698890727 665170430051114548336091)
        ·
          refine ⟨997755645076671822504137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665170430051114548336091 997755645076671822504137)
          ·
            refine ⟨748316733807503866878103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 997755645076671822504137 748316733807503866878103)
            ·
              refine ⟨1122475100711255800317155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748316733807503866878103 1122475100711255800317155)
              ·
                refine ⟨1683712651066883700475733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122475100711255800317155 1683712651066883700475733)
                ·
                  refine ⟨9865503814845021682475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1683712651066883700475733 9865503814845021682475)
                  ·
                    rfl

theorem cell23_172917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 9].length) (baseStart_172917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172917 prefixEnd_172917 := by exact prefixLift 172917
  have htrace : WordTrace (prefixWord ++ tailWord_172917) baseStart_172917 baseEnd_172917 := by
    simpa [prefixWord, tailWord_172917, baseEnd_172917] using wordTrace_append hprefix tailTrace_172917
  have hstable : (prefixWord ++ tailWord_172917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172917).length < 2 ^ (prefixWord ++ tailWord_172917).sum := by decide
  have hdescent : baseEnd_172917 < baseStart_172917 := by decide
  rcases family_descends (prefixWord ++ tailWord_172917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172957 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_172957 : Nat := 118140960795 + 172957 * 2 ^ 59
def prefixEnd_172957 : Nat := 4983230072969 + 3 ^ 40 * 172957 * 2
def baseEnd_172957 : Nat := 88810073559785038642091

theorem tailTrace_172957 : CollatzResearch.WordTrace tailWord_172957 prefixEnd_172957 88810073559785038642091 := by
  unfold tailWord_172957
  simp only [CollatzResearch.WordTrace]
  refine ⟨6308260034413802549013125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4205506689609201699342083 6308260034413802549013125)
  ·
    refine ⟨1182798756452587977939961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6308260034413802549013125 1182798756452587977939961)
    ·
      refine ⟨887099067339440983454971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182798756452587977939961 887099067339440983454971)
      ·
        refine ⟨1330648601009161475182457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887099067339440983454971 1330648601009161475182457)
        ·
          refine ⟨997986450756871106386843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330648601009161475182457 997986450756871106386843)
          ·
            refine ⟨1496979676135306659580265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997986450756871106386843 1496979676135306659580265)
            ·
              refine ⟨1122734757101479994685199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496979676135306659580265 1122734757101479994685199)
              ·
                refine ⟨1684102135652219992027799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122734757101479994685199 1684102135652219992027799)
                ·
                  refine ⟨2526153203478329988041699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684102135652219992027799 2526153203478329988041699)
                  ·
                    refine ⟨3789229805217494982062549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2526153203478329988041699 3789229805217494982062549)
                    ·
                      refine ⟨88810073559785038642091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3789229805217494982062549 88810073559785038642091)
                      ·
                        rfl

theorem cell23_172957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_172957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172957 prefixEnd_172957 := by exact prefixLift 172957
  have htrace : WordTrace (prefixWord ++ tailWord_172957) baseStart_172957 baseEnd_172957 := by
    simpa [prefixWord, tailWord_172957, baseEnd_172957] using wordTrace_append hprefix tailTrace_172957
  have hstable : (prefixWord ++ tailWord_172957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172957).length < 2 ^ (prefixWord ++ tailWord_172957).sum := by decide
  have hdescent : baseEnd_172957 < baseStart_172957 := by decide
  rcases family_descends (prefixWord ++ tailWord_172957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_172987 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3]
def baseStart_172987 : Nat := 118140960795 + 172987 * 2 ^ 59
def prefixEnd_172987 : Nat := 4983230072969 + 3 ^ 40 * 172987 * 2
def baseEnd_172987 : Nat := 88825477979419921266953

theorem tailTrace_172987 : CollatzResearch.WordTrace tailWord_172987 prefixEnd_172987 88825477979419921266953 := by
  unfold tailWord_172987
  simp only [CollatzResearch.WordTrace]
  refine ⟨6309354224305117672605215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4206236149536745115070143 6309354224305117672605215)
  ·
    refine ⟨9464031336457676508907823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6309354224305117672605215 9464031336457676508907823)
    ·
      refine ⟨14196047004686514763361735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9464031336457676508907823 14196047004686514763361735)
      ·
        refine ⟨21294070507029772145042603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14196047004686514763361735 21294070507029772145042603)
        ·
          refine ⟨31941105760544658217563905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21294070507029772145042603 31941105760544658217563905)
          ·
            refine ⟨23955829320408493663172929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31941105760544658217563905 23955829320408493663172929)
            ·
              refine ⟨17966871990306370247379697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23955829320408493663172929 17966871990306370247379697)
              ·
                refine ⟨13475153992729777685534773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17966871990306370247379697 13475153992729777685534773)
                ·
                  refine ⟨1263295686818416658018885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13475153992729777685534773 1263295686818416658018885)
                  ·
                    refine ⟨236867941278453123378541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1263295686818416658018885 236867941278453123378541)
                    ·
                      refine ⟨88825477979419921266953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 236867941278453123378541 88825477979419921266953)
                      ·
                        rfl

theorem cell23_172987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 4, 3].length) (baseStart_172987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_172987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_172987 prefixEnd_172987 := by exact prefixLift 172987
  have htrace : WordTrace (prefixWord ++ tailWord_172987) baseStart_172987 baseEnd_172987 := by
    simpa [prefixWord, tailWord_172987, baseEnd_172987] using wordTrace_append hprefix tailTrace_172987
  have hstable : (prefixWord ++ tailWord_172987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_172987).length < 2 ^ (prefixWord ++ tailWord_172987).sum := by decide
  have hdescent : baseEnd_172987 < baseStart_172987 := by decide
  rcases family_descends (prefixWord ++ tailWord_172987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173007 : List Nat := [1, 1, 2, 1, 1, 6, 2, 1, 8]
def baseStart_173007 : Nat := 118140960795 + 173007 * 2 ^ 59
def prefixEnd_173007 : Nat := 4983230072969 + 3 ^ 40 * 173007 * 2
def baseEnd_173007 : Nat := 9870638621389982557429

theorem tailTrace_173007 : CollatzResearch.WordTrace tailWord_173007 prefixEnd_173007 9870638621389982557429 := by
  unfold tailWord_173007
  simp only [CollatzResearch.WordTrace]
  refine ⟨6310083684232661088333275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4206722456155107392222183 6310083684232661088333275)
  ·
    refine ⟨9465125526348991632499913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6310083684232661088333275 9465125526348991632499913)
    ·
      refine ⟨7098844144761743724374935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9465125526348991632499913 7098844144761743724374935)
      ·
        refine ⟨10648266217142615586562403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7098844144761743724374935 10648266217142615586562403)
        ·
          refine ⟨15972399325713923379843605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10648266217142615586562403 15972399325713923379843605)
          ·
            refine ⟨748706218392840158430169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15972399325713923379843605 748706218392840158430169)
            ·
              refine ⟨561529663794630118822627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748706218392840158430169 561529663794630118822627)
              ·
                refine ⟨842294495691945178233941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561529663794630118822627 842294495691945178233941)
                ·
                  refine ⟨9870638621389982557429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 842294495691945178233941 9870638621389982557429)
                  ·
                    rfl

theorem cell23_173007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 8].length) (baseStart_173007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173007 prefixEnd_173007 := by exact prefixLift 173007
  have htrace : WordTrace (prefixWord ++ tailWord_173007) baseStart_173007 baseEnd_173007 := by
    simpa [prefixWord, tailWord_173007, baseEnd_173007] using wordTrace_append hprefix tailTrace_173007
  have hstable : (prefixWord ++ tailWord_173007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173007).length < 2 ^ (prefixWord ++ tailWord_173007).sum := by decide
  have hdescent : baseEnd_173007 < baseStart_173007 := by decide
  rcases family_descends (prefixWord ++ tailWord_173007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173038 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3]
def baseStart_173038 : Nat := 118140960795 + 173038 * 2 ^ 59
def prefixEnd_173038 : Nat := 4983230072969 + 3 ^ 40 * 173038 * 2
def baseEnd_173038 : Nat := 88851665492799221729219

theorem tailTrace_173038 : CollatzResearch.WordTrace tailWord_173038 prefixEnd_173038 88851665492799221729219 := by
  unfold tailWord_173038
  simp only [CollatzResearch.WordTrace]
  refine ⟨788901793390044172838971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4207476231413568921807845 788901793390044172838971)
  ·
    refine ⟨1183352690085066259258457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 788901793390044172838971 1183352690085066259258457)
    ·
      refine ⟨887514517563799694443843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1183352690085066259258457 887514517563799694443843)
      ·
        refine ⟨1331271776345699541665765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887514517563799694443843 1331271776345699541665765)
        ·
          refine ⟨249613458064818664062331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1331271776345699541665765 249613458064818664062331)
          ·
            refine ⟨374420187097227996093497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249613458064818664062331 374420187097227996093497)
            ·
              refine ⟨280815140322920997070123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374420187097227996093497 280815140322920997070123)
              ·
                refine ⟨421222710484381495605185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280815140322920997070123 421222710484381495605185)
                ·
                  refine ⟨315917032863286121703889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421222710484381495605185 315917032863286121703889)
                  ·
                    refine ⟨236937774647464591277917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315917032863286121703889 236937774647464591277917)
                    ·
                      refine ⟨88851665492799221729219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 236937774647464591277917 88851665492799221729219)
                      ·
                        rfl

theorem cell23_173038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_173038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173038 prefixEnd_173038 := by exact prefixLift 173038
  have htrace : WordTrace (prefixWord ++ tailWord_173038) baseStart_173038 baseEnd_173038 := by
    simpa [prefixWord, tailWord_173038, baseEnd_173038] using wordTrace_append hprefix tailTrace_173038
  have hstable : (prefixWord ++ tailWord_173038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173038).length < 2 ^ (prefixWord ++ tailWord_173038).sum := by decide
  have hdescent : baseEnd_173038 < baseStart_173038 := by decide
  rcases family_descends (prefixWord ++ tailWord_173038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173061 : List Nat := [1, 3, 1, 1, 2, 3, 1, 4, 2, 3, 2]
def baseStart_173061 : Nat := 118140960795 + 173061 * 2 ^ 59
def prefixEnd_173061 : Nat := 4983230072969 + 3 ^ 40 * 173061 * 2
def baseEnd_173061 : Nat := 88863475547852631741613

theorem tailTrace_173061 : CollatzResearch.WordTrace tailWord_173061 prefixEnd_173061 88863475547852631741613 := by
  unfold tailWord_173061
  simp only [CollatzResearch.WordTrace]
  refine ⟨6312053226037028310799037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4208035484024685540532691 6312053226037028310799037)
  ·
    refine ⟨2367019959763885616549639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6312053226037028310799037 2367019959763885616549639)
    ·
      refine ⟨3550529939645828424824459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367019959763885616549639 3550529939645828424824459)
      ·
        refine ⟨5325794909468742637236689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550529939645828424824459 5325794909468742637236689)
        ·
          refine ⟨3994346182101556977927517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325794909468742637236689 3994346182101556977927517)
          ·
            refine ⟨1497879818288083866722819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3994346182101556977927517 1497879818288083866722819)
            ·
              refine ⟨2246819727432125800084229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497879818288083866722819 2246819727432125800084229)
              ·
                refine ⟨421278698893523587515793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2246819727432125800084229 421278698893523587515793)
                ·
                  refine ⟨315959024170142690636845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421278698893523587515793 315959024170142690636845)
                  ·
                    refine ⟨118484634063803508988817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 315959024170142690636845 118484634063803508988817)
                    ·
                      refine ⟨88863475547852631741613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118484634063803508988817 88863475547852631741613)
                      ·
                        rfl

theorem cell23_173061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 3, 2].length) (baseStart_173061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173061 prefixEnd_173061 := by exact prefixLift 173061
  have htrace : WordTrace (prefixWord ++ tailWord_173061) baseStart_173061 baseEnd_173061 := by
    simpa [prefixWord, tailWord_173061, baseEnd_173061] using wordTrace_append hprefix tailTrace_173061
  have hstable : (prefixWord ++ tailWord_173061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173061).length < 2 ^ (prefixWord ++ tailWord_173061).sum := by decide
  have hdescent : baseEnd_173061 < baseStart_173061 := by decide
  rcases family_descends (prefixWord ++ tailWord_173061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173095 : List Nat := [1, 1, 7, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_173095 : Nat := 118140960795 + 173095 * 2 ^ 59
def prefixEnd_173095 : Nat := 4983230072969 + 3 ^ 40 * 173095 * 2
def baseEnd_173095 : Nat := 88880933890105498716457

theorem tailTrace_173095 : CollatzResearch.WordTrace tailWord_173095 prefixEnd_173095 88880933890105498716457 := by
  unfold tailWord_173095
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313293307913852117536739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4208862205275901411691159 6313293307913852117536739)
  ·
    refine ⟨9469939961870778176305109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6313293307913852117536739 9469939961870778176305109)
    ·
      refine ⟨221951717856346363507151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 9469939961870778176305109 221951717856346363507151)
      ·
        refine ⟨332927576784519545260727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221951717856346363507151 332927576784519545260727)
        ·
          refine ⟨499391365176779317891091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332927576784519545260727 499391365176779317891091)
          ·
            refine ⟨749087047765168976836637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499391365176779317891091 749087047765168976836637)
            ·
              refine ⟨280907642911938366313739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749087047765168976836637 280907642911938366313739)
              ·
                refine ⟨421361464367907549470609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280907642911938366313739 421361464367907549470609)
                ·
                  refine ⟨316021098275930662102957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421361464367907549470609 316021098275930662102957)
                  ·
                    refine ⟨118507911853473998288609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316021098275930662102957 118507911853473998288609)
                    ·
                      refine ⟨88880933890105498716457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118507911853473998288609 88880933890105498716457)
                      ·
                        rfl

theorem cell23_173095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_173095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173095 prefixEnd_173095 := by exact prefixLift 173095
  have htrace : WordTrace (prefixWord ++ tailWord_173095) baseStart_173095 baseEnd_173095 := by
    simpa [prefixWord, tailWord_173095, baseEnd_173095] using wordTrace_append hprefix tailTrace_173095
  have hstable : (prefixWord ++ tailWord_173095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173095).length < 2 ^ (prefixWord ++ tailWord_173095).sum := by decide
  have hdescent : baseEnd_173095 < baseStart_173095 := by decide
  rcases family_descends (prefixWord ++ tailWord_173095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173104 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_173104 : Nat := 118140960795 + 173104 * 2 ^ 59
def prefixEnd_173104 : Nat := 4983230072969 + 3 ^ 40 * 173104 * 2
def baseEnd_173104 : Nat := 88885555215995963503915

theorem tailTrace_173104 : CollatzResearch.WordTrace tailWord_173104 prefixEnd_173104 88885555215995963503915 := by
  unfold tailWord_173104
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156810782440623327307183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4209081043254164436409577 3156810782440623327307183)
  ·
    refine ⟨4735216173660934990960775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3156810782440623327307183 4735216173660934990960775)
    ·
      refine ⟨7102824260491402486441163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4735216173660934990960775 7102824260491402486441163)
      ·
        refine ⟨10654236390737103729661745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7102824260491402486441163 10654236390737103729661745)
        ·
          refine ⟨7990677293052827797246309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10654236390737103729661745 7990677293052827797246309)
          ·
            refine ⟨1498251992447405211983683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7990677293052827797246309 1498251992447405211983683)
            ·
              refine ⟨2247377988671107817975525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498251992447405211983683 2247377988671107817975525)
              ·
                refine ⟨421383372875832715870411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2247377988671107817975525 421383372875832715870411)
                ·
                  refine ⟨632075059313749073805617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421383372875832715870411 632075059313749073805617)
                  ·
                    refine ⟨474056294485311805354213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632075059313749073805617 474056294485311805354213)
                    ·
                      refine ⟨88885555215995963503915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 474056294485311805354213 88885555215995963503915)
                      ·
                        rfl

theorem cell23_173104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_173104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173104 prefixEnd_173104 := by exact prefixLift 173104
  have htrace : WordTrace (prefixWord ++ tailWord_173104) baseStart_173104 baseEnd_173104 := by
    simpa [prefixWord, tailWord_173104, baseEnd_173104] using wordTrace_append hprefix tailTrace_173104
  have hstable : (prefixWord ++ tailWord_173104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173104).length < 2 ^ (prefixWord ++ tailWord_173104).sum := by decide
  have hdescent : baseEnd_173104 < baseStart_173104 := by decide
  rcases family_descends (prefixWord ++ tailWord_173104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173118 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 4, 4]
def baseStart_173118 : Nat := 118140960795 + 173118 * 2 ^ 59
def prefixEnd_173118 : Nat := 4983230072969 + 3 ^ 40 * 173118 * 2
def baseEnd_173118 : Nat := 29630914648386302909617

theorem tailTrace_173118 : CollatzResearch.WordTrace tailWord_173118 prefixEnd_173118 29630914648386302909617 := by
  unfold tailWord_173118
  simp only [CollatzResearch.WordTrace]
  refine ⟨789266523353815880703001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4209421457887018030416005 789266523353815880703001)
  ·
    refine ⟨591949892515361910527251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 789266523353815880703001 591949892515361910527251)
    ·
      refine ⟨887924838773042865790877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 591949892515361910527251 887924838773042865790877)
      ·
        refine ⟨332971814539891074671579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 887924838773042865790877 332971814539891074671579)
        ·
          refine ⟨499457721809836612007369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332971814539891074671579 499457721809836612007369)
          ·
            refine ⟨374593291357377459005527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499457721809836612007369 374593291357377459005527)
            ·
              refine ⟨561889937036066188508291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374593291357377459005527 561889937036066188508291)
              ·
                refine ⟨842834905554099282762437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561889937036066188508291 842834905554099282762437)
                ·
                  refine ⟨158031544791393615517957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842834905554099282762437 158031544791393615517957)
                  ·
                    refine ⟨29630914648386302909617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158031544791393615517957 29630914648386302909617)
                    ·
                      rfl

theorem cell23_173118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_173118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173118 prefixEnd_173118 := by exact prefixLift 173118
  have htrace : WordTrace (prefixWord ++ tailWord_173118) baseStart_173118 baseEnd_173118 := by
    simpa [prefixWord, tailWord_173118, baseEnd_173118] using wordTrace_append hprefix tailTrace_173118
  have hstable : (prefixWord ++ tailWord_173118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173118).length < 2 ^ (prefixWord ++ tailWord_173118).sum := by decide
  have hdescent : baseEnd_173118 < baseStart_173118 := by decide
  rcases family_descends (prefixWord ++ tailWord_173118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173125 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 1, 2, 2]
def baseStart_173125 : Nat := 118140960795 + 173125 * 2 ^ 59
def prefixEnd_173125 : Nat := 4983230072969 + 3 ^ 40 * 173125 * 2
def baseEnd_173125 : Nat := 88896338309740381341319

theorem tailTrace_173125 : CollatzResearch.WordTrace tailWord_173125 prefixEnd_173125 88896338309740381341319 := by
  unfold tailWord_173125
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314387497805167241128829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4209591665203444827419219 6314387497805167241128829)
  ·
    refine ⟨2367895311676937715423311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6314387497805167241128829 2367895311676937715423311)
    ·
      refine ⟨3551842967515406573134967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367895311676937715423311 3551842967515406573134967)
      ·
        refine ⟨5327764451273109859702451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551842967515406573134967 5327764451273109859702451)
        ·
          refine ⟨7991646676909664789553677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327764451273109859702451 7991646676909664789553677)
          ·
            refine ⟨2996867503841124296082629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7991646676909664789553677 2996867503841124296082629)
            ·
              refine ⟨561912656970210805515493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2996867503841124296082629 561912656970210805515493)
              ·
                refine ⟨105358623181914526034155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 561912656970210805515493 105358623181914526034155)
                ·
                  refine ⟨158037934772871789051233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105358623181914526034155 158037934772871789051233)
                  ·
                    refine ⟨118528451079653841788425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158037934772871789051233 118528451079653841788425)
                    ·
                      refine ⟨88896338309740381341319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118528451079653841788425 88896338309740381341319)
                      ·
                        rfl

theorem cell23_173125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 2, 2].length) (baseStart_173125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173125 prefixEnd_173125 := by exact prefixLift 173125
  have htrace : WordTrace (prefixWord ++ tailWord_173125) baseStart_173125 baseEnd_173125 := by
    simpa [prefixWord, tailWord_173125, baseEnd_173125] using wordTrace_append hprefix tailTrace_173125
  have hstable : (prefixWord ++ tailWord_173125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173125).length < 2 ^ (prefixWord ++ tailWord_173125).sum := by decide
  have hdescent : baseEnd_173125 < baseStart_173125 := by decide
  rcases family_descends (prefixWord ++ tailWord_173125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173138 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 1, 2, 4]
def baseStart_173138 : Nat := 118140960795 + 173138 * 2 ^ 59
def prefixEnd_173138 : Nat := 4983230072969 + 3 ^ 40 * 173138 * 2
def baseEnd_173138 : Nat := 88903013558248830478759

theorem tailTrace_173138 : CollatzResearch.WordTrace tailWord_173138 prefixEnd_173138 88903013558248830478759 := by
  unfold tailWord_173138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578715411689517615338017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4209907764505380307568045 1578715411689517615338017)
  ·
    refine ⟨1184036558767138211503513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1578715411689517615338017 1184036558767138211503513)
    ·
      refine ⟨888027419075353658627635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1184036558767138211503513 888027419075353658627635)
      ·
        refine ⟨1332041128613030487941453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888027419075353658627635 1332041128613030487941453)
        ·
          refine ⟨499515423229886432978045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1332041128613030487941453 499515423229886432978045)
          ·
            refine ⟨187318283711207412366767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 499515423229886432978045 187318283711207412366767)
            ·
              refine ⟨280977425566811118550151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187318283711207412366767 280977425566811118550151)
              ·
                refine ⟨421466138350216677825227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280977425566811118550151 421466138350216677825227)
                ·
                  refine ⟨632199207525325016737841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421466138350216677825227 632199207525325016737841)
                  ·
                    refine ⟨474149405643993762553381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632199207525325016737841 474149405643993762553381)
                    ·
                      refine ⟨88903013558248830478759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 474149405643993762553381 88903013558248830478759)
                      ·
                        rfl

theorem cell23_173138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 1, 2, 4].length) (baseStart_173138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173138 prefixEnd_173138 := by exact prefixLift 173138
  have htrace : WordTrace (prefixWord ++ tailWord_173138) baseStart_173138 baseEnd_173138 := by
    simpa [prefixWord, tailWord_173138, baseEnd_173138] using wordTrace_append hprefix tailTrace_173138
  have hstable : (prefixWord ++ tailWord_173138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173138).length < 2 ^ (prefixWord ++ tailWord_173138).sum := by decide
  have hdescent : baseEnd_173138 < baseStart_173138 := by decide
  rcases family_descends (prefixWord ++ tailWord_173138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173142 : List Nat := [5, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_173142 : Nat := 118140960795 + 173142 * 2 ^ 59
def prefixEnd_173142 : Nat := 4983230072969 + 3 ^ 40 * 173142 * 2
def baseEnd_173142 : Nat := 88905067480866814828741

theorem tailTrace_173142 : CollatzResearch.WordTrace tailWord_173142 prefixEnd_173142 88905067480866814828741 := by
  unfold tailWord_173142
  simp only [CollatzResearch.WordTrace]
  refine ⟨394687971171473696531105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4210005025829052762998453 394687971171473696531105)
  ·
    refine ⟨296015978378605272398329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 394687971171473696531105 296015978378605272398329)
    ·
      refine ⟨222011983783953954298747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296015978378605272398329 222011983783953954298747)
      ·
        refine ⟨333017975675930931448121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222011983783953954298747 333017975675930931448121)
        ·
          refine ⟨249763481756948198586091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333017975675930931448121 249763481756948198586091)
          ·
            refine ⟨374645222635422297879137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249763481756948198586091 374645222635422297879137)
            ·
              refine ⟨280983916976566723409353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374645222635422297879137 280983916976566723409353)
              ·
                refine ⟨210737937732425042557015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280983916976566723409353 210737937732425042557015)
                ·
                  refine ⟨316106906598637563835523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210737937732425042557015 316106906598637563835523)
                  ·
                    refine ⟨474160359897956345753285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 316106906598637563835523 474160359897956345753285)
                    ·
                      refine ⟨88905067480866814828741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 474160359897956345753285 88905067480866814828741)
                      ·
                        rfl

theorem cell23_173142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_173142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173142 prefixEnd_173142 := by exact prefixLift 173142
  have htrace : WordTrace (prefixWord ++ tailWord_173142) baseStart_173142 baseEnd_173142 := by
    simpa [prefixWord, tailWord_173142, baseEnd_173142] using wordTrace_append hprefix tailTrace_173142
  have hstable : (prefixWord ++ tailWord_173142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173142).length < 2 ^ (prefixWord ++ tailWord_173142).sum := by decide
  have hdescent : baseEnd_173142 < baseStart_173142 := by decide
  rcases family_descends (prefixWord ++ tailWord_173142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173168 : List Nat := [2, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2]
def baseStart_173168 : Nat := 118140960795 + 173168 * 2 ^ 59
def prefixEnd_173168 : Nat := 4983230072969 + 3 ^ 40 * 173168 * 2
def baseEnd_173168 : Nat := 88918417977883713103621

theorem tailTrace_173168 : CollatzResearch.WordTrace tailWord_173168 prefixEnd_173168 88918417977883713103621 := by
  unfold tailWord_173168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157977918324692792472079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4210637224432923723296105 3157977918324692792472079)
  ·
    refine ⟨4736966877487039188708119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3157977918324692792472079 4736966877487039188708119)
    ·
      refine ⟨7105450316230558783062179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736966877487039188708119 7105450316230558783062179)
      ·
        refine ⟨10658175474345838174593269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7105450316230558783062179 10658175474345838174593269)
        ·
          refine ⟨999203950719922328868119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10658175474345838174593269 999203950719922328868119)
          ·
            refine ⟨1498805926079883493302179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999203950719922328868119 1498805926079883493302179)
            ·
              refine ⟨2248208889119825239953269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1498805926079883493302179 2248208889119825239953269)
              ·
                refine ⟨210769583354983616245619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2248208889119825239953269 210769583354983616245619)
                ·
                  refine ⟨316154375032475424368429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210769583354983616245619 316154375032475424368429)
                  ·
                    refine ⟨118557890637178284138161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316154375032475424368429 118557890637178284138161)
                    ·
                      refine ⟨88918417977883713103621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118557890637178284138161 88918417977883713103621)
                      ·
                        rfl

theorem cell23_173168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 5, 1, 3, 2].length) (baseStart_173168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173168 prefixEnd_173168 := by exact prefixLift 173168
  have htrace : WordTrace (prefixWord ++ tailWord_173168) baseStart_173168 baseEnd_173168 := by
    simpa [prefixWord, tailWord_173168, baseEnd_173168] using wordTrace_append hprefix tailTrace_173168
  have hstable : (prefixWord ++ tailWord_173168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173168).length < 2 ^ (prefixWord ++ tailWord_173168).sum := by decide
  have hdescent : baseEnd_173168 < baseStart_173168 := by decide
  rcases family_descends (prefixWord ++ tailWord_173168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173202 : List Nat := [3, 2, 3, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_173202 : Nat := 118140960795 + 173202 * 2 ^ 59
def prefixEnd_173202 : Nat := 4983230072969 + 3 ^ 40 * 173202 * 2
def baseEnd_173202 : Nat := 88935876320136580078465

theorem tailTrace_173202 : CollatzResearch.WordTrace tailWord_173202 prefixEnd_173202 88935876320136580078465 := by
  unfold tailWord_173202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579298979631552347920465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4211463945684139594454573 1579298979631552347920465)
  ·
    refine ⟨1184474234723664260940349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1579298979631552347920465 1184474234723664260940349)
    ·
      refine ⟨444177838021374097852631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1184474234723664260940349 444177838021374097852631)
      ·
        refine ⟨666266757032061146778947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444177838021374097852631 666266757032061146778947)
        ·
          refine ⟨999400135548091720168421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666266757032061146778947 999400135548091720168421)
          ·
            refine ⟨187387525415267197531579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 999400135548091720168421 187387525415267197531579)
            ·
              refine ⟨281081288122900796297369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187387525415267197531579 281081288122900796297369)
              ·
                refine ⟨210810966092175597223027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281081288122900796297369 210810966092175597223027)
                ·
                  refine ⟨316216449138263395834541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210810966092175597223027 316216449138263395834541)
                  ·
                    refine ⟨118581168426848773437953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 316216449138263395834541 118581168426848773437953)
                    ·
                      refine ⟨88935876320136580078465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118581168426848773437953 88935876320136580078465)
                      ·
                        rfl

theorem cell23_173202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_173202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173202 prefixEnd_173202 := by exact prefixLift 173202
  have htrace : WordTrace (prefixWord ++ tailWord_173202) baseStart_173202 baseEnd_173202 := by
    simpa [prefixWord, tailWord_173202, baseEnd_173202] using wordTrace_append hprefix tailTrace_173202
  have hstable : (prefixWord ++ tailWord_173202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173202).length < 2 ^ (prefixWord ++ tailWord_173202).sum := by decide
  have hdescent : baseEnd_173202 < baseStart_173202 := by decide
  rcases family_descends (prefixWord ++ tailWord_173202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173215 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 1, 4, 2]
def baseStart_173215 : Nat := 118140960795 + 173215 * 2 ^ 59
def prefixEnd_173215 : Nat := 4983230072969 + 3 ^ 40 * 173215 * 2
def baseEnd_173215 : Nat := 88942551568645029215905

theorem tailTrace_173215 : CollatzResearch.WordTrace tailWord_173215 prefixEnd_173215 88942551568645029215905 := by
  unfold tailWord_173215
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317670067479112611905099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4211780044986075074603399 6317670067479112611905099)
  ·
    refine ⟨9476505101218668917857649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317670067479112611905099 9476505101218668917857649)
    ·
      refine ⟨7107378825914001688393237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9476505101218668917857649 7107378825914001688393237)
      ·
        refine ⟨333158382464718829143433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7107378825914001688393237 333158382464718829143433)
        ·
          refine ⟨249868786848539121857575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333158382464718829143433 249868786848539121857575)
          ·
            refine ⟨374803180272808682786363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249868786848539121857575 374803180272808682786363)
            ·
              refine ⟨562204770409213024179545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374803180272808682786363 562204770409213024179545)
              ·
                refine ⟨421653577806909768134659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562204770409213024179545 421653577806909768134659)
                ·
                  refine ⟨632480366710364652201989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421653577806909768134659 632480366710364652201989)
                  ·
                    refine ⟨118590068758193372287873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632480366710364652201989 118590068758193372287873)
                    ·
                      refine ⟨88942551568645029215905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118590068758193372287873 88942551568645029215905)
                      ·
                        rfl

theorem cell23_173215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_173215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173215 prefixEnd_173215 := by exact prefixLift 173215
  have htrace : WordTrace (prefixWord ++ tailWord_173215) baseStart_173215 baseEnd_173215 := by
    simpa [prefixWord, tailWord_173215, baseEnd_173215] using wordTrace_append hprefix tailTrace_173215
  have hstable : (prefixWord ++ tailWord_173215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173215).length < 2 ^ (prefixWord ++ tailWord_173215).sum := by decide
  have hdescent : baseEnd_173215 < baseStart_173215 := by decide
  rcases family_descends (prefixWord ++ tailWord_173215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173248 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_173248 : Nat := 118140960795 + 173248 * 2 ^ 59
def prefixEnd_173248 : Nat := 4983230072969 + 3 ^ 40 * 173248 * 2
def baseEnd_173248 : Nat := 88959496430243400103253

theorem tailTrace_173248 : CollatzResearch.WordTrace tailWord_173248 prefixEnd_173248 88959496430243400103253 := by
  unfold tailWord_173248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159436838179779623928199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4212582450906372831904265 3159436838179779623928199)
  ·
    refine ⟨4739155257269669435892299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159436838179779623928199 4739155257269669435892299)
    ·
      refine ⟨7108732885904504153838449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4739155257269669435892299 7108732885904504153838449)
      ·
        refine ⟨5331549664428378115378837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7108732885904504153838449 5331549664428378115378837)
        ·
          refine ⟨249916390520080224158383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5331549664428378115378837 249916390520080224158383)
          ·
            refine ⟨374874585780120336237575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249916390520080224158383 374874585780120336237575)
            ·
              refine ⟨562311878670180504356363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374874585780120336237575 562311878670180504356363)
              ·
                refine ⟨843467818005270756534545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562311878670180504356363 843467818005270756534545)
                ·
                  refine ⟨632600863503953067400909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843467818005270756534545 632600863503953067400909)
                  ·
                    refine ⟨237225323813982400275341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632600863503953067400909 237225323813982400275341)
                    ·
                      refine ⟨88959496430243400103253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237225323813982400275341 88959496430243400103253)
                      ·
                        rfl

theorem cell23_173248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_173248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173248 prefixEnd_173248 := by exact prefixLift 173248
  have htrace : WordTrace (prefixWord ++ tailWord_173248) baseStart_173248 baseEnd_173248 := by
    simpa [prefixWord, tailWord_173248, baseEnd_173248] using wordTrace_append hprefix tailTrace_173248
  have hstable : (prefixWord ++ tailWord_173248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173248).length < 2 ^ (prefixWord ++ tailWord_173248).sum := by decide
  have hdescent : baseEnd_173248 < baseStart_173248 := by decide
  rcases family_descends (prefixWord ++ tailWord_173248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173288 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_173288 : Nat := 118140960795 + 173288 * 2 ^ 59
def prefixEnd_173288 : Nat := 4983230072969 + 3 ^ 40 * 173288 * 2
def baseEnd_173288 : Nat := 88980035656423243603069

theorem tailTrace_173288 : CollatzResearch.WordTrace tailWord_173288 prefixEnd_173288 88980035656423243603069 := by
  unfold tailWord_173288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160166298107323039656259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4213555064143097386208345 3160166298107323039656259)
  ·
    refine ⟨4740249447160984559484389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3160166298107323039656259 4740249447160984559484389)
    ·
      refine ⟨888796771342684604903323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4740249447160984559484389 888796771342684604903323)
      ·
        refine ⟨1333195157014026907354985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888796771342684604903323 1333195157014026907354985)
        ·
          refine ⟨999896367760520180516239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333195157014026907354985 999896367760520180516239)
          ·
            refine ⟨1499844551640780270774359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999896367760520180516239 1499844551640780270774359)
            ·
              refine ⟨2249766827461170406161539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499844551640780270774359 2249766827461170406161539)
              ·
                refine ⟨3374650241191755609242309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2249766827461170406161539 3374650241191755609242309)
                ·
                  refine ⟨632746920223454176732933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3374650241191755609242309 632746920223454176732933)
                  ·
                    refine ⟨118640047541897658137425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 632746920223454176732933 118640047541897658137425)
                    ·
                      refine ⟨88980035656423243603069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118640047541897658137425 88980035656423243603069)
                      ·
                        rfl

theorem cell23_173288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_173288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173288 prefixEnd_173288 := by exact prefixLift 173288
  have htrace : WordTrace (prefixWord ++ tailWord_173288) baseStart_173288 baseEnd_173288 := by
    simpa [prefixWord, tailWord_173288, baseEnd_173288] using wordTrace_append hprefix tailTrace_173288
  have hstable : (prefixWord ++ tailWord_173288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173288).length < 2 ^ (prefixWord ++ tailWord_173288).sum := by decide
  have hdescent : baseEnd_173288 < baseStart_173288 := by decide
  rcases family_descends (prefixWord ++ tailWord_173288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173321 : List Nat := [1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 3]
def baseStart_173321 : Nat := 118140960795 + 173321 * 2 ^ 59
def prefixEnd_173321 : Nat := 4983230072969 + 3 ^ 40 * 173321 * 2
def baseEnd_173321 : Nat := 88996980518021614490417

theorem tailTrace_173321 : CollatzResearch.WordTrace tailWord_173321 prefixEnd_173321 88996980518021614490417 := by
  unfold tailWord_173321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321536205095092715263817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4214357470063395143509211 6321536205095092715263817)
  ·
    refine ⟨4741152153821319536447863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6321536205095092715263817 4741152153821319536447863)
    ·
      refine ⟨7111728230731979304671795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741152153821319536447863 7111728230731979304671795)
      ·
        refine ⟨10667592346097968957007693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7111728230731979304671795 10667592346097968957007693)
        ·
          refine ⟨4000347129786738358877885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10667592346097968957007693 4000347129786738358877885)
          ·
            refine ⟨1500130173670026884579207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4000347129786738358877885 1500130173670026884579207)
            ·
              refine ⟨2250195260505040326868811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500130173670026884579207 2250195260505040326868811)
              ·
                refine ⟨3375292890757560490303217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250195260505040326868811 3375292890757560490303217)
                ·
                  refine ⟨2531469668068170367727413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3375292890757560490303217 2531469668068170367727413)
                  ·
                    refine ⟨237325281381390971974445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2531469668068170367727413 237325281381390971974445)
                    ·
                      refine ⟨88996980518021614490417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237325281381390971974445 88996980518021614490417)
                      ·
                        rfl

theorem cell23_173321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 5, 3].length) (baseStart_173321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173321 prefixEnd_173321 := by exact prefixLift 173321
  have htrace : WordTrace (prefixWord ++ tailWord_173321) baseStart_173321 baseEnd_173321 := by
    simpa [prefixWord, tailWord_173321, baseEnd_173321] using wordTrace_append hprefix tailTrace_173321
  have hstable : (prefixWord ++ tailWord_173321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173321).length < 2 ^ (prefixWord ++ tailWord_173321).sum := by decide
  have hdescent : baseEnd_173321 < baseStart_173321 := by decide
  rcases family_descends (prefixWord ++ tailWord_173321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173375 : List Nat := [1, 1, 2, 2, 4, 4, 1, 2, 1, 5]
def baseStart_173375 : Nat := 118140960795 + 173375 * 2 ^ 59
def prefixEnd_173375 : Nat := 4983230072969 + 3 ^ 40 * 173375 * 2
def baseEnd_173375 : Nat := 29674902824454801071723

theorem tailTrace_173375 : CollatzResearch.WordTrace tailWord_173375 prefixEnd_173375 29674902824454801071723 := by
  unfold tailWord_173375
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323505746899459937729579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4215670497932973291819719 6323505746899459937729579)
  ·
    refine ⟨9485258620349189906594369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323505746899459937729579 9485258620349189906594369)
    ·
      refine ⟨7113943965261892429945777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9485258620349189906594369 7113943965261892429945777)
      ·
        refine ⟨5335457973946419322459333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7113943965261892429945777 5335457973946419322459333)
        ·
          refine ⟨1000398370114953622961125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5335457973946419322459333 1000398370114953622961125)
          ·
            refine ⟨187574694396553804305211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1000398370114953622961125 187574694396553804305211)
            ·
              refine ⟨281362041594830706457817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187574694396553804305211 281362041594830706457817)
              ·
                refine ⟨211021531196123029843363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281362041594830706457817 211021531196123029843363)
                ·
                  refine ⟨316532296794184544765045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211021531196123029843363 316532296794184544765045)
                  ·
                    refine ⟨29674902824454801071723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 316532296794184544765045 29674902824454801071723)
                    ·
                      rfl

theorem cell23_173375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 5].length) (baseStart_173375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173375 prefixEnd_173375 := by exact prefixLift 173375
  have htrace : WordTrace (prefixWord ++ tailWord_173375) baseStart_173375 baseEnd_173375 := by
    simpa [prefixWord, tailWord_173375, baseEnd_173375] using wordTrace_append hprefix tailTrace_173375
  have hstable : (prefixWord ++ tailWord_173375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173375).length < 2 ^ (prefixWord ++ tailWord_173375).sum := by decide
  have hdescent : baseEnd_173375 < baseStart_173375 := by decide
  rcases family_descends (prefixWord ++ tailWord_173375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173381 : List Nat := [1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_173381 : Nat := 118140960795 + 173381 * 2 ^ 59
def prefixEnd_173381 : Nat := 4983230072969 + 3 ^ 40 * 173381 * 2
def baseEnd_173381 : Nat := 89027789357291379740141

theorem tailTrace_173381 : CollatzResearch.WordTrace tailWord_173381 prefixEnd_173381 89027789357291379740141 := by
  unfold tailWord_173381
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323724584877722962447997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4215816389918481974965331 6323724584877722962447997)
  ·
    refine ⟨2371396719329146110917999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6323724584877722962447997 2371396719329146110917999)
    ·
      refine ⟨3557095078993719166376999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371396719329146110917999 3557095078993719166376999)
      ·
        refine ⟨5335642618490578749565499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3557095078993719166376999 5335642618490578749565499)
        ·
          refine ⟨8003463927735868124348249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5335642618490578749565499 8003463927735868124348249)
          ·
            refine ⟨6002597945801901093261187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8003463927735868124348249 6002597945801901093261187)
            ·
              refine ⟨9003896918702851639891781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6002597945801901093261187 9003896918702851639891781)
              ·
                refine ⟨1688230672256784682479709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9003896918702851639891781 1688230672256784682479709)
                ·
                  refine ⟨633086502096294255929891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1688230672256784682479709 633086502096294255929891)
                  ·
                    refine ⟨949629753144441383894837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 633086502096294255929891 949629753144441383894837)
                    ·
                      refine ⟨89027789357291379740141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 949629753144441383894837 89027789357291379740141)
                      ·
                        rfl

theorem cell23_173381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_173381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173381 prefixEnd_173381 := by exact prefixLift 173381
  have htrace : WordTrace (prefixWord ++ tailWord_173381) baseStart_173381 baseEnd_173381 := by
    simpa [prefixWord, tailWord_173381, baseEnd_173381] using wordTrace_append hprefix tailTrace_173381
  have hstable : (prefixWord ++ tailWord_173381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173381).length < 2 ^ (prefixWord ++ tailWord_173381).sum := by decide
  have hdescent : baseEnd_173381 < baseStart_173381 := by decide
  rcases family_descends (prefixWord ++ tailWord_173381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173388 : List Nat := [2, 2, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_173388 : Nat := 118140960795 + 173388 * 2 ^ 59
def prefixEnd_173388 : Nat := 4983230072969 + 3 ^ 40 * 173388 * 2
def baseEnd_173388 : Nat := 29677127907290950784203

theorem tailTrace_173388 : CollatzResearch.WordTrace tailWord_173388 prefixEnd_173388 29677127907290950784203 := by
  unfold tailWord_173388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161989947926181578976409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4215986597234908771968545 3161989947926181578976409)
  ·
    refine ⟨2371492460944636184232307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3161989947926181578976409 2371492460944636184232307)
    ·
      refine ⟨3557238691416954276348461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371492460944636184232307 3557238691416954276348461)
      ·
        refine ⟨1333964509281357853630673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3557238691416954276348461 1333964509281357853630673)
        ·
          refine ⟨1000473381961018390223005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333964509281357853630673 1000473381961018390223005)
          ·
            refine ⟨375177518235381896333627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1000473381961018390223005 375177518235381896333627)
            ·
              refine ⟨562766277353072844500441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375177518235381896333627 562766277353072844500441)
              ·
                refine ⟨422074708014804633375331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562766277353072844500441 422074708014804633375331)
                ·
                  refine ⟨633112062022206950062997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422074708014804633375331 633112062022206950062997)
                  ·
                    refine ⟨29677127907290950784203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 633112062022206950062997 29677127907290950784203)
                    ·
                      rfl

theorem cell23_173388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_173388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173388 prefixEnd_173388 := by exact prefixLift 173388
  have htrace : WordTrace (prefixWord ++ tailWord_173388) baseStart_173388 baseEnd_173388 := by
    simpa [prefixWord, tailWord_173388, baseEnd_173388] using wordTrace_append hprefix tailTrace_173388
  have hstable : (prefixWord ++ tailWord_173388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173388).length < 2 ^ (prefixWord ++ tailWord_173388).sum := by decide
  have hdescent : baseEnd_173388 < baseStart_173388 := by decide
  rcases family_descends (prefixWord ++ tailWord_173388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173395 : List Nat := [1, 1, 1, 2, 1, 1, 9, 1, 1, 1, 4]
def baseStart_173395 : Nat := 118140960795 + 173395 * 2 ^ 59
def prefixEnd_173395 : Nat := 4983230072969 + 3 ^ 40 * 173395 * 2
def baseEnd_173395 : Nat := 89034978086454324965077

theorem tailTrace_173395 : CollatzResearch.WordTrace tailWord_173395 prefixEnd_173395 89034978086454324965077 := by
  unfold tailWord_173395
  simp only [CollatzResearch.WordTrace]
  refine ⟨6324235206827003353457639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4216156804551335568971759 6324235206827003353457639)
  ·
    refine ⟨9486352810240505030186459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6324235206827003353457639 9486352810240505030186459)
    ·
      refine ⟨14229529215360757545279689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9486352810240505030186459 14229529215360757545279689)
      ·
        refine ⟨10672146911520568158959767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14229529215360757545279689 10672146911520568158959767)
        ·
          refine ⟨16008220367280852238439651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10672146911520568158959767 16008220367280852238439651)
          ·
            refine ⟨24012330550921278357659477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16008220367280852238439651 24012330550921278357659477)
            ·
              refine ⟨140697249321804365376911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 24012330550921278357659477 140697249321804365376911)
              ·
                refine ⟨211045873982706548065367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140697249321804365376911 211045873982706548065367)
                ·
                  refine ⟨316568810974059822098051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211045873982706548065367 316568810974059822098051)
                  ·
                    refine ⟨474853216461089733147077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 316568810974059822098051 474853216461089733147077)
                    ·
                      refine ⟨89034978086454324965077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 474853216461089733147077 89034978086454324965077)
                      ·
                        rfl

theorem cell23_173395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 1, 1, 4].length) (baseStart_173395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173395 prefixEnd_173395 := by exact prefixLift 173395
  have htrace : WordTrace (prefixWord ++ tailWord_173395) baseStart_173395 baseEnd_173395 := by
    simpa [prefixWord, tailWord_173395, baseEnd_173395] using wordTrace_append hprefix tailTrace_173395
  have hstable : (prefixWord ++ tailWord_173395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173395).length < 2 ^ (prefixWord ++ tailWord_173395).sum := by decide
  have hdescent : baseEnd_173395 < baseStart_173395 := by decide
  rcases family_descends (prefixWord ++ tailWord_173395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173422 : List Nat := [4, 1, 2, 4, 1, 1, 2, 1, 1, 6]
def baseStart_173422 : Nat := 118140960795 + 173422 * 2 ^ 59
def prefixEnd_173422 : Nat := 4983230072969 + 3 ^ 40 * 173422 * 2
def baseEnd_173422 : Nat := 29682947354708573109151

theorem tailTrace_173422 : CollatzResearch.WordTrace tailWord_173422 prefixEnd_173422 29682947354708573109151 := by
  unfold tailWord_173422
  simp only [CollatzResearch.WordTrace]
  refine ⟨790652497216148370586315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4216813318486124643127013 790652497216148370586315)
  ·
    refine ⟨1185978745824222555879473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 790652497216148370586315 1185978745824222555879473)
    ·
      refine ⟨889484059368166916909605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185978745824222555879473 889484059368166916909605)
      ·
        refine ⟨166778261131531296920551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 889484059368166916909605 166778261131531296920551)
        ·
          refine ⟨250167391697296945380827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166778261131531296920551 250167391697296945380827)
          ·
            refine ⟨375251087545945418071241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250167391697296945380827 375251087545945418071241)
            ·
              refine ⟨281438315659459063553431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375251087545945418071241 281438315659459063553431)
              ·
                refine ⟨422157473489188595330147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281438315659459063553431 422157473489188595330147)
                ·
                  refine ⟨633236210233782892995221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422157473489188595330147 633236210233782892995221)
                  ·
                    refine ⟨29682947354708573109151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 633236210233782892995221 29682947354708573109151)
                    ·
                      rfl

theorem cell23_173422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_173422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173422 prefixEnd_173422 := by exact prefixLift 173422
  have htrace : WordTrace (prefixWord ++ tailWord_173422) baseStart_173422 baseEnd_173422 := by
    simpa [prefixWord, tailWord_173422, baseEnd_173422] using wordTrace_append hprefix tailTrace_173422
  have hstable : (prefixWord ++ tailWord_173422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173422).length < 2 ^ (prefixWord ++ tailWord_173422).sum := by decide
  have hdescent : baseEnd_173422 < baseStart_173422 := by decide
  rcases family_descends (prefixWord ++ tailWord_173422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173429 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_173429 : Nat := 118140960795 + 173429 * 2 ^ 59
def prefixEnd_173429 : Nat := 4983230072969 + 3 ^ 40 * 173429 * 2
def baseEnd_173429 : Nat := 89052436428707191939921

theorem tailTrace_173429 : CollatzResearch.WordTrace tailWord_173429 prefixEnd_173429 89052436428707191939921 := by
  unfold tailWord_173429
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325475288703827160195341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4216983525802551440130227 6325475288703827160195341)
  ·
    refine ⟨2372053233263935185073253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6325475288703827160195341 2372053233263935185073253)
    ·
      refine ⟨444759981236987847201235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2372053233263935185073253 444759981236987847201235)
      ·
        refine ⟨667139971855481770801853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444759981236987847201235 667139971855481770801853)
        ·
          refine ⟨250177489445805664050695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 667139971855481770801853 250177489445805664050695)
          ·
            refine ⟨375266234168708496076043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250177489445805664050695 375266234168708496076043)
            ·
              refine ⟨562899351253062744114065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375266234168708496076043 562899351253062744114065)
              ·
                refine ⟨422174513439797058085549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562899351253062744114065 422174513439797058085549)
                ·
                  refine ⟨158315442539923896782081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422174513439797058085549 158315442539923896782081)
                  ·
                    refine ⟨118736581904942922586561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158315442539923896782081 118736581904942922586561)
                    ·
                      refine ⟨89052436428707191939921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118736581904942922586561 89052436428707191939921)
                      ·
                        rfl

theorem cell23_173429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_173429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173429 prefixEnd_173429 := by exact prefixLift 173429
  have htrace : WordTrace (prefixWord ++ tailWord_173429) baseStart_173429 baseEnd_173429 := by
    simpa [prefixWord, tailWord_173429, baseEnd_173429] using wordTrace_append hprefix tailTrace_173429
  have hstable : (prefixWord ++ tailWord_173429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173429).length < 2 ^ (prefixWord ++ tailWord_173429).sum := by decide
  have hdescent : baseEnd_173429 < baseStart_173429 := by decide
  rcases family_descends (prefixWord ++ tailWord_173429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173431 : List Nat := [1, 1, 3, 1, 1, 2, 3, 2, 2, 7]
def baseStart_173431 : Nat := 118140960795 + 173431 * 2 ^ 59
def prefixEnd_173431 : Nat := 4983230072969 + 3 ^ 40 * 173431 * 2
def baseEnd_173431 : Nat := 29684487796672061371637

theorem tailTrace_173431 : CollatzResearch.WordTrace tailWord_173431 prefixEnd_173431 29684487796672061371637 := by
  unfold tailWord_173431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6325548234696581501768147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4217032156464387667845431 6325548234696581501768147)
  ·
    refine ⟨9488322352044872252652221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6325548234696581501768147 9488322352044872252652221)
    ·
      refine ⟨3558120882016827094744583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9488322352044872252652221 3558120882016827094744583)
      ·
        refine ⟨5337181323025240642116875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558120882016827094744583 5337181323025240642116875)
        ·
          refine ⟨8005771984537860963175313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337181323025240642116875 8005771984537860963175313)
          ·
            refine ⟨6004328988403395722381485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8005771984537860963175313 6004328988403395722381485)
            ·
              refine ⟨2251623370651273395893057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6004328988403395722381485 2251623370651273395893057)
              ·
                refine ⟨1688717527988455046919793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251623370651273395893057 1688717527988455046919793)
                ·
                  refine ⟨1266538145991341285189845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1688717527988455046919793 1266538145991341285189845)
                  ·
                    refine ⟨29684487796672061371637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1266538145991341285189845 29684487796672061371637)
                    ·
                      rfl

theorem cell23_173431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 7].length) (baseStart_173431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173431 prefixEnd_173431 := by exact prefixLift 173431
  have htrace : WordTrace (prefixWord ++ tailWord_173431) baseStart_173431 baseEnd_173431 := by
    simpa [prefixWord, tailWord_173431, baseEnd_173431] using wordTrace_append hprefix tailTrace_173431
  have hstable : (prefixWord ++ tailWord_173431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173431).length < 2 ^ (prefixWord ++ tailWord_173431).sum := by decide
  have hdescent : baseEnd_173431 < baseStart_173431 := by decide
  rcases family_descends (prefixWord ++ tailWord_173431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173442 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_173442 : Nat := 118140960795 + 173442 * 2 ^ 59
def prefixEnd_173442 : Nat := 4983230072969 + 3 ^ 40 * 173442 * 2
def baseEnd_173442 : Nat := 89059111677215641077361

theorem tailTrace_173442 : CollatzResearch.WordTrace tailWord_173442 prefixEnd_173442 89059111677215641077361 := by
  unfold tailWord_173442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581487359414182595104645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4217299625104486920279053 1581487359414182595104645)
  ·
    refine ⟨296528879890159236582121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1581487359414182595104645 296528879890159236582121)
    ·
      refine ⟨222396659917619427436591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296528879890159236582121 222396659917619427436591)
      ·
        refine ⟨333594989876429141154887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222396659917619427436591 333594989876429141154887)
        ·
          refine ⟨500392484814643711732331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333594989876429141154887 500392484814643711732331)
          ·
            refine ⟨750588727221965567598497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500392484814643711732331 750588727221965567598497)
            ·
              refine ⟨562941545416474175698873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750588727221965567598497 562941545416474175698873)
              ·
                refine ⟨422206159062355631774155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562941545416474175698873 422206159062355631774155)
                ·
                  refine ⟨633309238593533447661233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422206159062355631774155 633309238593533447661233)
                  ·
                    refine ⟨474981928945150085745925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 633309238593533447661233 474981928945150085745925)
                    ·
                      refine ⟨89059111677215641077361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 474981928945150085745925 89059111677215641077361)
                      ·
                        rfl

theorem cell23_173442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_173442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173442 prefixEnd_173442 := by exact prefixLift 173442
  have htrace : WordTrace (prefixWord ++ tailWord_173442) baseStart_173442 baseEnd_173442 := by
    simpa [prefixWord, tailWord_173442, baseEnd_173442] using wordTrace_append hprefix tailTrace_173442
  have hstable : (prefixWord ++ tailWord_173442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173442).length < 2 ^ (prefixWord ++ tailWord_173442).sum := by decide
  have hdescent : baseEnd_173442 < baseStart_173442 := by decide
  rcases family_descends (prefixWord ++ tailWord_173442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173449 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 1, 2, 3]
def baseStart_173449 : Nat := 118140960795 + 173449 * 2 ^ 59
def prefixEnd_173449 : Nat := 4983230072969 + 3 ^ 40 * 173449 * 2
def baseEnd_173449 : Nat := 89062706041797113689829

theorem tailTrace_173449 : CollatzResearch.WordTrace tailWord_173449 prefixEnd_173449 89062706041797113689829 := by
  unfold tailWord_173449
  simp only [CollatzResearch.WordTrace]
  refine ⟨6326204748631370575923401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4217469832420913717282267 6326204748631370575923401)
  ·
    refine ⟨4744653561473527931942551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6326204748631370575923401 4744653561473527931942551)
    ·
      refine ⟨7116980342210291897913827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4744653561473527931942551 7116980342210291897913827)
      ·
        refine ⟨10675470513315437846870741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7116980342210291897913827 10675470513315437846870741)
        ·
          refine ⟨250206340155830574536033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10675470513315437846870741 250206340155830574536033)
          ·
            refine ⟨187654755116872930902025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250206340155830574536033 187654755116872930902025)
            ·
              refine ⟨140741066337654698176519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187654755116872930902025 140741066337654698176519)
              ·
                refine ⟨211111599506482047264779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140741066337654698176519 211111599506482047264779)
                ·
                  refine ⟨316667399259723070897169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211111599506482047264779 316667399259723070897169)
                  ·
                    refine ⟨237500549444792303172877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 316667399259723070897169 237500549444792303172877)
                    ·
                      refine ⟨89062706041797113689829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237500549444792303172877 89062706041797113689829)
                      ·
                        rfl

theorem cell23_173449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 1, 2, 3].length) (baseStart_173449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173449 prefixEnd_173449 := by exact prefixLift 173449
  have htrace : WordTrace (prefixWord ++ tailWord_173449) baseStart_173449 baseEnd_173449 := by
    simpa [prefixWord, tailWord_173449, baseEnd_173449] using wordTrace_append hprefix tailTrace_173449
  have hstable : (prefixWord ++ tailWord_173449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173449).length < 2 ^ (prefixWord ++ tailWord_173449).sum := by decide
  have hdescent : baseEnd_173449 < baseStart_173449 := by decide
  rcases family_descends (prefixWord ++ tailWord_173449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173479 : List Nat := [1, 1, 6, 1, 1, 1, 5, 1, 2, 1, 3]
def baseStart_173479 : Nat := 118140960795 + 173479 * 2 ^ 59
def prefixEnd_173479 : Nat := 4983230072969 + 3 ^ 40 * 173479 * 2
def baseEnd_173479 : Nat := 89078110461431996314691

theorem tailTrace_173479 : CollatzResearch.WordTrace tailWord_173479 prefixEnd_173479 89078110461431996314691 := by
  unfold tailWord_173479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327298938522685699515491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4218199292348457133010327 6327298938522685699515491)
  ·
    refine ⟨9490948407784028549273237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6327298938522685699515491 9490948407784028549273237)
    ·
      refine ⟨444888206614876338247183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9490948407784028549273237 444888206614876338247183)
      ·
        refine ⟨667332309922314507370775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444888206614876338247183 667332309922314507370775)
        ·
          refine ⟨1000998464883471761056163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667332309922314507370775 1000998464883471761056163)
          ·
            refine ⟨1501497697325207641584245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000998464883471761056163 1501497697325207641584245)
            ·
              refine ⟨140765409124238216398523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1501497697325207641584245 140765409124238216398523)
              ·
                refine ⟨211148113686357324597785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140765409124238216398523 211148113686357324597785)
                ·
                  refine ⟨158361085264767993448339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211148113686357324597785 158361085264767993448339)
                  ·
                    refine ⟨237541627897151990172509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158361085264767993448339 237541627897151990172509)
                    ·
                      refine ⟨89078110461431996314691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237541627897151990172509 89078110461431996314691)
                      ·
                        rfl

theorem cell23_173479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_173479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173479 prefixEnd_173479 := by exact prefixLift 173479
  have htrace : WordTrace (prefixWord ++ tailWord_173479) baseStart_173479 baseEnd_173479 := by
    simpa [prefixWord, tailWord_173479, baseEnd_173479] using wordTrace_append hprefix tailTrace_173479
  have hstable : (prefixWord ++ tailWord_173479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173479).length < 2 ^ (prefixWord ++ tailWord_173479).sum := by decide
  have hdescent : baseEnd_173479 < baseStart_173479 := by decide
  rcases family_descends (prefixWord ++ tailWord_173479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173585 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 3, 4]
def baseStart_173585 : Nat := 118140960795 + 173585 * 2 ^ 59
def prefixEnd_173585 : Nat := 4983230072969 + 3 ^ 40 * 173585 * 2
def baseEnd_173585 : Nat := 29710846470269527196401

theorem tailTrace_173585 : CollatzResearch.WordTrace tailWord_173585 prefixEnd_173585 29710846470269527196401 := by
  unfold tailWord_173585
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331165076138665802874209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4220776717425777201916139 6331165076138665802874209)
  ·
    refine ⟨4748373807103999352155657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6331165076138665802874209 4748373807103999352155657)
    ·
      refine ⟨3561280355327999514116743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4748373807103999352155657 3561280355327999514116743)
      ·
        refine ⟨5341920532991999271175115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561280355327999514116743 5341920532991999271175115)
        ·
          refine ⟨8012880799487998906762673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5341920532991999271175115 8012880799487998906762673)
          ·
            refine ⟨6009660599615999180072005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8012880799487998906762673 6009660599615999180072005)
            ·
              refine ⟨1126811362427999846263501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6009660599615999180072005 1126811362427999846263501)
              ·
                refine ⟨422554260910499942348813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126811362427999846263501 422554260910499942348813)
                ·
                  refine ⟨158457847841437478380805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422554260910499942348813 158457847841437478380805)
                  ·
                    refine ⟨29710846470269527196401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158457847841437478380805 29710846470269527196401)
                    ·
                      rfl

theorem cell23_173585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_173585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173585 prefixEnd_173585 := by exact prefixLift 173585
  have htrace : WordTrace (prefixWord ++ tailWord_173585) baseStart_173585 baseEnd_173585 := by
    simpa [prefixWord, tailWord_173585, baseEnd_173585] using wordTrace_append hprefix tailTrace_173585
  have hstable : (prefixWord ++ tailWord_173585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173585).length < 2 ^ (prefixWord ++ tailWord_173585).sum := by decide
  have hdescent : baseEnd_173585 < baseStart_173585 := by decide
  rcases family_descends (prefixWord ++ tailWord_173585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173619 : List Nat := [1, 1, 1, 2, 4, 4, 2, 3, 1, 4]
def baseStart_173619 : Nat := 118140960795 + 173619 * 2 ^ 59
def prefixEnd_173619 : Nat := 4983230072969 + 3 ^ 40 * 173619 * 2
def baseEnd_173619 : Nat := 29716665917687149521349

theorem tailTrace_173619 : CollatzResearch.WordTrace tailWord_173619 prefixEnd_173619 29716665917687149521349 := by
  unfold tailWord_173619
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332405158015489609611911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4221603438676993073074607 6332405158015489609611911)
  ·
    refine ⟨9498607737023234414417867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6332405158015489609611911 9498607737023234414417867)
    ·
      refine ⟨14247911605534851621626801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498607737023234414417867 14247911605534851621626801)
      ·
        refine ⟨10685933704151138716220101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14247911605534851621626801 10685933704151138716220101)
        ·
          refine ⟨2003612569528338509291269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10685933704151138716220101 2003612569528338509291269)
          ·
            refine ⟨375677356786563470492113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2003612569528338509291269 375677356786563470492113)
            ·
              refine ⟨281758017589922602869085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375677356786563470492113 281758017589922602869085)
              ·
                refine ⟨105659256596220976075907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281758017589922602869085 105659256596220976075907)
                ·
                  refine ⟨158488884894331464113861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105659256596220976075907 158488884894331464113861)
                  ·
                    refine ⟨29716665917687149521349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158488884894331464113861 29716665917687149521349)
                    ·
                      rfl

theorem cell23_173619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 4].length) (baseStart_173619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173619 prefixEnd_173619 := by exact prefixLift 173619
  have htrace : WordTrace (prefixWord ++ tailWord_173619) baseStart_173619 baseEnd_173619 := by
    simpa [prefixWord, tailWord_173619, baseEnd_173619] using wordTrace_append hprefix tailTrace_173619
  have hstable : (prefixWord ++ tailWord_173619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173619).length < 2 ^ (prefixWord ++ tailWord_173619).sum := by decide
  have hdescent : baseEnd_173619 < baseStart_173619 := by decide
  rcases family_descends (prefixWord ++ tailWord_173619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173652 : List Nat := [2, 4, 1, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_173652 : Nat := 118140960795 + 173652 * 2 ^ 59
def prefixEnd_173652 : Nat := 4983230072969 + 3 ^ 40 * 173652 * 2
def baseEnd_173652 : Nat := 89166942614659819451395

theorem tailTrace_173652 : CollatzResearch.WordTrace tailWord_173652 prefixEnd_173652 89166942614659819451395 := by
  unfold tailWord_173652
  simp only [CollatzResearch.WordTrace]
  refine ⟨3166804383447968122781605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4222405844597290830375473 3166804383447968122781605)
  ·
    refine ⟨593775821896494023021551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3166804383447968122781605 593775821896494023021551)
    ·
      refine ⟨890663732844741034532327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593775821896494023021551 890663732844741034532327)
      ·
        refine ⟨1335995599267111551798491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890663732844741034532327 1335995599267111551798491)
        ·
          refine ⟨2003993398900667327697737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335995599267111551798491 2003993398900667327697737)
          ·
            refine ⟨1502995049175500495773303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003993398900667327697737 1502995049175500495773303)
            ·
              refine ⟨2254492573763250743659955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502995049175500495773303 2254492573763250743659955)
              ·
                refine ⟨3381738860644876115489933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254492573763250743659955 3381738860644876115489933)
                ·
                  refine ⟨1268152072741828543308725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3381738860644876115489933 1268152072741828543308725)
                  ·
                    refine ⟨118889256819546425935193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1268152072741828543308725 118889256819546425935193)
                    ·
                      refine ⟨89166942614659819451395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118889256819546425935193 89166942614659819451395)
                      ·
                        rfl

theorem cell23_173652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_173652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173652 prefixEnd_173652 := by exact prefixLift 173652
  have htrace : WordTrace (prefixWord ++ tailWord_173652) baseStart_173652 baseEnd_173652 := by
    simpa [prefixWord, tailWord_173652, baseEnd_173652] using wordTrace_append hprefix tailTrace_173652
  have hstable : (prefixWord ++ tailWord_173652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173652).length < 2 ^ (prefixWord ++ tailWord_173652).sum := by decide
  have hdescent : baseEnd_173652 < baseStart_173652 := by decide
  rcases family_descends (prefixWord ++ tailWord_173652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173686 : List Nat := [5, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_173686 : Nat := 118140960795 + 173686 * 2 ^ 59
def prefixEnd_173686 : Nat := 4983230072969 + 3 ^ 40 * 173686 * 2
def baseEnd_173686 : Nat := 89184400956912686426239

theorem tailTrace_173686 : CollatzResearch.WordTrace tailWord_173686 prefixEnd_173686 89184400956912686426239 := by
  unfold tailWord_173686
  simp only [CollatzResearch.WordTrace]
  refine ⟨395928053048297503268807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4223232565848506701533941 395928053048297503268807)
  ·
    refine ⟨593892079572446254903211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395928053048297503268807 593892079572446254903211)
    ·
      refine ⟨890838119358669382354817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593892079572446254903211 890838119358669382354817)
      ·
        refine ⟨668128589519002036766113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 890838119358669382354817 668128589519002036766113)
        ·
          refine ⟨501096442139251527574585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668128589519002036766113 501096442139251527574585)
          ·
            refine ⟨375822331604438645680939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501096442139251527574585 375822331604438645680939)
            ·
              refine ⟨563733497406657968521409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375822331604438645680939 563733497406657968521409)
              ·
                refine ⟨422800123054993476391057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563733497406657968521409 422800123054993476391057)
                ·
                  refine ⟨317100092291245107293293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422800123054993476391057 317100092291245107293293)
                  ·
                    refine ⟨118912534609216915234985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317100092291245107293293 118912534609216915234985)
                    ·
                      refine ⟨89184400956912686426239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118912534609216915234985 89184400956912686426239)
                      ·
                        rfl

theorem cell23_173686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_173686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173686 prefixEnd_173686 := by exact prefixLift 173686
  have htrace : WordTrace (prefixWord ++ tailWord_173686) baseStart_173686 baseEnd_173686 := by
    simpa [prefixWord, tailWord_173686, baseEnd_173686] using wordTrace_append hprefix tailTrace_173686
  have hstable : (prefixWord ++ tailWord_173686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173686).length < 2 ^ (prefixWord ++ tailWord_173686).sum := by decide
  have hdescent : baseEnd_173686 < baseStart_173686 := by decide
  rcases family_descends (prefixWord ++ tailWord_173686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173692 : List Nat := [2, 2, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_173692 : Nat := 118140960795 + 173692 * 2 ^ 59
def prefixEnd_173692 : Nat := 4983230072969 + 3 ^ 40 * 173692 * 2
def baseEnd_173692 : Nat := 29729160613613220983737

theorem tailTrace_173692 : CollatzResearch.WordTrace tailWord_173692 prefixEnd_173692 29729160613613220983737 := by
  unfold tailWord_173692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167533843375511538509665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4223378457834015384679553 3167533843375511538509665)
  ·
    refine ⟨2375650382531633653882249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3167533843375511538509665 2375650382531633653882249)
    ·
      refine ⟨1781737786898725240411687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375650382531633653882249 1781737786898725240411687)
      ·
        refine ⟨2672606680348087860617531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781737786898725240411687 2672606680348087860617531)
        ·
          refine ⟨4008910020522131790926297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672606680348087860617531 4008910020522131790926297)
          ·
            refine ⟨3006682515391598843194723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4008910020522131790926297 3006682515391598843194723)
            ·
              refine ⟨4510023773087398264792085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006682515391598843194723 4510023773087398264792085)
              ·
                refine ⟨211407364363471793662129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4510023773087398264792085 211407364363471793662129)
                ·
                  refine ⟨158555523272603845246597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211407364363471793662129 158555523272603845246597)
                  ·
                    refine ⟨29729160613613220983737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158555523272603845246597 29729160613613220983737)
                    ·
                      rfl

theorem cell23_173692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_173692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173692 prefixEnd_173692 := by exact prefixLift 173692
  have htrace : WordTrace (prefixWord ++ tailWord_173692) baseStart_173692 baseEnd_173692 := by
    simpa [prefixWord, tailWord_173692, baseEnd_173692] using wordTrace_append hprefix tailTrace_173692
  have hstable : (prefixWord ++ tailWord_173692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173692).length < 2 ^ (prefixWord ++ tailWord_173692).sum := by decide
  have hdescent : baseEnd_173692 < baseStart_173692 := by decide
  rcases family_descends (prefixWord ++ tailWord_173692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173693 : List Nat := [1, 4, 1, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_173693 : Nat := 118140960795 + 173693 * 2 ^ 59
def prefixEnd_173693 : Nat := 4983230072969 + 3 ^ 40 * 173693 * 2
def baseEnd_173693 : Nat := 89187995321494159038707

theorem tailTrace_173693 : CollatzResearch.WordTrace tailWord_173693 prefixEnd_173693 89187995321494159038707 := by
  unfold tailWord_173693
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335104159747400247805733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4223402773164933498537155 6335104159747400247805733)
  ·
    refine ⟨1187832029952637546463575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6335104159747400247805733 1187832029952637546463575)
    ·
      refine ⟨1781748044928956319695363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187832029952637546463575 1781748044928956319695363)
      ·
        refine ⟨2672622067393434479543045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781748044928956319695363 2672622067393434479543045)
        ·
          refine ⟨501116637636268964914321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2672622067393434479543045 501116637636268964914321)
          ·
            refine ⟨375837478227201723685741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501116637636268964914321 375837478227201723685741)
            ·
              refine ⟨140939054335200646382153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375837478227201723685741 140939054335200646382153)
              ·
                refine ⟨105704290751400484786615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140939054335200646382153 105704290751400484786615)
                ·
                  refine ⟨158556436127100727179923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105704290751400484786615 158556436127100727179923)
                  ·
                    refine ⟨237834654190651090769885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158556436127100727179923 237834654190651090769885)
                    ·
                      refine ⟨89187995321494159038707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237834654190651090769885 89187995321494159038707)
                      ·
                        rfl

theorem cell23_173693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_173693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173693 prefixEnd_173693 := by exact prefixLift 173693
  have htrace : WordTrace (prefixWord ++ tailWord_173693) baseStart_173693 baseEnd_173693 := by
    simpa [prefixWord, tailWord_173693, baseEnd_173693] using wordTrace_append hprefix tailTrace_173693
  have hstable : (prefixWord ++ tailWord_173693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173693).length < 2 ^ (prefixWord ++ tailWord_173693).sum := by decide
  have hdescent : baseEnd_173693 < baseStart_173693 := by decide
  rcases family_descends (prefixWord ++ tailWord_173693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173719 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 3]
def baseStart_173719 : Nat := 118140960795 + 173719 * 2 ^ 59
def prefixEnd_173719 : Nat := 4983230072969 + 3 ^ 40 * 173719 * 2
def baseEnd_173719 : Nat := 89201345818511057313587

theorem tailTrace_173719 : CollatzResearch.WordTrace tailWord_173719 prefixEnd_173719 89201345818511057313587 := by
  unfold tailWord_173719
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336052457653206688252211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4224034971768804458834807 6336052457653206688252211)
  ·
    refine ⟨9504078686479810032378317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6336052457653206688252211 9504078686479810032378317)
    ·
      refine ⟨3564029507429928762141869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9504078686479810032378317 3564029507429928762141869)
      ·
        refine ⟨1336511065286223285803201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3564029507429928762141869 1336511065286223285803201)
        ·
          refine ⟨1002383298964667464352401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336511065286223285803201 1002383298964667464352401)
          ·
            refine ⟨751787474223500598264301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002383298964667464352401 751787474223500598264301)
            ·
              refine ⟨281920302833812724349113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 751787474223500598264301 281920302833812724349113)
              ·
                refine ⟨211440227125359543261835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281920302833812724349113 211440227125359543261835)
                ·
                  refine ⟨317160340688039314892753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211440227125359543261835 317160340688039314892753)
                  ·
                    refine ⟨237870255516029486169565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 317160340688039314892753 237870255516029486169565)
                    ·
                      refine ⟨89201345818511057313587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237870255516029486169565 89201345818511057313587)
                      ·
                        rfl

theorem cell23_173719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_173719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173719 prefixEnd_173719 := by exact prefixLift 173719
  have htrace : WordTrace (prefixWord ++ tailWord_173719) baseStart_173719 baseEnd_173719 := by
    simpa [prefixWord, tailWord_173719, baseEnd_173719] using wordTrace_append hprefix tailTrace_173719
  have hstable : (prefixWord ++ tailWord_173719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173719).length < 2 ^ (prefixWord ++ tailWord_173719).sum := by decide
  have hdescent : baseEnd_173719 < baseStart_173719 := by decide
  rcases family_descends (prefixWord ++ tailWord_173719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173732 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_173732 : Nat := 118140960795 + 173732 * 2 ^ 59
def prefixEnd_173732 : Nat := 4983230072969 + 3 ^ 40 * 173732 * 2
def baseEnd_173732 : Nat := 89208021067019506451027

theorem tailTrace_173732 : CollatzResearch.WordTrace tailWord_173732 prefixEnd_173732 89208021067019506451027 := by
  unfold tailWord_173732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168263303303054954237725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4224351071070739938983633 3168263303303054954237725)
  ·
    refine ⟨1188098738738645607839147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3168263303303054954237725 1188098738738645607839147)
    ·
      refine ⟨1782148108107968411758721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1188098738738645607839147 1782148108107968411758721)
      ·
        refine ⟨1336611081080976308819041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782148108107968411758721 1336611081080976308819041)
        ·
          refine ⟨1002458310810732231614281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336611081080976308819041 1002458310810732231614281)
          ·
            refine ⟨751843733108049173710711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002458310810732231614281 751843733108049173710711)
            ·
              refine ⟨1127765599662073760566067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751843733108049173710711 1127765599662073760566067)
              ·
                refine ⟨1691648399493110640849101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127765599662073760566067 1691648399493110640849101)
                ·
                  refine ⟨634368149809916490318413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1691648399493110640849101 634368149809916490318413)
                  ·
                    refine ⟨237888056178718683869405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634368149809916490318413 237888056178718683869405)
                    ·
                      refine ⟨89208021067019506451027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 237888056178718683869405 89208021067019506451027)
                      ·
                        rfl

theorem cell23_173732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_173732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173732 prefixEnd_173732 := by exact prefixLift 173732
  have htrace : WordTrace (prefixWord ++ tailWord_173732) baseStart_173732 baseEnd_173732 := by
    simpa [prefixWord, tailWord_173732, baseEnd_173732] using wordTrace_append hprefix tailTrace_173732
  have hstable : (prefixWord ++ tailWord_173732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173732).length < 2 ^ (prefixWord ++ tailWord_173732).sum := by decide
  have hdescent : baseEnd_173732 < baseStart_173732 := by decide
  rcases family_descends (prefixWord ++ tailWord_173732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173765 : List Nat := [1, 3, 1, 1, 1, 1, 2, 5, 2, 6]
def baseStart_173765 : Nat := 118140960795 + 173765 * 2 ^ 59
def prefixEnd_173765 : Nat := 4983230072969 + 3 ^ 40 * 173765 * 2
def baseEnd_173765 : Nat := 29741655309539292446125

theorem tailTrace_173765 : CollatzResearch.WordTrace tailWord_173765 prefixEnd_173765 29741655309539292446125 := by
  unfold tailWord_173765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337730215486556544426749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4225153476991037696284499 6337730215486556544426749)
  ·
    refine ⟨2376648830807458704160031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6337730215486556544426749 2376648830807458704160031)
    ·
      refine ⟨3564973246211188056240047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376648830807458704160031 3564973246211188056240047)
      ·
        refine ⟨5347459869316782084360071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564973246211188056240047 5347459869316782084360071)
        ·
          refine ⟨8021189803975173126540107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347459869316782084360071 8021189803975173126540107)
          ·
            refine ⟨12031784705962759689810161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8021189803975173126540107 12031784705962759689810161)
            ·
              refine ⟨9023838529472069767357621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12031784705962759689810161 9023838529472069767357621)
              ·
                refine ⟨845984862138006540689777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9023838529472069767357621 845984862138006540689777)
                ·
                  refine ⟨634488646603504905517333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 845984862138006540689777 634488646603504905517333)
                  ·
                    refine ⟨29741655309539292446125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 634488646603504905517333 29741655309539292446125)
                    ·
                      rfl

theorem cell23_173765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_173765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173765 prefixEnd_173765 := by exact prefixLift 173765
  have htrace : WordTrace (prefixWord ++ tailWord_173765) baseStart_173765 baseEnd_173765 := by
    simpa [prefixWord, tailWord_173765, baseEnd_173765] using wordTrace_append hprefix tailTrace_173765
  have hstable : (prefixWord ++ tailWord_173765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173765).length < 2 ^ (prefixWord ++ tailWord_173765).sum := by decide
  have hdescent : baseEnd_173765 < baseStart_173765 := by decide
  rcases family_descends (prefixWord ++ tailWord_173765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173775 : List Nat := [1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5]
def baseStart_173775 : Nat := 118140960795 + 173775 * 2 ^ 59
def prefixEnd_173775 : Nat := 4983230072969 + 3 ^ 40 * 173775 * 2
def baseEnd_173775 : Nat := 89230100735162838213329

theorem tailTrace_173775 : CollatzResearch.WordTrace tailWord_173775 prefixEnd_173775 89230100735162838213329 := by
  unfold tailWord_173775
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338094945450328252290779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4225396630300218834860519 6338094945450328252290779)
  ·
    refine ⟨9507142418175492378436169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6338094945450328252290779 9507142418175492378436169)
    ·
      refine ⟨7130356813631619283827127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9507142418175492378436169 7130356813631619283827127)
      ·
        refine ⟨10695535220447428925740691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130356813631619283827127 10695535220447428925740691)
        ·
          refine ⟨16043302830671143388611037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10695535220447428925740691 16043302830671143388611037)
          ·
            refine ⟨6016238561501678770729139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16043302830671143388611037 6016238561501678770729139)
            ·
              refine ⟨9024357842252518156093709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016238561501678770729139 9024357842252518156093709)
              ·
                refine ⟨3384134190844694308535141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9024357842252518156093709 3384134190844694308535141)
                ·
                  refine ⟨634525160783380182850339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3384134190844694308535141 634525160783380182850339)
                  ·
                    refine ⟨951787741175070274275509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634525160783380182850339 951787741175070274275509)
                    ·
                      refine ⟨89230100735162838213329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 951787741175070274275509 89230100735162838213329)
                      ·
                        rfl

theorem cell23_173775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 1, 5].length) (baseStart_173775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173775 prefixEnd_173775 := by exact prefixLift 173775
  have htrace : WordTrace (prefixWord ++ tailWord_173775) baseStart_173775 baseEnd_173775 := by
    simpa [prefixWord, tailWord_173775, baseEnd_173775] using wordTrace_append hprefix tailTrace_173775
  have hstable : (prefixWord ++ tailWord_173775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173775).length < 2 ^ (prefixWord ++ tailWord_173775).sum := by decide
  have hdescent : baseEnd_173775 < baseStart_173775 := by decide
  rcases family_descends (prefixWord ++ tailWord_173775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173802 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_173802 : Nat := 118140960795 + 173802 * 2 ^ 59
def prefixEnd_173802 : Nat := 4983230072969 + 3 ^ 40 * 173802 * 2
def baseEnd_173802 : Nat := 89243964712834232575705

theorem tailTrace_173802 : CollatzResearch.WordTrace tailWord_173802 prefixEnd_173802 89243964712834232575705 := by
  unfold tailWord_173802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584769929088127965880915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4226053144235007909015773 1584769929088127965880915)
  ·
    refine ⟨2377154893632191948821373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1584769929088127965880915 2377154893632191948821373)
    ·
      refine ⟨891433085112071980808015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2377154893632191948821373 891433085112071980808015)
      ·
        refine ⟨1337149627668107971212023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891433085112071980808015 1337149627668107971212023)
        ·
          refine ⟨2005724441502161956818035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337149627668107971212023 2005724441502161956818035)
          ·
            refine ⟨3008586662253242935227053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2005724441502161956818035 3008586662253242935227053)
            ·
              refine ⟨1128219998344966100710145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3008586662253242935227053 1128219998344966100710145)
              ·
                refine ⟨846164998758724575532609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128219998344966100710145 846164998758724575532609)
                ·
                  refine ⟨634623749069043431649457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846164998758724575532609 634623749069043431649457)
                  ·
                    refine ⟨475967811801782573737093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634623749069043431649457 475967811801782573737093)
                    ·
                      refine ⟨89243964712834232575705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 475967811801782573737093 89243964712834232575705)
                      ·
                        rfl

theorem cell23_173802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_173802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173802 prefixEnd_173802 := by exact prefixLift 173802
  have htrace : WordTrace (prefixWord ++ tailWord_173802) baseStart_173802 baseEnd_173802 := by
    simpa [prefixWord, tailWord_173802, baseEnd_173802] using wordTrace_append hprefix tailTrace_173802
  have hstable : (prefixWord ++ tailWord_173802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173802).length < 2 ^ (prefixWord ++ tailWord_173802).sum := by decide
  have hdescent : baseEnd_173802 < baseStart_173802 := by decide
  rcases family_descends (prefixWord ++ tailWord_173802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173806 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2]
def baseStart_173806 : Nat := 118140960795 + 173806 * 2 ^ 59
def prefixEnd_173806 : Nat := 4983230072969 + 3 ^ 40 * 173806 * 2
def baseEnd_173806 : Nat := 89246018635452216925687

theorem tailTrace_173806 : CollatzResearch.WordTrace tailWord_173806 prefixEnd_173806 89246018635452216925687 := by
  unfold tailWord_173806
  simp only [CollatzResearch.WordTrace]
  refine ⟨792403201042252568333659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4226150405558680364446181 792403201042252568333659)
  ·
    refine ⟨1188604801563378852500489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 792403201042252568333659 1188604801563378852500489)
    ·
      refine ⟨891453601172534139375367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1188604801563378852500489 891453601172534139375367)
      ·
        refine ⟨1337180401758801209063051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891453601172534139375367 1337180401758801209063051)
        ·
          refine ⟨2005770602638201813594577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337180401758801209063051 2005770602638201813594577)
          ·
            refine ⟨1504327951978651360195933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005770602638201813594577 1504327951978651360195933)
            ·
              refine ⟨564122981991994260073475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504327951978651360195933 564122981991994260073475)
              ·
                refine ⟨846184472987991390110213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564122981991994260073475 846184472987991390110213)
                ·
                  refine ⟨158659588685248385645665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846184472987991390110213 158659588685248385645665)
                  ·
                    refine ⟨118994691513936289234249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158659588685248385645665 118994691513936289234249)
                    ·
                      refine ⟨89246018635452216925687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 118994691513936289234249 89246018635452216925687)
                      ·
                        rfl

theorem cell23_173806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_173806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173806 prefixEnd_173806 := by exact prefixLift 173806
  have htrace : WordTrace (prefixWord ++ tailWord_173806) baseStart_173806 baseEnd_173806 := by
    simpa [prefixWord, tailWord_173806, baseEnd_173806] using wordTrace_append hprefix tailTrace_173806
  have hstable : (prefixWord ++ tailWord_173806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173806).length < 2 ^ (prefixWord ++ tailWord_173806).sum := by decide
  have hdescent : baseEnd_173806 < baseStart_173806 := by decide
  rcases family_descends (prefixWord ++ tailWord_173806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173852 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_173852 : Nat := 118140960795 + 173852 * 2 ^ 59
def prefixEnd_173852 : Nat := 4983230072969 + 3 ^ 40 * 173852 * 2
def baseEnd_173852 : Nat := 89269638745559036950475

theorem tailTrace_173852 : CollatzResearch.WordTrace tailWord_173852 prefixEnd_173852 89269638745559036950475 := by
  unfold tailWord_173852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170451683085685201421905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4227268910780913601895873 3170451683085685201421905)
  ·
    refine ⟨2377838762314263901066429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3170451683085685201421905 2377838762314263901066429)
    ·
      refine ⟨891689535867848962899911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2377838762314263901066429 891689535867848962899911)
      ·
        refine ⟨1337534303801773444349867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891689535867848962899911 1337534303801773444349867)
        ·
          refine ⟨2006301455702660166524801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337534303801773444349867 2006301455702660166524801)
          ·
            refine ⟨1504726091776995124893601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2006301455702660166524801 1504726091776995124893601)
            ·
              refine ⟨1128544568832746343670201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1504726091776995124893601 1128544568832746343670201)
              ·
                refine ⟨846408426624559757752651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128544568832746343670201 846408426624559757752651)
                ·
                  refine ⟨1269612639936839636628977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846408426624559757752651 1269612639936839636628977)
                  ·
                    refine ⟨952209479952629727471733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269612639936839636628977 952209479952629727471733)
                    ·
                      refine ⟨89269638745559036950475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 952209479952629727471733 89269638745559036950475)
                      ·
                        rfl

theorem cell23_173852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_173852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173852 prefixEnd_173852 := by exact prefixLift 173852
  have htrace : WordTrace (prefixWord ++ tailWord_173852) baseStart_173852 baseEnd_173852 := by
    simpa [prefixWord, tailWord_173852, baseEnd_173852] using wordTrace_append hprefix tailTrace_173852
  have hstable : (prefixWord ++ tailWord_173852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173852).length < 2 ^ (prefixWord ++ tailWord_173852).sum := by decide
  have hdescent : baseEnd_173852 < baseStart_173852 := by decide
  rcases family_descends (prefixWord ++ tailWord_173852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173919 : List Nat := [1, 1, 2, 3, 1, 5, 2, 2, 6]
def baseStart_173919 : Nat := 118140960795 + 173919 * 2 ^ 59
def prefixEnd_173919 : Nat := 4983230072969 + 3 ^ 40 * 173919 * 2
def baseEnd_173919 : Nat := 9922671327712252756963

theorem tailTrace_173919 : CollatzResearch.WordTrace tailWord_173919 prefixEnd_173919 9922671327712252756963 := by
  unfold tailWord_173919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343347056928640845532811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4228898037952427230355207 6343347056928640845532811)
  ·
    refine ⟨9515020585392961268299217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343347056928640845532811 9515020585392961268299217)
    ·
      refine ⟨7136265439044720951224413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9515020585392961268299217 7136265439044720951224413)
      ·
        refine ⟨2676099539641770356709155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7136265439044720951224413 2676099539641770356709155)
        ·
          refine ⟨4014149309462655535063733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676099539641770356709155 4014149309462655535063733)
          ·
            refine ⟨376326497762123956412225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4014149309462655535063733 376326497762123956412225)
            ·
              refine ⟨282244873321592967309169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376326497762123956412225 282244873321592967309169)
              ·
                refine ⟨211683654991194725481877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282244873321592967309169 211683654991194725481877)
                ·
                  refine ⟨9922671327712252756963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211683654991194725481877 9922671327712252756963)
                  ·
                    rfl

theorem cell23_173919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 6].length) (baseStart_173919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173919 prefixEnd_173919 := by exact prefixLift 173919
  have htrace : WordTrace (prefixWord ++ tailWord_173919) baseStart_173919 baseEnd_173919 := by
    simpa [prefixWord, tailWord_173919, baseEnd_173919] using wordTrace_append hprefix tailTrace_173919
  have hstable : (prefixWord ++ tailWord_173919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173919).length < 2 ^ (prefixWord ++ tailWord_173919).sum := by decide
  have hdescent : baseEnd_173919 < baseStart_173919 := by decide
  rcases family_descends (prefixWord ++ tailWord_173919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173923 : List Nat := [1, 1, 1, 5, 4, 1, 1, 4, 1, 4]
def baseStart_173923 : Nat := 118140960795 + 173923 * 2 ^ 59
def prefixEnd_173923 : Nat := 4983230072969 + 3 ^ 40 * 173923 * 2
def baseEnd_173923 : Nat := 29768698624009419720883

theorem tailTrace_173923 : CollatzResearch.WordTrace tailWord_173923 prefixEnd_173923 29768698624009419720883 := by
  unfold tailWord_173923
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343492948914149528678423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4228995299276099685785615 6343492948914149528678423)
  ·
    refine ⟨9515239423371224293017635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343492948914149528678423 9515239423371224293017635)
    ·
      refine ⟨14272859135056836439526453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515239423371224293017635 14272859135056836439526453)
      ·
        refine ⟨1338080543911578416205605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14272859135056836439526453 1338080543911578416205605)
        ·
          refine ⟨250890101983420953038551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1338080543911578416205605 250890101983420953038551)
          ·
            refine ⟨376335152975131429557827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250890101983420953038551 376335152975131429557827)
            ·
              refine ⟨564502729462697144336741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376335152975131429557827 564502729462697144336741)
              ·
                refine ⟨105844261774255714563139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564502729462697144336741 105844261774255714563139)
                ·
                  refine ⟨158766392661383571844709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105844261774255714563139 158766392661383571844709)
                  ·
                    refine ⟨29768698624009419720883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 158766392661383571844709 29768698624009419720883)
                    ·
                      rfl

theorem cell23_173923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 4, 1, 4].length) (baseStart_173923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173923 prefixEnd_173923 := by exact prefixLift 173923
  have htrace : WordTrace (prefixWord ++ tailWord_173923) baseStart_173923 baseEnd_173923 := by
    simpa [prefixWord, tailWord_173923, baseEnd_173923] using wordTrace_append hprefix tailTrace_173923
  have hstable : (prefixWord ++ tailWord_173923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173923).length < 2 ^ (prefixWord ++ tailWord_173923).sum := by decide
  have hdescent : baseEnd_173923 < baseStart_173923 := by decide
  rcases family_descends (prefixWord ++ tailWord_173923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173929 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 3]
def baseStart_173929 : Nat := 118140960795 + 173929 * 2 ^ 59
def prefixEnd_173929 : Nat := 4983230072969 + 3 ^ 40 * 173929 * 2
def baseEnd_173929 : Nat := 89309176755955235687621

theorem tailTrace_173929 : CollatzResearch.WordTrace tailWord_173929 prefixEnd_173929 89309176755955235687621 := by
  unfold tailWord_173929
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343711786892412553396841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4229141191261608368931227 6343711786892412553396841)
  ·
    refine ⟨4757783840169309415047631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6343711786892412553396841 4757783840169309415047631)
    ·
      refine ⟨7136675760253964122571447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4757783840169309415047631 7136675760253964122571447)
      ·
        refine ⟨10705013640380946183857171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136675760253964122571447 10705013640380946183857171)
        ·
          refine ⟨16057520460571419275785757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10705013640380946183857171 16057520460571419275785757)
          ·
            refine ⟨6021570172714282228419659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16057520460571419275785757 6021570172714282228419659)
            ·
              refine ⟨9032355259071423342629489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6021570172714282228419659 9032355259071423342629489)
              ·
                refine ⟨6774266444303567506972117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9032355259071423342629489 6774266444303567506972117)
                ·
                  refine ⟨158771869788364863444659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6774266444303567506972117 158771869788364863444659)
                  ·
                    refine ⟨238157804682547295166989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158771869788364863444659 238157804682547295166989)
                    ·
                      refine ⟨89309176755955235687621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 238157804682547295166989 89309176755955235687621)
                      ·
                        rfl

theorem cell23_173929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 1, 3].length) (baseStart_173929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173929 prefixEnd_173929 := by exact prefixLift 173929
  have htrace : WordTrace (prefixWord ++ tailWord_173929) baseStart_173929 baseEnd_173929 := by
    simpa [prefixWord, tailWord_173929, baseEnd_173929] using wordTrace_append hprefix tailTrace_173929
  have hstable : (prefixWord ++ tailWord_173929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173929).length < 2 ^ (prefixWord ++ tailWord_173929).sum := by decide
  have hdescent : baseEnd_173929 < baseStart_173929 := by decide
  rcases family_descends (prefixWord ++ tailWord_173929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173939 : List Nat := [1, 1, 1, 2, 2, 1, 3, 4, 1, 5, 2]
def baseStart_173939 : Nat := 118140960795 + 173939 * 2 ^ 59
def prefixEnd_173939 : Nat := 4983230072969 + 3 ^ 40 * 173939 * 2
def baseEnd_173939 : Nat := 89314311562500196562575

theorem tailTrace_173939 : CollatzResearch.WordTrace tailWord_173939 prefixEnd_173939 89314311562500196562575 := by
  unfold tailWord_173939
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344076516856184261260871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4229384344570789507507247 6344076516856184261260871)
  ·
    refine ⟨9516114775284276391891307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6344076516856184261260871 9516114775284276391891307)
    ·
      refine ⟨14274172162926414587836961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9516114775284276391891307 14274172162926414587836961)
      ·
        refine ⟨10705629122194810940877721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14274172162926414587836961 10705629122194810940877721)
        ·
          refine ⟨8029221841646108205658291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10705629122194810940877721 8029221841646108205658291)
          ·
            refine ⟨12043832762469162308487437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8029221841646108205658291 12043832762469162308487437)
            ·
              refine ⟨4516437285925935865682789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12043832762469162308487437 4516437285925935865682789)
              ·
                refine ⟨846831991111112974815523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4516437285925935865682789 846831991111112974815523)
                ·
                  refine ⟨1270247986666669462223285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 846831991111112974815523 1270247986666669462223285)
                  ·
                    refine ⟨119085748750000262083433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1270247986666669462223285 119085748750000262083433)
                    ·
                      refine ⟨89314311562500196562575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119085748750000262083433 89314311562500196562575)
                      ·
                        rfl

theorem cell23_173939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5, 2].length) (baseStart_173939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173939 prefixEnd_173939 := by exact prefixLift 173939
  have htrace : WordTrace (prefixWord ++ tailWord_173939) baseStart_173939 baseEnd_173939 := by
    simpa [prefixWord, tailWord_173939, baseEnd_173939] using wordTrace_append hprefix tailTrace_173939
  have hstable : (prefixWord ++ tailWord_173939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173939).length < 2 ^ (prefixWord ++ tailWord_173939).sum := by decide
  have hdescent : baseEnd_173939 < baseStart_173939 := by decide
  rcases family_descends (prefixWord ++ tailWord_173939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173949 : List Nat := [1, 4, 1, 1, 2, 1, 1, 6, 1, 5]
def baseStart_173949 : Nat := 118140960795 + 173949 * 2 ^ 59
def prefixEnd_173949 : Nat := 4983230072969 + 3 ^ 40 * 173949 * 2
def baseEnd_173949 : Nat := 29773148789681719145843

theorem tailTrace_173949 : CollatzResearch.WordTrace tailWord_173949 prefixEnd_173949 29773148789681719145843 := by
  unfold tailWord_173949
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344441246819955969124901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4229627497879970646083267 6344441246819955969124901)
  ·
    refine ⟨1189582733778741744210919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6344441246819955969124901 1189582733778741744210919)
    ·
      refine ⟨1784374100668112616316379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189582733778741744210919 1784374100668112616316379)
      ·
        refine ⟨2676561151002168924474569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784374100668112616316379 2676561151002168924474569)
        ·
          refine ⟨2007420863251626693355927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676561151002168924474569 2007420863251626693355927)
          ·
            refine ⟨3011131294877440040033891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007420863251626693355927 3011131294877440040033891)
            ·
              refine ⟨4516696942316160060050837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3011131294877440040033891 4516696942316160060050837)
              ·
                refine ⟨211720169171070002814883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4516696942316160060050837 211720169171070002814883)
                ·
                  refine ⟨317580253756605004222325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211720169171070002814883 317580253756605004222325)
                  ·
                    refine ⟨29773148789681719145843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 317580253756605004222325 29773148789681719145843)
                    ·
                      rfl

theorem cell23_173949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_173949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173949 prefixEnd_173949 := by exact prefixLift 173949
  have htrace : WordTrace (prefixWord ++ tailWord_173949) baseStart_173949 baseEnd_173949 := by
    simpa [prefixWord, tailWord_173949, baseEnd_173949] using wordTrace_append hprefix tailTrace_173949
  have hstable : (prefixWord ++ tailWord_173949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173949).length < 2 ^ (prefixWord ++ tailWord_173949).sum := by decide
  have hdescent : baseEnd_173949 < baseStart_173949 := by decide
  rcases family_descends (prefixWord ++ tailWord_173949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173950 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_173950 : Nat := 118140960795 + 173950 * 2 ^ 59
def prefixEnd_173950 : Nat := 4983230072969 + 3 ^ 40 * 173950 * 2
def baseEnd_173950 : Nat := 89319959849699653525025

theorem tailTrace_173950 : CollatzResearch.WordTrace tailWord_173950 prefixEnd_173950 89319959849699653525025 := by
  unfold tailWord_173950
  simp only [CollatzResearch.WordTrace]
  refine ⟨793059714977041642488913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4229651813210888759940869 793059714977041642488913)
  ·
    refine ⟨594794786232781231866685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 793059714977041642488913 594794786232781231866685)
    ·
      refine ⟨223048044837292961950007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 594794786232781231866685 223048044837292961950007)
      ·
        refine ⟨334572067255939442925011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223048044837292961950007 334572067255939442925011)
        ·
          refine ⟨501858100883909164387517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334572067255939442925011 501858100883909164387517)
          ·
            refine ⟨188196787831465936645319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501858100883909164387517 188196787831465936645319)
            ·
              refine ⟨282295181747198904967979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188196787831465936645319 282295181747198904967979)
              ·
                refine ⟨423442772620798357451969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282295181747198904967979 423442772620798357451969)
                ·
                  refine ⟨317582079465598768088977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423442772620798357451969 317582079465598768088977)
                  ·
                    refine ⟨238186559599199076066733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 317582079465598768088977 238186559599199076066733)
                    ·
                      refine ⟨89319959849699653525025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 238186559599199076066733 89319959849699653525025)
                      ·
                        rfl

theorem cell23_173950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_173950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173950 prefixEnd_173950 := by exact prefixLift 173950
  have htrace : WordTrace (prefixWord ++ tailWord_173950) baseStart_173950 baseEnd_173950 := by
    simpa [prefixWord, tailWord_173950, baseEnd_173950] using wordTrace_append hprefix tailTrace_173950
  have hstable : (prefixWord ++ tailWord_173950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173950).length < 2 ^ (prefixWord ++ tailWord_173950).sum := by decide
  have hdescent : baseEnd_173950 < baseStart_173950 := by decide
  rcases family_descends (prefixWord ++ tailWord_173950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173980 : List Nat := [2, 2, 3, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_173980 : Nat := 118140960795 + 173980 * 2 ^ 59
def prefixEnd_173980 : Nat := 4983230072969 + 3 ^ 40 * 173980 * 2
def baseEnd_173980 : Nat := 89335364269334536149887

theorem tailTrace_173980 : CollatzResearch.WordTrace tailWord_173980 prefixEnd_173980 89335364269334536149887 := by
  unfold tailWord_173980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172785954853824131751697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4230381273138432175668929 3172785954853824131751697)
  ·
    refine ⟨2379589466140368098813773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3172785954853824131751697 2379589466140368098813773)
    ·
      refine ⟨892346049802638037055165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2379589466140368098813773 892346049802638037055165)
      ·
        refine ⟨334629768675989263895687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 892346049802638037055165 334629768675989263895687)
        ·
          refine ⟨501944653013983895843531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334629768675989263895687 501944653013983895843531)
          ·
            refine ⟨752916979520975843765297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501944653013983895843531 752916979520975843765297)
            ·
              refine ⟨564687734640731882823973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752916979520975843765297 564687734640731882823973)
              ·
                refine ⟨105878950245137228029495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 564687734640731882823973 105878950245137228029495)
                ·
                  refine ⟨158818425367705842044243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105878950245137228029495 158818425367705842044243)
                  ·
                    refine ⟨238227638051558763066365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158818425367705842044243 238227638051558763066365)
                    ·
                      refine ⟨89335364269334536149887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 238227638051558763066365 89335364269334536149887)
                      ·
                        rfl

theorem cell23_173980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_173980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173980 prefixEnd_173980 := by exact prefixLift 173980
  have htrace : WordTrace (prefixWord ++ tailWord_173980) baseStart_173980 baseEnd_173980 := by
    simpa [prefixWord, tailWord_173980, baseEnd_173980] using wordTrace_append hprefix tailTrace_173980
  have hstable : (prefixWord ++ tailWord_173980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173980).length < 2 ^ (prefixWord ++ tailWord_173980).sum := by decide
  have hdescent : baseEnd_173980 < baseStart_173980 := by decide
  rcases family_descends (prefixWord ++ tailWord_173980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_173989 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_173989 : Nat := 118140960795 + 173989 * 2 ^ 59
def prefixEnd_173989 : Nat := 4983230072969 + 3 ^ 40 * 173989 * 2
def baseEnd_173989 : Nat := 89339985595225000937345

theorem tailTrace_173989 : CollatzResearch.WordTrace tailWord_173989 prefixEnd_173989 89339985595225000937345 := by
  unfold tailWord_173989
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345900166675042800581021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4230600111116695200387347 6345900166675042800581021)
  ·
    refine ⟨2379712562503141050217883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6345900166675042800581021 2379712562503141050217883)
    ·
      refine ⟨3569568843754711575326825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2379712562503141050217883 3569568843754711575326825)
      ·
        refine ⟨2677176632816033681495119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3569568843754711575326825 2677176632816033681495119)
        ·
          refine ⟨4015764949224050522242679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677176632816033681495119 4015764949224050522242679)
          ·
            refine ⟨6023647423836075783364019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015764949224050522242679 6023647423836075783364019)
            ·
              refine ⟨9035471135754113675046029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6023647423836075783364019 9035471135754113675046029)
              ·
                refine ⟨3388301675907792628142261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9035471135754113675046029 3388301675907792628142261)
                ·
                  refine ⟨317653282116355558888337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3388301675907792628142261 317653282116355558888337)
                  ·
                    refine ⟨238239961587266669166253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 317653282116355558888337 238239961587266669166253)
                    ·
                      refine ⟨89339985595225000937345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 238239961587266669166253 89339985595225000937345)
                      ·
                        rfl

theorem cell23_173989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_173989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_173989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_173989 prefixEnd_173989 := by exact prefixLift 173989
  have htrace : WordTrace (prefixWord ++ tailWord_173989) baseStart_173989 baseEnd_173989 := by
    simpa [prefixWord, tailWord_173989, baseEnd_173989] using wordTrace_append hprefix tailTrace_173989
  have hstable : (prefixWord ++ tailWord_173989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_173989).length < 2 ^ (prefixWord ++ tailWord_173989).sum := by decide
  have hdescent : baseEnd_173989 < baseStart_173989 := by decide
  rcases family_descends (prefixWord ++ tailWord_173989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174079 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3]
def baseStart_174079 : Nat := 118140960795 + 174079 * 2 ^ 59
def prefixEnd_174079 : Nat := 4983230072969 + 3 ^ 40 * 174079 * 2
def baseEnd_174079 : Nat := 89386198854129648811931

theorem tailTrace_174079 : CollatzResearch.WordTrace tailWord_174079 prefixEnd_174079 89386198854129648811931 := by
  unfold tailWord_174079
  simp only [CollatzResearch.WordTrace]
  refine ⟨6349182736348988171357291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4232788490899325447571527 6349182736348988171357291)
  ·
    refine ⟨9523774104523482257035937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6349182736348988171357291 9523774104523482257035937)
    ·
      refine ⟨7142830578392611692776953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9523774104523482257035937 7142830578392611692776953)
      ·
        refine ⟨5357122933794458769582715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7142830578392611692776953 5357122933794458769582715)
        ·
          refine ⟨8035684400691688154374073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5357122933794458769582715 8035684400691688154374073)
          ·
            refine ⟨6026763300518766115780555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8035684400691688154374073 6026763300518766115780555)
            ·
              refine ⟨9040144950778149173670833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6026763300518766115780555 9040144950778149173670833)
              ·
                refine ⟨6780108713083611880253125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9040144950778149173670833 6780108713083611880253125)
                ·
                  refine ⟨1271270383703177227547461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6780108713083611880253125 1271270383703177227547461)
                  ·
                    refine ⟨238363196944345730165149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1271270383703177227547461 238363196944345730165149)
                    ·
                      refine ⟨89386198854129648811931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 238363196944345730165149 89386198854129648811931)
                      ·
                        rfl

theorem cell23_174079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_174079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174079 prefixEnd_174079 := by exact prefixLift 174079
  have htrace : WordTrace (prefixWord ++ tailWord_174079) baseStart_174079 baseEnd_174079 := by
    simpa [prefixWord, tailWord_174079, baseEnd_174079] using wordTrace_append hprefix tailTrace_174079
  have hstable : (prefixWord ++ tailWord_174079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174079).length < 2 ^ (prefixWord ++ tailWord_174079).sum := by decide
  have hdescent : baseEnd_174079 < baseStart_174079 := by decide
  rcases family_descends (prefixWord ++ tailWord_174079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174106 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4]
def baseStart_174106 : Nat := 118140960795 + 174106 * 2 ^ 59
def prefixEnd_174106 : Nat := 4983230072969 + 3 ^ 40 * 174106 * 2
def baseEnd_174106 : Nat := 89400062831801043174307

theorem tailTrace_174106 : CollatzResearch.WordTrace tailWord_174106 prefixEnd_174106 89400062831801043174307 := by
  unfold tailWord_174106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587541876812792945647543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4233445004834114521726781 1587541876812792945647543)
  ·
    refine ⟨2381312815219189418471315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587541876812792945647543 2381312815219189418471315)
    ·
      refine ⟨3571969222828784127706973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381312815219189418471315 3571969222828784127706973)
      ·
        refine ⟨1339488458560794047890115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3571969222828784127706973 1339488458560794047890115)
        ·
          refine ⟨2009232687841191071835173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339488458560794047890115 2009232687841191071835173)
          ·
            refine ⟨376731128970223325969095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2009232687841191071835173 376731128970223325969095)
            ·
              refine ⟨565096693455334988953643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376731128970223325969095 565096693455334988953643)
              ·
                refine ⟨847645040183002483430465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565096693455334988953643 847645040183002483430465)
                ·
                  refine ⟨635733780137251862572849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 847645040183002483430465 635733780137251862572849)
                  ·
                    refine ⟨476800335102938896929637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 635733780137251862572849 476800335102938896929637)
                    ·
                      refine ⟨89400062831801043174307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 476800335102938896929637 89400062831801043174307)
                      ·
                        rfl

theorem cell23_174106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_174106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174106 prefixEnd_174106 := by exact prefixLift 174106
  have htrace : WordTrace (prefixWord ++ tailWord_174106) baseStart_174106 baseEnd_174106 := by
    simpa [prefixWord, tailWord_174106, baseEnd_174106] using wordTrace_append hprefix tailTrace_174106
  have hstable : (prefixWord ++ tailWord_174106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174106).length < 2 ^ (prefixWord ++ tailWord_174106).sum := by decide
  have hdescent : baseEnd_174106 < baseStart_174106 := by decide
  rcases family_descends (prefixWord ++ tailWord_174106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174150 : List Nat := [6, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_174150 : Nat := 118140960795 + 174150 * 2 ^ 59
def prefixEnd_174150 : Nat := 4983230072969 + 3 ^ 40 * 174150 * 2
def baseEnd_174150 : Nat := 9935850664510985669345

theorem tailTrace_174150 : CollatzResearch.WordTrace tailWord_174150 prefixEnd_174150 9935850664510985669345 := by
  unfold tailWord_174150
  simp only [CollatzResearch.WordTrace]
  refine ⟨198492884971617728037247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4234514879394511531461269 198492884971617728037247)
  ·
    refine ⟨297739327457426592055871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198492884971617728037247 297739327457426592055871)
    ·
      refine ⟨446608991186139888083807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297739327457426592055871 446608991186139888083807)
      ·
        refine ⟨669913486779209832125711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446608991186139888083807 669913486779209832125711)
        ·
          refine ⟨1004870230168814748188567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669913486779209832125711 1004870230168814748188567)
          ·
            refine ⟨1507305345253222122282851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004870230168814748188567 1507305345253222122282851)
            ·
              refine ⟨2260958017879833183424277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1507305345253222122282851 2260958017879833183424277)
              ·
                refine ⟨105982407088117180473013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2260958017879833183424277 105982407088117180473013)
                ·
                  refine ⟨9935850664510985669345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105982407088117180473013 9935850664510985669345)
                  ·
                    rfl

theorem cell23_174150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_174150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174150 prefixEnd_174150 := by exact prefixLift 174150
  have htrace : WordTrace (prefixWord ++ tailWord_174150) baseStart_174150 baseEnd_174150 := by
    simpa [prefixWord, tailWord_174150, baseEnd_174150] using wordTrace_append hprefix tailTrace_174150
  have hstable : (prefixWord ++ tailWord_174150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174150).length < 2 ^ (prefixWord ++ tailWord_174150).sum := by decide
  have hdescent : baseEnd_174150 < baseStart_174150 := by decide
  rcases family_descends (prefixWord ++ tailWord_174150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174219 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 11]
def baseStart_174219 : Nat := 118140960795 + 174219 * 2 ^ 59
def prefixEnd_174219 : Nat := 4983230072969 + 3 ^ 40 * 174219 * 2
def baseEnd_174219 : Nat := 29819362048586367020429

theorem tailTrace_174219 : CollatzResearch.WordTrace tailWord_174219 prefixEnd_174219 29819362048586367020429 := by
  unfold tailWord_174219
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354288955841792081453711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4236192637227861387635807 6354288955841792081453711)
  ·
    refine ⟨9531433433762688122180567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6354288955841792081453711 9531433433762688122180567)
    ·
      refine ⟨14297150150644032183270851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9531433433762688122180567 14297150150644032183270851)
      ·
        refine ⟨21445725225966048274906277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14297150150644032183270851 21445725225966048274906277)
        ·
          refine ⟨4021073479868634051544927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21445725225966048274906277 4021073479868634051544927)
          ·
            refine ⟨6031610219802951077317391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4021073479868634051544927 6031610219802951077317391)
            ·
              refine ⟨9047415329704426615976087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6031610219802951077317391 9047415329704426615976087)
              ·
                refine ⟨13571122994556639923964131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9047415329704426615976087 13571122994556639923964131)
                ·
                  refine ⟨20356684491834959885946197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13571122994556639923964131 20356684491834959885946197)
                  ·
                    refine ⟨29819362048586367020429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 20356684491834959885946197 29819362048586367020429)
                    ·
                      rfl

theorem cell23_174219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 11].length) (baseStart_174219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174219 prefixEnd_174219 := by exact prefixLift 174219
  have htrace : WordTrace (prefixWord ++ tailWord_174219) baseStart_174219 baseEnd_174219 := by
    simpa [prefixWord, tailWord_174219, baseEnd_174219] using wordTrace_append hprefix tailTrace_174219
  have hstable : (prefixWord ++ tailWord_174219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174219).length < 2 ^ (prefixWord ++ tailWord_174219).sum := by decide
  have hdescent : baseEnd_174219 < baseStart_174219 := by decide
  rcases family_descends (prefixWord ++ tailWord_174219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174233 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 3]
def baseStart_174233 : Nat := 118140960795 + 174233 * 2 ^ 59
def prefixEnd_174233 : Nat := 4983230072969 + 3 ^ 40 * 174233 * 2
def baseEnd_174233 : Nat := 89465274874922046286223

theorem tailTrace_174233 : CollatzResearch.WordTrace tailWord_174233 prefixEnd_174233 89465274874922046286223 := by
  unfold tailWord_174233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354799577791072472463353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4236533051860714981642235 6354799577791072472463353)
  ·
    refine ⟨4766099683343304354347515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6354799577791072472463353 4766099683343304354347515)
    ·
      refine ⟨7149149525014956531521273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766099683343304354347515 7149149525014956531521273)
      ·
        refine ⟨5361862143761217398640955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7149149525014956531521273 5361862143761217398640955)
        ·
          refine ⟨8042793215641826097961433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5361862143761217398640955 8042793215641826097961433)
          ·
            refine ⟨6032094911731369573471075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8042793215641826097961433 6032094911731369573471075)
            ·
              refine ⟨9048142367597054360206613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6032094911731369573471075 9048142367597054360206613)
              ·
                refine ⟨424131673481111923134685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9048142367597054360206613 424131673481111923134685)
                ·
                  refine ⟨159049377555416971175507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424131673481111923134685 159049377555416971175507)
                  ·
                    refine ⟨238574066333125456763261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159049377555416971175507 238574066333125456763261)
                    ·
                      refine ⟨89465274874922046286223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 238574066333125456763261 89465274874922046286223)
                      ·
                        rfl

theorem cell23_174233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 3].length) (baseStart_174233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174233 prefixEnd_174233 := by exact prefixLift 174233
  have htrace : WordTrace (prefixWord ++ tailWord_174233) baseStart_174233 baseEnd_174233 := by
    simpa [prefixWord, tailWord_174233, baseEnd_174233] using wordTrace_append hprefix tailTrace_174233
  have hstable : (prefixWord ++ tailWord_174233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174233).length < 2 ^ (prefixWord ++ tailWord_174233).sum := by decide
  have hdescent : baseEnd_174233 < baseStart_174233 := by decide
  rcases family_descends (prefixWord ++ tailWord_174233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174256 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_174256 : Nat := 118140960795 + 174256 * 2 ^ 59
def prefixEnd_174256 : Nat := 4983230072969 + 3 ^ 40 * 174256 * 2
def baseEnd_174256 : Nat := 89477084929975456298617

theorem tailTrace_174256 : CollatzResearch.WordTrace tailWord_174256 prefixEnd_174256 89477084929975456298617 := by
  unfold tailWord_174256
  simp only [CollatzResearch.WordTrace]
  refine ⟨3177819228353873700275311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4237092304471831600367081 3177819228353873700275311)
  ·
    refine ⟨4766728842530810550412967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3177819228353873700275311 4766728842530810550412967)
    ·
      refine ⟨7150093263796215825619451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766728842530810550412967 7150093263796215825619451)
      ·
        refine ⟨10725139895694323738429177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7150093263796215825619451 10725139895694323738429177)
        ·
          refine ⟨8043854921770742803821883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10725139895694323738429177 8043854921770742803821883)
          ·
            refine ⟨12065782382656114205732825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8043854921770742803821883 12065782382656114205732825)
            ·
              refine ⟨9049336786992085654299619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12065782382656114205732825 9049336786992085654299619)
              ·
                refine ⟨13574005180488128481449429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9049336786992085654299619 13574005180488128481449429)
                ·
                  refine ⟨318140746417690511283971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13574005180488128481449429 318140746417690511283971)
                  ·
                    refine ⟨477211119626535766925957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 318140746417690511283971 477211119626535766925957)
                    ·
                      refine ⟨89477084929975456298617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 477211119626535766925957 89477084929975456298617)
                      ·
                        rfl

theorem cell23_174256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_174256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174256 prefixEnd_174256 := by exact prefixLift 174256
  have htrace : WordTrace (prefixWord ++ tailWord_174256) baseStart_174256 baseEnd_174256 := by
    simpa [prefixWord, tailWord_174256, baseEnd_174256] using wordTrace_append hprefix tailTrace_174256
  have hstable : (prefixWord ++ tailWord_174256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174256).length < 2 ^ (prefixWord ++ tailWord_174256).sum := by decide
  have hdescent : baseEnd_174256 < baseStart_174256 := by decide
  rcases family_descends (prefixWord ++ tailWord_174256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174261 : List Nat := [1, 3, 3, 4, 1, 2, 2, 2, 1, 4]
def baseStart_174261 : Nat := 118140960795 + 174261 * 2 ^ 59
def prefixEnd_174261 : Nat := 4983230072969 + 3 ^ 40 * 174261 * 2
def baseEnd_174261 : Nat := 29826550777749312245365

theorem tailTrace_174261 : CollatzResearch.WordTrace tailWord_174261 prefixEnd_174261 29826550777749312245365 := by
  unfold tailWord_174261
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355820821689633254482637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4237213881126422169655091 6355820821689633254482637)
  ·
    refine ⟨2383432808133612470430989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6355820821689633254482637 2383432808133612470430989)
    ·
      refine ⟨893787303050104676411621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2383432808133612470430989 893787303050104676411621)
      ·
        refine ⟨167585119321894626827179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 893787303050104676411621 167585119321894626827179)
        ·
          refine ⟨251377678982841940240769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167585119321894626827179 251377678982841940240769)
          ·
            refine ⟨188533259237131455180577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251377678982841940240769 188533259237131455180577)
            ·
              refine ⟨141399944427848591385433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188533259237131455180577 141399944427848591385433)
              ·
                refine ⟨106049958320886443539075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141399944427848591385433 106049958320886443539075)
                ·
                  refine ⟨159074937481329665308613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106049958320886443539075 159074937481329665308613)
                  ·
                    refine ⟨29826550777749312245365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159074937481329665308613 29826550777749312245365)
                    ·
                      rfl

theorem cell23_174261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_174261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174261 prefixEnd_174261 := by exact prefixLift 174261
  have htrace : WordTrace (prefixWord ++ tailWord_174261) baseStart_174261 baseEnd_174261 := by
    simpa [prefixWord, tailWord_174261, baseEnd_174261] using wordTrace_append hprefix tailTrace_174261
  have hstable : (prefixWord ++ tailWord_174261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174261).length < 2 ^ (prefixWord ++ tailWord_174261).sum := by decide
  have hdescent : baseEnd_174261 < baseStart_174261 := by decide
  rcases family_descends (prefixWord ++ tailWord_174261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174283 : List Nat := [1, 1, 1, 1, 3, 2, 3, 5, 2, 4]
def baseStart_174283 : Nat := 118140960795 + 174283 * 2 ^ 59
def prefixEnd_174283 : Nat := 4983230072969 + 3 ^ 40 * 174283 * 2
def baseEnd_174283 : Nat := 29830316302548950220331

theorem tailTrace_174283 : CollatzResearch.WordTrace tailWord_174283 prefixEnd_174283 29830316302548950220331 := by
  unfold tailWord_174283
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356623227609931011783503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4237748818406620674522335 6356623227609931011783503)
  ·
    refine ⟨9534934841414896517675255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356623227609931011783503 9534934841414896517675255)
    ·
      refine ⟨14302402262122344776512883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9534934841414896517675255 14302402262122344776512883)
      ·
        refine ⟨21453603393183517164769325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14302402262122344776512883 21453603393183517164769325)
        ·
          refine ⟨8045101272443818936788497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21453603393183517164769325 8045101272443818936788497)
          ·
            refine ⟨6033825954332864202591373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8045101272443818936788497 6033825954332864202591373)
            ·
              refine ⟨2262684732874824075971765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6033825954332864202591373 2262684732874824075971765)
              ·
                refine ⟨212126693707014757122353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2262684732874824075971765 212126693707014757122353)
                ·
                  refine ⟨159095020280261067841765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212126693707014757122353 159095020280261067841765)
                  ·
                    refine ⟨29830316302548950220331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159095020280261067841765 29830316302548950220331)
                    ·
                      rfl

theorem cell23_174283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 4].length) (baseStart_174283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174283 prefixEnd_174283 := by exact prefixLift 174283
  have htrace : WordTrace (prefixWord ++ tailWord_174283) baseStart_174283 baseEnd_174283 := by
    simpa [prefixWord, tailWord_174283, baseEnd_174283] using wordTrace_append hprefix tailTrace_174283
  have hstable : (prefixWord ++ tailWord_174283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174283).length < 2 ^ (prefixWord ++ tailWord_174283).sum := by decide
  have hdescent : baseEnd_174283 < baseStart_174283 := by decide
  rcases family_descends (prefixWord ++ tailWord_174283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174294 : List Nat := [5, 2, 1, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_174294 : Nat := 118140960795 + 174294 * 2 ^ 59
def prefixEnd_174294 : Nat := 4983230072969 + 3 ^ 40 * 174294 * 2
def baseEnd_174294 : Nat := 89496597194846307623443

theorem tailTrace_174294 : CollatzResearch.WordTrace tailWord_174294 prefixEnd_174294 89496597194846307623443 := by
  unfold tailWord_174294
  simp only [CollatzResearch.WordTrace]
  refine ⟨397314026910629993152121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4238016287046719926955957 397314026910629993152121)
  ·
    refine ⟨297985520182972494864091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 397314026910629993152121 297985520182972494864091)
    ·
      refine ⟨446978280274458742296137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297985520182972494864091 446978280274458742296137)
      ·
        refine ⟨335233710205844056722103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446978280274458742296137 335233710205844056722103)
        ·
          refine ⟨502850565308766085083155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335233710205844056722103 502850565308766085083155)
          ·
            refine ⟨754275847963149127624733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502850565308766085083155 754275847963149127624733)
            ·
              refine ⟨282853442986180922859275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 754275847963149127624733 282853442986180922859275)
              ·
                refine ⟨424280164479271384288913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282853442986180922859275 424280164479271384288913)
                ·
                  refine ⟨318210123359453538216685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424280164479271384288913 318210123359453538216685)
                  ·
                    refine ⟨119328796259795076831257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318210123359453538216685 119328796259795076831257)
                    ·
                      refine ⟨89496597194846307623443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119328796259795076831257 89496597194846307623443)
                      ·
                        rfl

theorem cell23_174294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_174294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174294 prefixEnd_174294 := by exact prefixLift 174294
  have htrace : WordTrace (prefixWord ++ tailWord_174294) baseStart_174294 baseEnd_174294 := by
    simpa [prefixWord, tailWord_174294, baseEnd_174294] using wordTrace_append hprefix tailTrace_174294
  have hstable : (prefixWord ++ tailWord_174294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174294).length < 2 ^ (prefixWord ++ tailWord_174294).sum := by decide
  have hdescent : baseEnd_174294 < baseStart_174294 := by decide
  rcases family_descends (prefixWord ++ tailWord_174294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174307 : List Nat := [1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 4]
def baseStart_174307 : Nat := 118140960795 + 174307 * 2 ^ 59
def prefixEnd_174307 : Nat := 4983230072969 + 3 ^ 40 * 174307 * 2
def baseEnd_174307 : Nat := 89503272443354756760883

theorem tailTrace_174307 : CollatzResearch.WordTrace tailWord_174307 prefixEnd_174307 89503272443354756760883 := by
  unfold tailWord_174307
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357498579522983110657175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4238332386348655407104783 6357498579522983110657175)
  ·
    refine ⟨9536247869284474665985763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6357498579522983110657175 9536247869284474665985763)
    ·
      refine ⟨14304371803926711998978645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9536247869284474665985763 14304371803926711998978645)
      ·
        refine ⟨167629357077266156238031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 14304371803926711998978645 167629357077266156238031)
        ·
          refine ⟨251444035615899234357047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167629357077266156238031 251444035615899234357047)
          ·
            refine ⟨377166053423848851535571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251444035615899234357047 377166053423848851535571)
            ·
              refine ⟨565749080135773277303357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377166053423848851535571 565749080135773277303357)
              ·
                refine ⟨212155905050914978988759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565749080135773277303357 212155905050914978988759)
                ·
                  refine ⟨318233857576372468483139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212155905050914978988759 318233857576372468483139)
                  ·
                    refine ⟨477350786364558702724709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 318233857576372468483139 477350786364558702724709)
                    ·
                      refine ⟨89503272443354756760883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 477350786364558702724709 89503272443354756760883)
                      ·
                        rfl

theorem cell23_174307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_174307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174307 prefixEnd_174307 := by exact prefixLift 174307
  have htrace : WordTrace (prefixWord ++ tailWord_174307) baseStart_174307 baseEnd_174307 := by
    simpa [prefixWord, tailWord_174307, baseEnd_174307] using wordTrace_append hprefix tailTrace_174307
  have hstable : (prefixWord ++ tailWord_174307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174307).length < 2 ^ (prefixWord ++ tailWord_174307).sum := by decide
  have hdescent : baseEnd_174307 < baseStart_174307 := by decide
  rcases family_descends (prefixWord ++ tailWord_174307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174367 : List Nat := [1, 1, 2, 4, 3, 1, 2, 3, 1, 3, 2]
def baseStart_174367 : Nat := 118140960795 + 174367 * 2 ^ 59
def prefixEnd_174367 : Nat := 4983230072969 + 3 ^ 40 * 174367 * 2
def baseEnd_174367 : Nat := 89534081282624522010607

theorem tailTrace_174367 : CollatzResearch.WordTrace tailWord_174367 prefixEnd_174367 89534081282624522010607 := by
  unfold tailWord_174367
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359686959305613357841355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239791306203742238560903 6359686959305613357841355)
  ·
    refine ⟨9539530438958420036762033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359686959305613357841355 9539530438958420036762033)
    ·
      refine ⟨7154647829218815027571525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9539530438958420036762033 7154647829218815027571525)
      ·
        refine ⟨1341496467978527817669661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7154647829218815027571525 1341496467978527817669661)
        ·
          refine ⟨503061175491947931626123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1341496467978527817669661 503061175491947931626123)
          ·
            refine ⟨754591763237921897439185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503061175491947931626123 754591763237921897439185)
            ·
              refine ⟨565943822428441423079389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754591763237921897439185 565943822428441423079389)
              ·
                refine ⟨212228933410665533654771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565943822428441423079389 212228933410665533654771)
                ·
                  refine ⟨318343400115998300482157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212228933410665533654771 318343400115998300482157)
                  ·
                    refine ⟨119378775043499362680809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318343400115998300482157 119378775043499362680809)
                    ·
                      refine ⟨89534081282624522010607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119378775043499362680809 89534081282624522010607)
                      ·
                        rfl

theorem cell23_174367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_174367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174367 prefixEnd_174367 := by exact prefixLift 174367
  have htrace : WordTrace (prefixWord ++ tailWord_174367) baseStart_174367 baseEnd_174367 := by
    simpa [prefixWord, tailWord_174367, baseEnd_174367] using wordTrace_append hprefix tailTrace_174367
  have hstable : (prefixWord ++ tailWord_174367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174367).length < 2 ^ (prefixWord ++ tailWord_174367).sum := by decide
  have hdescent : baseEnd_174367 < baseStart_174367 := by decide
  rcases family_descends (prefixWord ++ tailWord_174367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174375 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 3, 2, 2]
def baseStart_174375 : Nat := 118140960795 + 174375 * 2 ^ 59
def prefixEnd_174375 : Nat := 4983230072969 + 3 ^ 40 * 174375 * 2
def baseEnd_174375 : Nat := 89538189127860490710571

theorem tailTrace_174375 : CollatzResearch.WordTrace tailWord_174375 prefixEnd_174375 89538189127860490710571 := by
  unfold tailWord_174375
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359978743276630724132579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4239985828851087149421719 6359978743276630724132579)
  ·
    refine ⟨9539968114914946086198869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359978743276630724132579 9539968114914946086198869)
    ·
      refine ⟨111796501346659524447643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 9539968114914946086198869 111796501346659524447643)
      ·
        refine ⟨167694752019989286671465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111796501346659524447643 167694752019989286671465)
        ·
          refine ⟨125771064014991965003599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167694752019989286671465 125771064014991965003599)
          ·
            refine ⟨188656596022487947505399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125771064014991965003599 188656596022487947505399)
            ·
              refine ⟨282984894033731921258099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188656596022487947505399 282984894033731921258099)
              ·
                refine ⟨424477341050597881887149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282984894033731921258099 424477341050597881887149)
                ·
                  refine ⟨159179002893974205707681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424477341050597881887149 159179002893974205707681)
                  ·
                    refine ⟨119384252170480654280761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159179002893974205707681 119384252170480654280761)
                    ·
                      refine ⟨89538189127860490710571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119384252170480654280761 89538189127860490710571)
                      ·
                        rfl

theorem cell23_174375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_174375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174375 prefixEnd_174375 := by exact prefixLift 174375
  have htrace : WordTrace (prefixWord ++ tailWord_174375) baseStart_174375 baseEnd_174375 := by
    simpa [prefixWord, tailWord_174375, baseEnd_174375] using wordTrace_append hprefix tailTrace_174375
  have hstable : (prefixWord ++ tailWord_174375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174375).length < 2 ^ (prefixWord ++ tailWord_174375).sum := by decide
  have hdescent : baseEnd_174375 < baseStart_174375 := by decide
  rcases family_descends (prefixWord ++ tailWord_174375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174401 : List Nat := [1, 2, 5, 2, 2, 2, 1, 2, 1, 3, 2]
def baseStart_174401 : Nat := 118140960795 + 174401 * 2 ^ 59
def prefixEnd_174401 : Nat := 4983230072969 + 3 ^ 40 * 174401 * 2
def baseEnd_174401 : Nat := 89551539624877388985451

theorem tailTrace_174401 : CollatzResearch.WordTrace tailWord_174401 prefixEnd_174401 89551539624877388985451 := by
  unfold tailWord_174401
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360927041182437164579057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4240618027454958109719371 6360927041182437164579057)
  ·
    refine ⟨4770695280886827873434293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6360927041182437164579057 4770695280886827873434293)
    ·
      refine ⟨447252682583140113134465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4770695280886827873434293 447252682583140113134465)
      ·
        refine ⟨335439511937355084850849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447252682583140113134465 335439511937355084850849)
        ·
          refine ⟨251579633953016313638137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335439511937355084850849 251579633953016313638137)
          ·
            refine ⟨188684725464762235228603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251579633953016313638137 188684725464762235228603)
            ·
              refine ⟨283027088197143352842905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188684725464762235228603 283027088197143352842905)
              ·
                refine ⟨212270316147857514632179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283027088197143352842905 212270316147857514632179)
                ·
                  refine ⟨318405474221786271948269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212270316147857514632179 318405474221786271948269)
                  ·
                    refine ⟨119402052833169851980601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 318405474221786271948269 119402052833169851980601)
                    ·
                      refine ⟨89551539624877388985451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119402052833169851980601 89551539624877388985451)
                      ·
                        rfl

theorem cell23_174401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_174401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174401 prefixEnd_174401 := by exact prefixLift 174401
  have htrace : WordTrace (prefixWord ++ tailWord_174401) baseStart_174401 baseEnd_174401 := by
    simpa [prefixWord, tailWord_174401, baseEnd_174401] using wordTrace_append hprefix tailTrace_174401
  have hstable : (prefixWord ++ tailWord_174401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174401).length < 2 ^ (prefixWord ++ tailWord_174401).sum := by decide
  have hdescent : baseEnd_174401 < baseStart_174401 := by decide
  rcases family_descends (prefixWord ++ tailWord_174401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174437 : List Nat := [1, 3, 1, 3, 1, 3, 4, 2, 5]
def baseStart_174437 : Nat := 118140960795 + 174437 * 2 ^ 59
def prefixEnd_174437 : Nat := 4983230072969 + 3 ^ 40 * 174437 * 2
def baseEnd_174437 : Nat := 9952224992048805348365

theorem tailTrace_174437 : CollatzResearch.WordTrace tailWord_174437 prefixEnd_174437 9952224992048805348365 := by
  unfold tailWord_174437
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362240069052015312889565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4241493379368010208593043 6362240069052015312889565)
  ·
    refine ⟨2385840025894505742333587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6362240069052015312889565 2385840025894505742333587)
    ·
      refine ⟨3578760038841758613500381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385840025894505742333587 3578760038841758613500381)
      ·
        refine ⟨1342035014565659480062643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3578760038841758613500381 1342035014565659480062643)
        ·
          refine ⟨2013052521848489220093965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342035014565659480062643 2013052521848489220093965)
          ·
            refine ⟨754894695693183457535237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2013052521848489220093965 754894695693183457535237)
            ·
              refine ⟨141542755442471898287857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 754894695693183457535237 141542755442471898287857)
              ·
                refine ⟨106157066581853923715893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141542755442471898287857 106157066581853923715893)
                ·
                  refine ⟨9952224992048805348365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106157066581853923715893 9952224992048805348365)
                  ·
                    rfl

theorem cell23_174437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 2, 5].length) (baseStart_174437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174437 prefixEnd_174437 := by exact prefixLift 174437
  have htrace : WordTrace (prefixWord ++ tailWord_174437) baseStart_174437 baseEnd_174437 := by
    simpa [prefixWord, tailWord_174437, baseEnd_174437] using wordTrace_append hprefix tailTrace_174437
  have hstable : (prefixWord ++ tailWord_174437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174437).length < 2 ^ (prefixWord ++ tailWord_174437).sum := by decide
  have hdescent : baseEnd_174437 < baseStart_174437 := by decide
  rcases family_descends (prefixWord ++ tailWord_174437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174467 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 2, 5]
def baseStart_174467 : Nat := 118140960795 + 174467 * 2 ^ 59
def prefixEnd_174467 : Nat := 4983230072969 + 3 ^ 40 * 174467 * 2
def baseEnd_174467 : Nat := 29861809782691376920049

theorem tailTrace_174467 : CollatzResearch.WordTrace tailWord_174467 prefixEnd_174467 29861809782691376920049 := by
  unfold tailWord_174467
  simp only [CollatzResearch.WordTrace]
  refine ⟨6363334258943330436481655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4242222839295553624321103 6363334258943330436481655)
  ·
    refine ⟨9545001388414995654722483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6363334258943330436481655 9545001388414995654722483)
    ·
      refine ⟨14317502082622493482083725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9545001388414995654722483 14317502082622493482083725)
      ·
        refine ⟨5369063280983435055781397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14317502082622493482083725 5369063280983435055781397)
        ·
          refine ⟨251674841296098518239753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5369063280983435055781397 251674841296098518239753)
          ·
            refine ⟨188756130972073888679815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251674841296098518239753 188756130972073888679815)
            ·
              refine ⟨283134196458110833019723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188756130972073888679815 283134196458110833019723)
              ·
                refine ⟨424701294687166249529585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283134196458110833019723 424701294687166249529585)
                ·
                  refine ⟨318525971015374687147189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424701294687166249529585 318525971015374687147189)
                  ·
                    refine ⟨29861809782691376920049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 318525971015374687147189 29861809782691376920049)
                    ·
                      rfl

theorem cell23_174467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 5].length) (baseStart_174467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174467 prefixEnd_174467 := by exact prefixLift 174467
  have htrace : WordTrace (prefixWord ++ tailWord_174467) baseStart_174467 baseEnd_174467 := by
    simpa [prefixWord, tailWord_174467, baseEnd_174467] using wordTrace_append hprefix tailTrace_174467
  have hstable : (prefixWord ++ tailWord_174467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174467).length < 2 ^ (prefixWord ++ tailWord_174467).sum := by decide
  have hdescent : baseEnd_174467 < baseStart_174467 := by decide
  rcases family_descends (prefixWord ++ tailWord_174467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174504 : List Nat := [2, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_174504 : Nat := 118140960795 + 174504 * 2 ^ 59
def prefixEnd_174504 : Nat := 4983230072969 + 3 ^ 40 * 174504 * 2
def baseEnd_174504 : Nat := 89604428132290485997477

theorem tailTrace_174504 : CollatzResearch.WordTrace tailWord_174504 prefixEnd_174504 89604428132290485997477 := by
  unfold tailWord_174504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182341879904642877789283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4243122506539523837052377 3182341879904642877789283)
  ·
    refine ⟨4773512819856964316683925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3182341879904642877789283 4773512819856964316683925)
    ·
      refine ⟨223758413430795202344559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4773512819856964316683925 223758413430795202344559)
      ·
        refine ⟨335637620146192803516839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223758413430795202344559 335637620146192803516839)
        ·
          refine ⟨503456430219289205275259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335637620146192803516839 503456430219289205275259)
          ·
            refine ⟨755184645328933807912889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503456430219289205275259 755184645328933807912889)
            ·
              refine ⟨566388483996700355934667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755184645328933807912889 566388483996700355934667)
              ·
                refine ⟨849582725995050533902001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566388483996700355934667 849582725995050533902001)
                ·
                  refine ⟨637187044496287900426501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849582725995050533902001 637187044496287900426501)
                  ·
                    refine ⟨119472570843053981329969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637187044496287900426501 119472570843053981329969)
                    ·
                      refine ⟨89604428132290485997477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119472570843053981329969 89604428132290485997477)
                      ·
                        rfl

theorem cell23_174504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_174504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174504 prefixEnd_174504 := by exact prefixLift 174504
  have htrace : WordTrace (prefixWord ++ tailWord_174504) baseStart_174504 baseEnd_174504 := by
    simpa [prefixWord, tailWord_174504, baseEnd_174504] using wordTrace_append hprefix tailTrace_174504
  have hstable : (prefixWord ++ tailWord_174504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174504).length < 2 ^ (prefixWord ++ tailWord_174504).sum := by decide
  have hdescent : baseEnd_174504 < baseStart_174504 := by decide
  rcases family_descends (prefixWord ++ tailWord_174504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174560 : List Nat := [2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_174560 : Nat := 118140960795 + 174560 * 2 ^ 59
def prefixEnd_174560 : Nat := 4983230072969 + 3 ^ 40 * 174560 * 2
def baseEnd_174560 : Nat := 89633183048942266897219

theorem tailTrace_174560 : CollatzResearch.WordTrace tailWord_174560 prefixEnd_174560 89633183048942266897219 := by
  unfold tailWord_174560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3183363123803203659808567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4244484165070938213078089 3183363123803203659808567)
  ·
    refine ⟨4775044685704805489712851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3183363123803203659808567 4775044685704805489712851)
    ·
      refine ⟨7162567028557208234569277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4775044685704805489712851 7162567028557208234569277)
      ·
        refine ⟨2685962635708953087963479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7162567028557208234569277 2685962635708953087963479)
        ·
          refine ⟨4028943953563429631945219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2685962635708953087963479 4028943953563429631945219)
          ·
            refine ⟨6043415930345144447917829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4028943953563429631945219 6043415930345144447917829)
            ·
              refine ⟨1133140486939714583984593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6043415930345144447917829 1133140486939714583984593)
              ·
                refine ⟨849855365204785937988445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133140486939714583984593 849855365204785937988445)
                ·
                  refine ⟨318695761951794726745667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 849855365204785937988445 318695761951794726745667)
                  ·
                    refine ⟨478043642927692090118501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 318695761951794726745667 478043642927692090118501)
                    ·
                      refine ⟨89633183048942266897219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 478043642927692090118501 89633183048942266897219)
                      ·
                        rfl

theorem cell23_174560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_174560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174560 prefixEnd_174560 := by exact prefixLift 174560
  have htrace : WordTrace (prefixWord ++ tailWord_174560) baseStart_174560 baseEnd_174560 := by
    simpa [prefixWord, tailWord_174560, baseEnd_174560] using wordTrace_append hprefix tailTrace_174560
  have hstable : (prefixWord ++ tailWord_174560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174560).length < 2 ^ (prefixWord ++ tailWord_174560).sum := by decide
  have hdescent : baseEnd_174560 < baseStart_174560 := by decide
  rcases family_descends (prefixWord ++ tailWord_174560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174574 : List Nat := [4, 1, 2, 1, 2, 4, 1, 2, 1, 5]
def baseStart_174574 : Nat := 118140960795 + 174574 * 2 ^ 59
def prefixEnd_174574 : Nat := 4983230072969 + 3 ^ 40 * 174574 * 2
def baseEnd_174574 : Nat := 29880123926035070707385

theorem tailTrace_174574 : CollatzResearch.WordTrace tailWord_174574 prefixEnd_174574 29880123926035070707385 := by
  unfold tailWord_174574
  simp only [CollatzResearch.WordTrace]
  refine ⟨795904608694460963828347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4244824579703791807084517 795904608694460963828347)
  ·
    refine ⟨1193856913041691445742521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 795904608694460963828347 1193856913041691445742521)
    ·
      refine ⟨895392684781268584306891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1193856913041691445742521 895392684781268584306891)
      ·
        refine ⟨1343089027171902876460337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895392684781268584306891 1343089027171902876460337)
        ·
          refine ⟨1007316770378927157345253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343089027171902876460337 1007316770378927157345253)
          ·
            refine ⟨188871894446048842002235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1007316770378927157345253 188871894446048842002235)
            ·
              refine ⟨283307841669073263003353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188871894446048842002235 283307841669073263003353)
              ·
                refine ⟨212480881251804947252515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283307841669073263003353 212480881251804947252515)
                ·
                  refine ⟨318721321877707420878773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212480881251804947252515 318721321877707420878773)
                  ·
                    refine ⟨29880123926035070707385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 318721321877707420878773 29880123926035070707385)
                    ·
                      rfl

theorem cell23_174574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_174574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174574 prefixEnd_174574 := by exact prefixLift 174574
  have htrace : WordTrace (prefixWord ++ tailWord_174574) baseStart_174574 baseEnd_174574 := by
    simpa [prefixWord, tailWord_174574, baseEnd_174574] using wordTrace_append hprefix tailTrace_174574
  have hstable : (prefixWord ++ tailWord_174574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174574).length < 2 ^ (prefixWord ++ tailWord_174574).sum := by decide
  have hdescent : baseEnd_174574 < baseStart_174574 := by decide
  rcases family_descends (prefixWord ++ tailWord_174574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174597 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 3]
def baseStart_174597 : Nat := 118140960795 + 174597 * 2 ^ 59
def prefixEnd_174597 : Nat := 4983230072969 + 3 ^ 40 * 174597 * 2
def baseEnd_174597 : Nat := 89652181833158622134549

theorem tailTrace_174597 : CollatzResearch.WordTrace tailWord_174597 prefixEnd_174597 89652181833158622134549 := by
  unfold tailWord_174597
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368075748472362638714045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4245383832314908425809363 6368075748472362638714045)
  ·
    refine ⟨2388028405677135989517767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6368075748472362638714045 2388028405677135989517767)
    ·
      refine ⟨3582042608515703984276651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388028405677135989517767 3582042608515703984276651)
      ·
        refine ⟨5373063912773555976414977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582042608515703984276651 5373063912773555976414977)
        ·
          refine ⟨4029797934580166982311233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5373063912773555976414977 4029797934580166982311233)
          ·
            refine ⟨3022348450935125236733425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4029797934580166982311233 3022348450935125236733425)
            ·
              refine ⟨2266761338201343927550069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3022348450935125236733425 2266761338201343927550069)
              ·
                refine ⟨212508875456375993207819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2266761338201343927550069 212508875456375993207819)
                ·
                  refine ⟨318763313184563989811729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212508875456375993207819 318763313184563989811729)
                  ·
                    refine ⟨239072484888422992358797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318763313184563989811729 239072484888422992358797)
                    ·
                      refine ⟨89652181833158622134549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239072484888422992358797 89652181833158622134549)
                      ·
                        rfl

theorem cell23_174597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 2, 3].length) (baseStart_174597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174597 prefixEnd_174597 := by exact prefixLift 174597
  have htrace : WordTrace (prefixWord ++ tailWord_174597) baseStart_174597 baseEnd_174597 := by
    simpa [prefixWord, tailWord_174597, baseEnd_174597] using wordTrace_append hprefix tailTrace_174597
  have hstable : (prefixWord ++ tailWord_174597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174597).length < 2 ^ (prefixWord ++ tailWord_174597).sum := by decide
  have hdescent : baseEnd_174597 < baseStart_174597 := by decide
  rcases family_descends (prefixWord ++ tailWord_174597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174604 : List Nat := [2, 2, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_174604 : Nat := 118140960795 + 174604 * 2 ^ 59
def prefixEnd_174604 : Nat := 4983230072969 + 3 ^ 40 * 174604 * 2
def baseEnd_174604 : Nat := 29885258732580031582339

theorem tailTrace_174604 : CollatzResearch.WordTrace tailWord_174604 prefixEnd_174604 29885258732580031582339 := by
  unfold tailWord_174604
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184165529723501417109433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4245554039631335222812577 3184165529723501417109433)
  ·
    refine ⟨2388124147292626062832075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3184165529723501417109433 2388124147292626062832075)
    ·
      refine ⟨3582186220938939094248113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388124147292626062832075 3582186220938939094248113)
      ·
        refine ⟨2686639665704204320686085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3582186220938939094248113 2686639665704204320686085)
        ·
          refine ⟨503744937319538310128641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2686639665704204320686085 503744937319538310128641)
          ·
            refine ⟨377808702989653732596481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503744937319538310128641 377808702989653732596481)
            ·
              refine ⟨283356527242240299447361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377808702989653732596481 283356527242240299447361)
              ·
                refine ⟨212517395431680224585521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283356527242240299447361 212517395431680224585521)
                ·
                  refine ⟨159388046573760168439141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212517395431680224585521 159388046573760168439141)
                  ·
                    refine ⟨29885258732580031582339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159388046573760168439141 29885258732580031582339)
                    ·
                      rfl

theorem cell23_174604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_174604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174604 prefixEnd_174604 := by exact prefixLift 174604
  have htrace : WordTrace (prefixWord ++ tailWord_174604) baseStart_174604 baseEnd_174604 := by
    simpa [prefixWord, tailWord_174604, baseEnd_174604] using wordTrace_append hprefix tailTrace_174604
  have hstable : (prefixWord ++ tailWord_174604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174604).length < 2 ^ (prefixWord ++ tailWord_174604).sum := by decide
  have hdescent : baseEnd_174604 < baseStart_174604 := by decide
  rcases family_descends (prefixWord ++ tailWord_174604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174605 : List Nat := [1, 7, 1, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_174605 : Nat := 118140960795 + 174605 * 2 ^ 59
def prefixEnd_174605 : Nat := 4983230072969 + 3 ^ 40 * 174605 * 2
def baseEnd_174605 : Nat := 89656289678394590834513

theorem tailTrace_174605 : CollatzResearch.WordTrace tailWord_174605 prefixEnd_174605 89656289678394590834513 := by
  unfold tailWord_174605
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368367532443380005005269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4245578354962253336670179 6368367532443380005005269)
  ·
    refine ⟨149258614041641718867311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6368367532443380005005269 149258614041641718867311)
    ·
      refine ⟨223887921062462578300967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149258614041641718867311 223887921062462578300967)
      ·
        refine ⟨335831881593693867451451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223887921062462578300967 335831881593693867451451)
        ·
          refine ⟨503747822390540801177177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335831881593693867451451 503747822390540801177177)
          ·
            refine ⟨377810866792905600882883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503747822390540801177177 377810866792905600882883)
            ·
              refine ⟨566716300189358401324325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377810866792905600882883 566716300189358401324325)
              ·
                refine ⟨106259306285504700248311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566716300189358401324325 106259306285504700248311)
                ·
                  refine ⟨159388959428257050372467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106259306285504700248311 159388959428257050372467)
                  ·
                    refine ⟨239083439142385575558701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159388959428257050372467 239083439142385575558701)
                    ·
                      refine ⟨89656289678394590834513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239083439142385575558701 89656289678394590834513)
                      ·
                        rfl

theorem cell23_174605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_174605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174605 prefixEnd_174605 := by exact prefixLift 174605
  have htrace : WordTrace (prefixWord ++ tailWord_174605) baseStart_174605 baseEnd_174605 := by
    simpa [prefixWord, tailWord_174605, baseEnd_174605] using wordTrace_append hprefix tailTrace_174605
  have hstable : (prefixWord ++ tailWord_174605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174605).length < 2 ^ (prefixWord ++ tailWord_174605).sum := by decide
  have hdescent : baseEnd_174605 < baseStart_174605 := by decide
  rcases family_descends (prefixWord ++ tailWord_174605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174611 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 1, 2, 2]
def baseStart_174611 : Nat := 118140960795 + 174611 * 2 ^ 59
def prefixEnd_174611 : Nat := 4983230072969 + 3 ^ 40 * 174611 * 2
def baseEnd_174611 : Nat := 89659370562321567359485

theorem tailTrace_174611 : CollatzResearch.WordTrace tailWord_174611 prefixEnd_174611 89659370562321567359485 := by
  unfold tailWord_174611
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368586370421643029723687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4245724246947762019815791 6368586370421643029723687)
  ·
    refine ⟨9552879555632464544585531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6368586370421643029723687 9552879555632464544585531)
    ·
      refine ⟨14329319333448696816878297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9552879555632464544585531 14329319333448696816878297)
      ·
        refine ⟨10746989500086522612658723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14329319333448696816878297 10746989500086522612658723)
        ·
          refine ⟨16120484250129783918988085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10746989500086522612658723 16120484250129783918988085)
          ·
            refine ⟨1511295398449667242405133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16120484250129783918988085 1511295398449667242405133)
            ·
              refine ⟨566735774418625215901925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1511295398449667242405133 566735774418625215901925)
              ·
                refine ⟨106262957703492227981611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 566735774418625215901925 106262957703492227981611)
                ·
                  refine ⟨159394436555238341972417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106262957703492227981611 159394436555238341972417)
                  ·
                    refine ⟨119545827416428756479313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159394436555238341972417 119545827416428756479313)
                    ·
                      refine ⟨89659370562321567359485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119545827416428756479313 89659370562321567359485)
                      ·
                        rfl

theorem cell23_174611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 1, 2, 2].length) (baseStart_174611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174611 prefixEnd_174611 := by exact prefixLift 174611
  have htrace : WordTrace (prefixWord ++ tailWord_174611) baseStart_174611 baseEnd_174611 := by
    simpa [prefixWord, tailWord_174611, baseEnd_174611] using wordTrace_append hprefix tailTrace_174611
  have hstable : (prefixWord ++ tailWord_174611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174611).length < 2 ^ (prefixWord ++ tailWord_174611).sum := by decide
  have hdescent : baseEnd_174611 < baseStart_174611 := by decide
  rcases family_descends (prefixWord ++ tailWord_174611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174624 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_174624 : Nat := 118140960795 + 174624 * 2 ^ 59
def prefixEnd_174624 : Nat := 4983230072969 + 3 ^ 40 * 174624 * 2
def baseEnd_174624 : Nat := 89666045810830016496925

theorem tailTrace_174624 : CollatzResearch.WordTrace tailWord_174624 prefixEnd_174624 89666045810830016496925 := by
  unfold tailWord_174624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184530259687273124973463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4246040346249697499964617 3184530259687273124973463)
  ·
    refine ⟨4776795389530909687460195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184530259687273124973463 4776795389530909687460195)
    ·
      refine ⟨7165193084296364531190293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776795389530909687460195 7165193084296364531190293)
      ·
        refine ⟨335868425826392087399545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7165193084296364531190293 335868425826392087399545)
        ·
          refine ⟨251901319369794065549659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335868425826392087399545 251901319369794065549659)
          ·
            refine ⟨377851979054691098324489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251901319369794065549659 377851979054691098324489)
            ·
              refine ⟨283388984291018323743367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377851979054691098324489 283388984291018323743367)
              ·
                refine ⟨425083476436527485615051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283388984291018323743367 425083476436527485615051)
                ·
                  refine ⟨637625214654791228422577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425083476436527485615051 637625214654791228422577)
                  ·
                    refine ⟨478218910991093421316933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637625214654791228422577 478218910991093421316933)
                    ·
                      refine ⟨89666045810830016496925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 478218910991093421316933 89666045810830016496925)
                      ·
                        rfl

theorem cell23_174624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_174624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174624 prefixEnd_174624 := by exact prefixLift 174624
  have htrace : WordTrace (prefixWord ++ tailWord_174624) baseStart_174624 baseEnd_174624 := by
    simpa [prefixWord, tailWord_174624, baseEnd_174624] using wordTrace_append hprefix tailTrace_174624
  have hstable : (prefixWord ++ tailWord_174624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174624).length < 2 ^ (prefixWord ++ tailWord_174624).sum := by decide
  have hdescent : baseEnd_174624 < baseStart_174624 := by decide
  rcases family_descends (prefixWord ++ tailWord_174624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174627 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3]
def baseStart_174627 : Nat := 118140960795 + 174627 * 2 ^ 59
def prefixEnd_174627 : Nat := 4983230072969 + 3 ^ 40 * 174627 * 2
def baseEnd_174627 : Nat := 89667586252793504759411

theorem tailTrace_174627 : CollatzResearch.WordTrace tailWord_174627 prefixEnd_174627 89667586252793504759411 := by
  unfold tailWord_174627
  simp only [CollatzResearch.WordTrace]
  refine ⟨6369169938363677762306135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4246113292242451841537423 6369169938363677762306135)
  ·
    refine ⟨9553754907545516643459203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6369169938363677762306135 9553754907545516643459203)
    ·
      refine ⟨14330632361318274965188805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9553754907545516643459203 14330632361318274965188805)
      ·
        refine ⟨2686993567747176555972901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14330632361318274965188805 2686993567747176555972901)
        ·
          refine ⟨503811293952595604244919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2686993567747176555972901 503811293952595604244919)
          ·
            refine ⟨755716940928893406367379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503811293952595604244919 755716940928893406367379)
            ·
              refine ⟨1133575411393340109551069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755716940928893406367379 1133575411393340109551069)
              ·
                refine ⟨425090779272502541081651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133575411393340109551069 425090779272502541081651)
                ·
                  refine ⟨637636168908753811622477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425090779272502541081651 637636168908753811622477)
                  ·
                    refine ⟨239113563340782679358429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 637636168908753811622477 239113563340782679358429)
                    ·
                      refine ⟨89667586252793504759411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239113563340782679358429 89667586252793504759411)
                      ·
                        rfl

theorem cell23_174627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_174627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174627 prefixEnd_174627 := by exact prefixLift 174627
  have htrace : WordTrace (prefixWord ++ tailWord_174627) baseStart_174627 baseEnd_174627 := by
    simpa [prefixWord, tailWord_174627, baseEnd_174627] using wordTrace_append hprefix tailTrace_174627
  have hstable : (prefixWord ++ tailWord_174627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174627).length < 2 ^ (prefixWord ++ tailWord_174627).sum := by decide
  have hdescent : baseEnd_174627 < baseStart_174627 := by decide
  rcases family_descends (prefixWord ++ tailWord_174627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174628 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_174628 : Nat := 118140960795 + 174628 * 2 ^ 59
def prefixEnd_174628 : Nat := 4983230072969 + 3 ^ 40 * 174628 * 2
def baseEnd_174628 : Nat := 89668099733448000846907

theorem tailTrace_174628 : CollatzResearch.WordTrace tailWord_174628 prefixEnd_174628 89668099733448000846907 := by
  unfold tailWord_174628
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184603205680027466546269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4246137607573369955395025 3184603205680027466546269)
  ·
    refine ⟨1194226202130010299954851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3184603205680027466546269 1194226202130010299954851)
    ·
      refine ⟨1791339303195015449932277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194226202130010299954851 1791339303195015449932277)
      ·
        refine ⟨167938059674532698431151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1791339303195015449932277 167938059674532698431151)
        ·
          refine ⟨251907089511799047646727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167938059674532698431151 251907089511799047646727)
          ·
            refine ⟨377860634267698571470091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251907089511799047646727 377860634267698571470091)
            ·
              refine ⟨566790951401547857205137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377860634267698571470091 566790951401547857205137)
              ·
                refine ⟨425093213551160892903853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566790951401547857205137 425093213551160892903853)
                ·
                  refine ⟨159409955081685334838945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425093213551160892903853 159409955081685334838945)
                  ·
                    refine ⟨119557466311264001129209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159409955081685334838945 119557466311264001129209)
                    ·
                      refine ⟨89668099733448000846907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119557466311264001129209 89668099733448000846907)
                      ·
                        rfl

theorem cell23_174628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_174628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174628 prefixEnd_174628 := by exact prefixLift 174628
  have htrace : WordTrace (prefixWord ++ tailWord_174628) baseStart_174628 baseEnd_174628 := by
    simpa [prefixWord, tailWord_174628, baseEnd_174628] using wordTrace_append hprefix tailTrace_174628
  have hstable : (prefixWord ++ tailWord_174628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174628).length < 2 ^ (prefixWord ++ tailWord_174628).sum := by decide
  have hdescent : baseEnd_174628 < baseStart_174628 := by decide
  rcases family_descends (prefixWord ++ tailWord_174628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174661 : List Nat := [1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 3]
def baseStart_174661 : Nat := 118140960795 + 174661 * 2 ^ 59
def prefixEnd_174661 : Nat := 4983230072969 + 3 ^ 40 * 174661 * 2
def baseEnd_174661 : Nat := 89685044595046371734255

theorem tailTrace_174661 : CollatzResearch.WordTrace tailWord_174661 prefixEnd_174661 89685044595046371734255 := by
  unfold tailWord_174661
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370410020240501569043837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4246940013493667712695891 6370410020240501569043837)
  ·
    refine ⟨2388903757590188088391439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6370410020240501569043837 2388903757590188088391439)
    ·
      refine ⟨3583355636385282132587159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2388903757590188088391439 3583355636385282132587159)
      ·
        refine ⟨5375033454577923198880739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3583355636385282132587159 5375033454577923198880739)
        ·
          refine ⟨8062550181866884798321109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5375033454577923198880739 8062550181866884798321109)
          ·
            refine ⟨188966019887505112460651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 8062550181866884798321109 188966019887505112460651)
            ·
              refine ⟨283449029831257668690977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188966019887505112460651 283449029831257668690977)
              ·
                refine ⟨212586772373443251518233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283449029831257668690977 212586772373443251518233)
                ·
                  refine ⟨159440079280082438638675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212586772373443251518233 159440079280082438638675)
                  ·
                    refine ⟨239160118920123657958013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159440079280082438638675 239160118920123657958013)
                    ·
                      refine ⟨89685044595046371734255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239160118920123657958013 89685044595046371734255)
                      ·
                        rfl

theorem cell23_174661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 3].length) (baseStart_174661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174661 prefixEnd_174661 := by exact prefixLift 174661
  have htrace : WordTrace (prefixWord ++ tailWord_174661) baseStart_174661 baseEnd_174661 := by
    simpa [prefixWord, tailWord_174661, baseEnd_174661] using wordTrace_append hprefix tailTrace_174661
  have hstable : (prefixWord ++ tailWord_174661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174661).length < 2 ^ (prefixWord ++ tailWord_174661).sum := by decide
  have hdescent : baseEnd_174661 < baseStart_174661 := by decide
  rcases family_descends (prefixWord ++ tailWord_174661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174667 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 3, 4, 2]
def baseStart_174667 : Nat := 118140960795 + 174667 * 2 ^ 59
def prefixEnd_174667 : Nat := 4983230072969 + 3 ^ 40 * 174667 * 2
def baseEnd_174667 : Nat := 89688125478973348259227

theorem tailTrace_174667 : CollatzResearch.WordTrace tailWord_174667 prefixEnd_174667 89688125478973348259227 := by
  unfold tailWord_174667
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370628858218764593762255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4247085905479176395841503 6370628858218764593762255)
  ·
    refine ⟨9555943287328146890643383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370628858218764593762255 9555943287328146890643383)
    ·
      refine ⟨14333914930992220335965075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555943287328146890643383 14333914930992220335965075)
      ·
        refine ⟨21500872396488330503947613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14333914930992220335965075 21500872396488330503947613)
        ·
          refine ⟨8062827148683123938980355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21500872396488330503947613 8062827148683123938980355)
          ·
            refine ⟨12094240723024685908470533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8062827148683123938980355 12094240723024685908470533)
            ·
              refine ⟨2267670135567128607838225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12094240723024685908470533 2267670135567128607838225)
              ·
                refine ⟨1700752601675346455878669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2267670135567128607838225 1700752601675346455878669)
                ·
                  refine ⟨637782225628254920954501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1700752601675346455878669 637782225628254920954501)
                  ·
                    refine ⟨119584167305297797678969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 637782225628254920954501 119584167305297797678969)
                    ·
                      refine ⟨89688125478973348259227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119584167305297797678969 89688125478973348259227)
                      ·
                        rfl

theorem cell23_174667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 4, 2].length) (baseStart_174667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174667 prefixEnd_174667 := by exact prefixLift 174667
  have htrace : WordTrace (prefixWord ++ tailWord_174667) baseStart_174667 baseEnd_174667 := by
    simpa [prefixWord, tailWord_174667, baseEnd_174667] using wordTrace_append hprefix tailTrace_174667
  have hstable : (prefixWord ++ tailWord_174667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174667).length < 2 ^ (prefixWord ++ tailWord_174667).sum := by decide
  have hdescent : baseEnd_174667 < baseStart_174667 := by decide
  rcases family_descends (prefixWord ++ tailWord_174667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174701 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_174701 : Nat := 118140960795 + 174701 * 2 ^ 59
def prefixEnd_174701 : Nat := 4983230072969 + 3 ^ 40 * 174701 * 2
def baseEnd_174701 : Nat := 89705583821226215234071

theorem tailTrace_174701 : CollatzResearch.WordTrace tailWord_174701 prefixEnd_174701 89705583821226215234071 := by
  unfold tailWord_174701
  simp only [CollatzResearch.WordTrace]
  refine ⟨6371868940095588400499957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4247912626730392266999971 6371868940095588400499957)
  ·
    refine ⟨597362713133961412546871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6371868940095588400499957 597362713133961412546871)
    ·
      refine ⟨896044069700942118820307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597362713133961412546871 896044069700942118820307)
      ·
        refine ⟨1344066104551413178230461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896044069700942118820307 1344066104551413178230461)
        ·
          refine ⟨504024789206779941836423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1344066104551413178230461 504024789206779941836423)
          ·
            refine ⟨756037183810169912754635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504024789206779941836423 756037183810169912754635)
            ·
              refine ⟨1134055775715254869131953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756037183810169912754635 1134055775715254869131953)
              ·
                refine ⟨850541831786441151848965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134055775715254869131953 850541831786441151848965)
                ·
                  refine ⟨159476593459957715971681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850541831786441151848965 159476593459957715971681)
                  ·
                    refine ⟨119607445094968286978761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159476593459957715971681 119607445094968286978761)
                    ·
                      refine ⟨89705583821226215234071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119607445094968286978761 89705583821226215234071)
                      ·
                        rfl

theorem cell23_174701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_174701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174701 prefixEnd_174701 := by exact prefixLift 174701
  have htrace : WordTrace (prefixWord ++ tailWord_174701) baseStart_174701 baseEnd_174701 := by
    simpa [prefixWord, tailWord_174701, baseEnd_174701] using wordTrace_append hprefix tailTrace_174701
  have hstable : (prefixWord ++ tailWord_174701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174701).length < 2 ^ (prefixWord ++ tailWord_174701).sum := by decide
  have hdescent : baseEnd_174701 < baseStart_174701 := by decide
  rcases family_descends (prefixWord ++ tailWord_174701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174707 : List Nat := [1, 1, 1, 2, 2, 1, 1, 9, 5]
def baseStart_174707 : Nat := 118140960795 + 174707 * 2 ^ 59
def prefixEnd_174707 : Nat := 4983230072969 + 3 ^ 40 * 174707 * 2
def baseEnd_174707 : Nat := 9967629411683687973227

theorem tailTrace_174707 : CollatzResearch.WordTrace tailWord_174707 prefixEnd_174707 9967629411683687973227 := by
  unfold tailWord_174707
  simp only [CollatzResearch.WordTrace]
  refine ⟨6372087778073851425218375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4248058518715900950145583 6372087778073851425218375)
  ·
    refine ⟨9558131667110777137827563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6372087778073851425218375 9558131667110777137827563)
    ·
      refine ⟨14337197500666165706741345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9558131667110777137827563 14337197500666165706741345)
      ·
        refine ⟨10752898125499624280056009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14337197500666165706741345 10752898125499624280056009)
        ·
          refine ⟨8064673594124718210042007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10752898125499624280056009 8064673594124718210042007)
          ·
            refine ⟨12097010391187077315063011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8064673594124718210042007 12097010391187077315063011)
            ·
              refine ⟨18145515586780615972594517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12097010391187077315063011 18145515586780615972594517)
              ·
                refine ⟨106321380391292671714421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18145515586780615972594517 106321380391292671714421)
                ·
                  refine ⟨9967629411683687973227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106321380391292671714421 9967629411683687973227)
                  ·
                    rfl

theorem cell23_174707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 9, 5].length) (baseStart_174707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174707 prefixEnd_174707 := by exact prefixLift 174707
  have htrace : WordTrace (prefixWord ++ tailWord_174707) baseStart_174707 baseEnd_174707 := by
    simpa [prefixWord, tailWord_174707, baseEnd_174707] using wordTrace_append hprefix tailTrace_174707
  have hstable : (prefixWord ++ tailWord_174707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174707).length < 2 ^ (prefixWord ++ tailWord_174707).sum := by decide
  have hdescent : baseEnd_174707 < baseStart_174707 := by decide
  rcases family_descends (prefixWord ++ tailWord_174707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174724 : List Nat := [2, 3, 2, 1, 3, 3, 1, 1, 7]
def baseStart_174724 : Nat := 118140960795 + 174724 * 2 ^ 59
def prefixEnd_174724 : Nat := 4983230072969 + 3 ^ 40 * 174724 * 2
def baseEnd_174724 : Nat := 9968599319586625027385

theorem tailTrace_174724 : CollatzResearch.WordTrace tailWord_174724 prefixEnd_174724 9968599319586625027385 := by
  unfold tailWord_174724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3186353909506131664293613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4248471879341508885724817 3186353909506131664293613)
  ·
    refine ⟨1194882716064799374110105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3186353909506131664293613 1194882716064799374110105)
    ·
      refine ⟨896162037048599530582579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1194882716064799374110105 896162037048599530582579)
      ·
        refine ⟨1344243055572899295873869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896162037048599530582579 1344243055572899295873869)
        ·
          refine ⟨504091145839837235952701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1344243055572899295873869 504091145839837235952701)
          ·
            refine ⟨189034179689938963482263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504091145839837235952701 189034179689938963482263)
            ·
              refine ⟨283551269534908445223395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189034179689938963482263 283551269534908445223395)
              ·
                refine ⟨425326904302362667835093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283551269534908445223395 425326904302362667835093)
                ·
                  refine ⟨9968599319586625027385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 425326904302362667835093 9968599319586625027385)
                  ·
                    rfl

theorem cell23_174724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_174724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174724 prefixEnd_174724 := by exact prefixLift 174724
  have htrace : WordTrace (prefixWord ++ tailWord_174724) baseStart_174724 baseEnd_174724 := by
    simpa [prefixWord, tailWord_174724, baseEnd_174724] using wordTrace_append hprefix tailTrace_174724
  have hstable : (prefixWord ++ tailWord_174724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174724).length < 2 ^ (prefixWord ++ tailWord_174724).sum := by decide
  have hdescent : baseEnd_174724 < baseStart_174724 := by decide
  rcases family_descends (prefixWord ++ tailWord_174724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174777 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 3]
def baseStart_174777 : Nat := 118140960795 + 174777 * 2 ^ 59
def prefixEnd_174777 : Nat := 4983230072969 + 3 ^ 40 * 174777 * 2
def baseEnd_174777 : Nat := 89744608350967917883721

theorem tailTrace_174777 : CollatzResearch.WordTrace tailWord_174777 prefixEnd_174777 89744608350967917883721 := by
  unfold tailWord_174777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374640887820253380266585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4249760591880168920177723 6374640887820253380266585)
  ·
    refine ⟨4780980665865190035199939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6374640887820253380266585 4780980665865190035199939)
    ·
      refine ⟨7171470998797785052799909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4780980665865190035199939 7171470998797785052799909)
      ·
        refine ⟨1344650812274584697399983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7171470998797785052799909 1344650812274584697399983)
        ·
          refine ⟨2016976218411877046099975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344650812274584697399983 2016976218411877046099975)
          ·
            refine ⟨3025464327617815569149963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2016976218411877046099975 3025464327617815569149963)
            ·
              refine ⟨4538196491426723353724945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3025464327617815569149963 4538196491426723353724945)
              ·
                refine ⟨3403647368570042515293709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4538196491426723353724945 3403647368570042515293709)
                ·
                  refine ⟨1276367763213765943235141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3403647368570042515293709 1276367763213765943235141)
                  ·
                    refine ⟨239318955602581114356589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1276367763213765943235141 239318955602581114356589)
                    ·
                      refine ⟨89744608350967917883721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239318955602581114356589 89744608350967917883721)
                      ·
                        rfl

theorem cell23_174777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_174777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174777 prefixEnd_174777 := by exact prefixLift 174777
  have htrace : WordTrace (prefixWord ++ tailWord_174777) baseStart_174777 baseEnd_174777 := by
    simpa [prefixWord, tailWord_174777, baseEnd_174777] using wordTrace_append hprefix tailTrace_174777
  have hstable : (prefixWord ++ tailWord_174777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174777).length < 2 ^ (prefixWord ++ tailWord_174777).sum := by decide
  have hdescent : baseEnd_174777 < baseStart_174777 := by decide
  rcases family_descends (prefixWord ++ tailWord_174777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174867 : List Nat := [1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5]
def baseStart_174867 : Nat := 118140960795 + 174867 * 2 ^ 59
def prefixEnd_174867 : Nat := 4983230072969 + 3 ^ 40 * 174867 * 2
def baseEnd_174867 : Nat := 89790821609872565758307

theorem tailTrace_174867 : CollatzResearch.WordTrace tailWord_174867 prefixEnd_174867 89790821609872565758307 := by
  unfold tailWord_174867
  simp only [CollatzResearch.WordTrace]
  refine ⟨6377923457494198751042855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4251948971662799167361903 6377923457494198751042855)
  ·
    refine ⟨9566885186241298126564283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6377923457494198751042855 9566885186241298126564283)
    ·
      refine ⟨14350327779361947189846425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9566885186241298126564283 14350327779361947189846425)
      ·
        refine ⟨10762745834521460392384819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14350327779361947189846425 10762745834521460392384819)
        ·
          refine ⟨16144118751782190588577229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762745834521460392384819 16144118751782190588577229)
          ·
            refine ⟨6054044531918321470716461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16144118751782190588577229 6054044531918321470716461)
            ·
              refine ⟨2270266699469370551518673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6054044531918321470716461 2270266699469370551518673)
              ·
                refine ⟨1702700024602027913639005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270266699469370551518673 1702700024602027913639005)
                ·
                  refine ⟨638512509225760467614627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1702700024602027913639005 638512509225760467614627)
                  ·
                    refine ⟨957768763838640701421941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 638512509225760467614627 957768763838640701421941)
                    ·
                      refine ⟨89790821609872565758307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 957768763838640701421941 89790821609872565758307)
                      ·
                        rfl

theorem cell23_174867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_174867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174867 prefixEnd_174867 := by exact prefixLift 174867
  have htrace : WordTrace (prefixWord ++ tailWord_174867) baseStart_174867 baseEnd_174867 := by
    simpa [prefixWord, tailWord_174867, baseEnd_174867] using wordTrace_append hprefix tailTrace_174867
  have hstable : (prefixWord ++ tailWord_174867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174867).length < 2 ^ (prefixWord ++ tailWord_174867).sum := by decide
  have hdescent : baseEnd_174867 < baseStart_174867 := by decide
  rcases family_descends (prefixWord ++ tailWord_174867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174874 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 6, 4]
def baseStart_174874 : Nat := 118140960795 + 174874 * 2 ^ 59
def prefixEnd_174874 : Nat := 4983230072969 + 3 ^ 40 * 174874 * 2
def baseEnd_174874 : Nat := 29931471991484679456925

theorem tailTrace_174874 : CollatzResearch.WordTrace tailWord_174874 prefixEnd_174874 29931471991484679456925 := by
  unfold tailWord_174874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594544692117209736636919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4252119178979225964365117 1594544692117209736636919)
  ·
    refine ⟨2391817038175814604955379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594544692117209736636919 2391817038175814604955379)
    ·
      refine ⟨3587725557263721907433069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2391817038175814604955379 3587725557263721907433069)
      ·
        refine ⟨1345397083973895715287401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3587725557263721907433069 1345397083973895715287401)
        ·
          refine ⟨1009047812980421786465551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345397083973895715287401 1009047812980421786465551)
          ·
            refine ⟨1513571719470632679698327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009047812980421786465551 1513571719470632679698327)
            ·
              refine ⟨2270357579205949019547491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513571719470632679698327 2270357579205949019547491)
              ·
                refine ⟨3405536368808923529321237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2270357579205949019547491 3405536368808923529321237)
                ·
                  refine ⟨159634517287918290436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3405536368808923529321237 159634517287918290436933)
                  ·
                    refine ⟨29931471991484679456925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159634517287918290436933 29931471991484679456925)
                    ·
                      rfl

theorem cell23_174874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_174874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174874 prefixEnd_174874 := by exact prefixLift 174874
  have htrace : WordTrace (prefixWord ++ tailWord_174874) baseStart_174874 baseEnd_174874 := by
    simpa [prefixWord, tailWord_174874, baseEnd_174874] using wordTrace_append hprefix tailTrace_174874
  have hstable : (prefixWord ++ tailWord_174874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174874).length < 2 ^ (prefixWord ++ tailWord_174874).sum := by decide
  have hdescent : baseEnd_174874 < baseStart_174874 := by decide
  rcases family_descends (prefixWord ++ tailWord_174874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174917 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 4, 7]
def baseStart_174917 : Nat := 118140960795 + 174917 * 2 ^ 59
def prefixEnd_174917 : Nat := 4983230072969 + 3 ^ 40 * 174917 * 2
def baseEnd_174917 : Nat := 29938831880865790044359

theorem tailTrace_174917 : CollatzResearch.WordTrace tailWord_174917 prefixEnd_174917 29938831880865790044359 := by
  unfold tailWord_174917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6379747107313057290363005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4253164738208704860242003 6379747107313057290363005)
  ·
    refine ⟨2392405165242396483886127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6379747107313057290363005 2392405165242396483886127)
    ·
      refine ⟨3588607747863594725829191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2392405165242396483886127 3588607747863594725829191)
      ·
        refine ⟨5382911621795392088743787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3588607747863594725829191 5382911621795392088743787)
        ·
          refine ⟨8074367432693088133115681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5382911621795392088743787 8074367432693088133115681)
          ·
            refine ⟨6055775574519816099836761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8074367432693088133115681 6055775574519816099836761)
            ·
              refine ⟨4541831680889862074877571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6055775574519816099836761 4541831680889862074877571)
              ·
                refine ⟨6812747521334793112316357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4541831680889862074877571 6812747521334793112316357)
                ·
                  refine ⟨1277390160250273708559317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6812747521334793112316357 1277390160250273708559317)
                  ·
                    refine ⟨29938831880865790044359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1277390160250273708559317 29938831880865790044359)
                    ·
                      rfl

theorem cell23_174917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_174917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174917 prefixEnd_174917 := by exact prefixLift 174917
  have htrace : WordTrace (prefixWord ++ tailWord_174917) baseStart_174917 baseEnd_174917 := by
    simpa [prefixWord, tailWord_174917, baseEnd_174917] using wordTrace_append hprefix tailTrace_174917
  have hstable : (prefixWord ++ tailWord_174917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174917).length < 2 ^ (prefixWord ++ tailWord_174917).sum := by decide
  have hdescent : baseEnd_174917 < baseStart_174917 := by decide
  rcases family_descends (prefixWord ++ tailWord_174917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174948 : List Nat := [2, 3, 1, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_174948 : Nat := 118140960795 + 174948 * 2 ^ 59
def prefixEnd_174948 : Nat := 4983230072969 + 3 ^ 40 * 174948 * 2
def baseEnd_174948 : Nat := 89832413542886748845435

theorem tailTrace_174948 : CollatzResearch.WordTrace tailWord_174948 prefixEnd_174948 89832413542886748845435 := by
  unfold tailWord_174948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190438885100374792370749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4253918513467166389827665 3190438885100374792370749)
  ·
    refine ⟨1196414581912640547139031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3190438885100374792370749 1196414581912640547139031)
    ·
      refine ⟨1794621872868960820708547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1196414581912640547139031 1794621872868960820708547)
      ·
        refine ⟨2691932809303441231062821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1794621872868960820708547 2691932809303441231062821)
        ·
          refine ⟨504737401744395230824279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2691932809303441231062821 504737401744395230824279)
          ·
            refine ⟨757106102616592846236419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504737401744395230824279 757106102616592846236419)
            ·
              refine ⟨1135659153924889269354629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757106102616592846236419 1135659153924889269354629)
              ·
                refine ⟨212936091360916738003993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1135659153924889269354629 212936091360916738003993)
                ·
                  refine ⟨159702068520687553502995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212936091360916738003993 159702068520687553502995)
                  ·
                    refine ⟨239553102781031330254493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159702068520687553502995 239553102781031330254493)
                    ·
                      refine ⟨89832413542886748845435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239553102781031330254493 89832413542886748845435)
                      ·
                        rfl

theorem cell23_174948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_174948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174948 prefixEnd_174948 := by exact prefixLift 174948
  have htrace : WordTrace (prefixWord ++ tailWord_174948) baseStart_174948 baseEnd_174948 := by
    simpa [prefixWord, tailWord_174948, baseEnd_174948] using wordTrace_append hprefix tailTrace_174948
  have hstable : (prefixWord ++ tailWord_174948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174948).length < 2 ^ (prefixWord ++ tailWord_174948).sum := by decide
  have hdescent : baseEnd_174948 < baseStart_174948 := by decide
  rcases family_descends (prefixWord ++ tailWord_174948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_174971 : List Nat := [1, 1, 1, 1, 1, 5, 3, 3, 1, 4, 2]
def baseStart_174971 : Nat := 118140960795 + 174971 * 2 ^ 59
def prefixEnd_174971 : Nat := 4983230072969 + 3 ^ 40 * 174971 * 2
def baseEnd_174971 : Nat := 89844223597940158857829

theorem tailTrace_174971 : CollatzResearch.WordTrace tailWord_174971 prefixEnd_174971 89844223597940158857829 := by
  unfold tailWord_174971
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381716649117424512828767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4254477766078283008552511 6381716649117424512828767)
  ·
    refine ⟨9572574973676136769243151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6381716649117424512828767 9572574973676136769243151)
    ·
      refine ⟨14358862460514205153864727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9572574973676136769243151 14358862460514205153864727)
      ·
        refine ⟨21538293690771307730797091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14358862460514205153864727 21538293690771307730797091)
        ·
          refine ⟨32307440536156961596195637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21538293690771307730797091 32307440536156961596195637)
          ·
            refine ⟨3028822550264715149643341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32307440536156961596195637 3028822550264715149643341)
            ·
              refine ⟨1135808456349268181116253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3028822550264715149643341 1135808456349268181116253)
              ·
                refine ⟨425928171130975567918595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1135808456349268181116253 425928171130975567918595)
                ·
                  refine ⟨638892256696463351877893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425928171130975567918595 638892256696463351877893)
                  ·
                    refine ⟨119792298130586878477105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 638892256696463351877893 119792298130586878477105)
                    ·
                      refine ⟨89844223597940158857829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119792298130586878477105 89844223597940158857829)
                      ·
                        rfl

theorem cell23_174971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4, 2].length) (baseStart_174971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_174971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_174971 prefixEnd_174971 := by exact prefixLift 174971
  have htrace : WordTrace (prefixWord ++ tailWord_174971) baseStart_174971 baseEnd_174971 := by
    simpa [prefixWord, tailWord_174971, baseEnd_174971] using wordTrace_append hprefix tailTrace_174971
  have hstable : (prefixWord ++ tailWord_174971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_174971).length < 2 ^ (prefixWord ++ tailWord_174971).sum := by decide
  have hdescent : baseEnd_174971 < baseStart_174971 := by decide
  rcases family_descends (prefixWord ++ tailWord_174971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175011 : List Nat := [1, 1, 1, 4, 1, 2, 4, 4, 5]
def baseStart_175011 : Nat := 118140960795 + 175011 * 2 ^ 59
def prefixEnd_175011 : Nat := 4983230072969 + 3 ^ 40 * 175011 * 2
def baseEnd_175011 : Nat := 9984973647124444706405

theorem tailTrace_175011 : CollatzResearch.WordTrace tailWord_175011 prefixEnd_175011 9984973647124444706405 := by
  unfold tailWord_175011
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383175568972511344284887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4255450379315007562856591 6383175568972511344284887)
  ·
    refine ⟨9574763353458767016427331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383175568972511344284887 9574763353458767016427331)
    ·
      refine ⟨14362145030188150524640997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9574763353458767016427331 14362145030188150524640997)
      ·
        refine ⟨2692902193160278223370187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14362145030188150524640997 2692902193160278223370187)
        ·
          refine ⟨4039353289740417335055281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2692902193160278223370187 4039353289740417335055281)
          ·
            refine ⟨3029514967305313001291461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4039353289740417335055281 3029514967305313001291461)
            ·
              refine ⟨568034056369746187742149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3029514967305313001291461 568034056369746187742149)
              ·
                refine ⟨106506385569327410201653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 568034056369746187742149 106506385569327410201653)
                ·
                  refine ⟨9984973647124444706405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106506385569327410201653 9984973647124444706405)
                  ·
                    rfl

theorem cell23_175011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 5].length) (baseStart_175011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175011 prefixEnd_175011 := by exact prefixLift 175011
  have htrace : WordTrace (prefixWord ++ tailWord_175011) baseStart_175011 baseEnd_175011 := by
    simpa [prefixWord, tailWord_175011, baseEnd_175011] using wordTrace_append hprefix tailTrace_175011
  have hstable : (prefixWord ++ tailWord_175011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175011).length < 2 ^ (prefixWord ++ tailWord_175011).sum := by decide
  have hdescent : baseEnd_175011 < baseStart_175011 := by decide
  rcases family_descends (prefixWord ++ tailWord_175011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175028 : List Nat := [2, 5, 2, 1, 1, 1, 2, 2, 7]
def baseStart_175028 : Nat := 118140960795 + 175028 * 2 ^ 59
def prefixEnd_175028 : Nat := 4983230072969 + 3 ^ 40 * 175028 * 2
def baseEnd_175028 : Nat := 9985943555027381760563

theorem tailTrace_175028 : CollatzResearch.WordTrace tailWord_175028 prefixEnd_175028 9985943555027381760563 := by
  unfold tailWord_175028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191897804955461623826869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4255863739940615498435825 3191897804955461623826869)
  ·
    refine ⟨299240419214574527233769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3191897804955461623826869 299240419214574527233769)
    ·
      refine ⟨224430314410930895425327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299240419214574527233769 224430314410930895425327)
      ·
        refine ⟨336645471616396343137991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224430314410930895425327 336645471616396343137991)
        ·
          refine ⟨504968207424594514706987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336645471616396343137991 504968207424594514706987)
          ·
            refine ⟨757452311136891772060481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504968207424594514706987 757452311136891772060481)
            ·
              refine ⟨568089233352668829045361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757452311136891772060481 568089233352668829045361)
              ·
                refine ⟨426066925014501621784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568089233352668829045361 426066925014501621784021)
                ·
                  refine ⟨9985943555027381760563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 426066925014501621784021 9985943555027381760563)
                  ·
                    rfl

theorem cell23_175028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_175028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175028 prefixEnd_175028 := by exact prefixLift 175028
  have htrace : WordTrace (prefixWord ++ tailWord_175028) baseStart_175028 baseEnd_175028 := by
    simpa [prefixWord, tailWord_175028, baseEnd_175028] using wordTrace_append hprefix tailTrace_175028
  have hstable : (prefixWord ++ tailWord_175028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175028).length < 2 ^ (prefixWord ++ tailWord_175028).sum := by decide
  have hdescent : baseEnd_175028 < baseStart_175028 := by decide
  rcases family_descends (prefixWord ++ tailWord_175028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175031 : List Nat := [1, 1, 3, 1, 3, 1, 2, 2, 2, 5, 2]
def baseStart_175031 : Nat := 118140960795 + 175031 * 2 ^ 59
def prefixEnd_175031 : Nat := 4983230072969 + 3 ^ 40 * 175031 * 2
def baseEnd_175031 : Nat := 89875032437209924107553

theorem tailTrace_175031 : CollatzResearch.WordTrace tailWord_175031 prefixEnd_175031 89875032437209924107553 := by
  unfold tailWord_175031
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383905028900054760012947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4255936685933369840008631 6383905028900054760012947)
  ·
    refine ⟨9575857543350082140019421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383905028900054760012947 9575857543350082140019421)
    ·
      refine ⟨3590946578756280802507283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9575857543350082140019421 3590946578756280802507283)
      ·
        refine ⟨5386419868134421203760925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590946578756280802507283 5386419868134421203760925)
        ·
          refine ⟨2019907450550407951410347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5386419868134421203760925 2019907450550407951410347)
          ·
            refine ⟨3029861175825611927115521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019907450550407951410347 3029861175825611927115521)
            ·
              refine ⟨2272395881869208945336641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3029861175825611927115521 2272395881869208945336641)
              ·
                refine ⟨1704296911401906709002481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2272395881869208945336641 1704296911401906709002481)
                ·
                  refine ⟨1278222683551430031751861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1704296911401906709002481 1278222683551430031751861)
                  ·
                    refine ⟨119833376582946565476737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1278222683551430031751861 119833376582946565476737)
                    ·
                      refine ⟨89875032437209924107553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119833376582946565476737 89875032437209924107553)
                      ·
                        rfl

theorem cell23_175031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_175031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175031 prefixEnd_175031 := by exact prefixLift 175031
  have htrace : WordTrace (prefixWord ++ tailWord_175031) baseStart_175031 baseEnd_175031 := by
    simpa [prefixWord, tailWord_175031, baseEnd_175031] using wordTrace_append hprefix tailTrace_175031
  have hstable : (prefixWord ++ tailWord_175031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175031).length < 2 ^ (prefixWord ++ tailWord_175031).sum := by decide
  have hdescent : baseEnd_175031 < baseStart_175031 := by decide
  rcases family_descends (prefixWord ++ tailWord_175031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175058 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 2, 5]
def baseStart_175058 : Nat := 118140960795 + 175058 * 2 ^ 59
def prefixEnd_175058 : Nat := 4983230072969 + 3 ^ 40 * 175058 * 2
def baseEnd_175058 : Nat := 29962965471627106156643

theorem tailTrace_175058 : CollatzResearch.WordTrace tailWord_175058 prefixEnd_175058 29962965471627106156643 := by
  unfold tailWord_175058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1596222449950559592811457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4256593199868158914163885 1596222449950559592811457)
  ·
    refine ⟨1197166837462919694608593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1596222449950559592811457 1197166837462919694608593)
    ·
      refine ⟨897875128097189770956445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1197166837462919694608593 897875128097189770956445)
      ·
        refine ⟨336703173036446164108667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 897875128097189770956445 336703173036446164108667)
        ·
          refine ⟨505054759554669246163001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336703173036446164108667 505054759554669246163001)
          ·
            refine ⟨378791069666001934622251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505054759554669246163001 378791069666001934622251)
            ·
              refine ⟨568186604499002901933377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378791069666001934622251 568186604499002901933377)
              ·
                refine ⟨426139953374252176450033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568186604499002901933377 426139953374252176450033)
                ·
                  refine ⟨319604965030689132337525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 426139953374252176450033 319604965030689132337525)
                  ·
                    refine ⟨29962965471627106156643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 319604965030689132337525 29962965471627106156643)
                    ·
                      rfl

theorem cell23_175058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_175058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175058 prefixEnd_175058 := by exact prefixLift 175058
  have htrace : WordTrace (prefixWord ++ tailWord_175058) baseStart_175058 baseEnd_175058 := by
    simpa [prefixWord, tailWord_175058, baseEnd_175058] using wordTrace_append hprefix tailTrace_175058
  have hstable : (prefixWord ++ tailWord_175058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175058).length < 2 ^ (prefixWord ++ tailWord_175058).sum := by decide
  have hdescent : baseEnd_175058 < baseStart_175058 := by decide
  rcases family_descends (prefixWord ++ tailWord_175058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175062 : List Nat := [5, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_175062 : Nat := 118140960795 + 175062 * 2 ^ 59
def prefixEnd_175062 : Nat := 4983230072969 + 3 ^ 40 * 175062 * 2
def baseEnd_175062 : Nat := 9987883370833255868879

theorem tailTrace_175062 : CollatzResearch.WordTrace tailWord_175062 prefixEnd_175062 9987883370833255868879 := by
  unfold tailWord_175062
  simp only [CollatzResearch.WordTrace]
  refine ⟨399064730736734190899465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4256690461191831369594293 399064730736734190899465)
  ·
    refine ⟨299298548052550643174599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 399064730736734190899465 299298548052550643174599)
    ·
      refine ⟨448947822078825964761899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299298548052550643174599 448947822078825964761899)
      ·
        refine ⟨673421733118238947142849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448947822078825964761899 673421733118238947142849)
        ·
          refine ⟨505066299838679210357137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673421733118238947142849 505066299838679210357137)
          ·
            refine ⟨378799724879009407767853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505066299838679210357137 378799724879009407767853)
            ·
              refine ⟨142049896829628527912945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 378799724879009407767853 142049896829628527912945)
              ·
                refine ⟨106537422622221395934709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142049896829628527912945 106537422622221395934709)
                ·
                  refine ⟨9987883370833255868879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106537422622221395934709 9987883370833255868879)
                  ·
                    rfl

theorem cell23_175062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_175062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175062 prefixEnd_175062 := by exact prefixLift 175062
  have htrace : WordTrace (prefixWord ++ tailWord_175062) baseStart_175062 baseEnd_175062 := by
    simpa [prefixWord, tailWord_175062, baseEnd_175062] using wordTrace_append hprefix tailTrace_175062
  have hstable : (prefixWord ++ tailWord_175062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175062).length < 2 ^ (prefixWord ++ tailWord_175062).sum := by decide
  have hdescent : baseEnd_175062 < baseStart_175062 := by decide
  rcases family_descends (prefixWord ++ tailWord_175062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175118 : List Nat := [4, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_175118 : Nat := 118140960795 + 175118 * 2 ^ 59
def prefixEnd_175118 : Nat := 4983230072969 + 3 ^ 40 * 175118 * 2
def baseEnd_175118 : Nat := 9991078361572342635517

theorem tailTrace_175118 : CollatzResearch.WordTrace tailWord_175118 prefixEnd_175118 9991078361572342635517 := by
  unfold tailWord_175118
  simp only [CollatzResearch.WordTrace]
  refine ⟨798384772448108577303751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4258052119723245745620005 798384772448108577303751)
  ·
    refine ⟨1197577158672162865955627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798384772448108577303751 1197577158672162865955627)
    ·
      refine ⟨1796365738008244298933441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197577158672162865955627 1796365738008244298933441)
      ·
        refine ⟨1347274303506183224200081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1796365738008244298933441 1347274303506183224200081)
        ·
          refine ⟨1010455727629637418150061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347274303506183224200081 1010455727629637418150061)
          ·
            refine ⟨378920897861114031806273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1010455727629637418150061 378920897861114031806273)
            ·
              refine ⟨284190673395835523854705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378920897861114031806273 284190673395835523854705)
              ·
                refine ⟨213143005046876642891029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284190673395835523854705 213143005046876642891029)
                ·
                  refine ⟨9991078361572342635517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213143005046876642891029 9991078361572342635517)
                  ·
                    rfl

theorem cell23_175118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_175118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175118 prefixEnd_175118 := by exact prefixLift 175118
  have htrace : WordTrace (prefixWord ++ tailWord_175118) baseStart_175118 baseEnd_175118 := by
    simpa [prefixWord, tailWord_175118, baseEnd_175118] using wordTrace_append hprefix tailTrace_175118
  have hstable : (prefixWord ++ tailWord_175118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175118).length < 2 ^ (prefixWord ++ tailWord_175118).sum := by decide
  have hdescent : baseEnd_175118 < baseStart_175118 := by decide
  rcases family_descends (prefixWord ++ tailWord_175118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175165 : List Nat := [1, 4, 1, 3, 1, 2, 4, 1, 1, 5]
def baseStart_175165 : Nat := 118140960795 + 175165 * 2 ^ 59
def prefixEnd_175165 : Nat := 4983230072969 + 3 ^ 40 * 175165 * 2
def baseEnd_175165 : Nat := 29981279614970799943979

theorem tailTrace_175165 : CollatzResearch.WordTrace tailWord_175165 prefixEnd_175165 29981279614970799943979 := by
  unfold tailWord_175165
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388792410414595645390949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259194940276397096927299 6388792410414595645390949)
  ·
    refine ⟨1197898576952736683510803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6388792410414595645390949 1197898576952736683510803)
    ·
      refine ⟨1796847865429105025266205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1197898576952736683510803 1796847865429105025266205)
      ·
        refine ⟨673817949535914384474827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1796847865429105025266205 673817949535914384474827)
        ·
          refine ⟨1010726924303871576712241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673817949535914384474827 1010726924303871576712241)
          ·
            refine ⟨758045193227903682534181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1010726924303871576712241 758045193227903682534181)
            ·
              refine ⟨142133473730231940475159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 758045193227903682534181 142133473730231940475159)
              ·
                refine ⟨213200210595347910712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142133473730231940475159 213200210595347910712739)
                ·
                  refine ⟨319800315893021866069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213200210595347910712739 319800315893021866069109)
                  ·
                    refine ⟨29981279614970799943979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 319800315893021866069109 29981279614970799943979)
                    ·
                      rfl

theorem cell23_175165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_175165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175165 prefixEnd_175165 := by exact prefixLift 175165
  have htrace : WordTrace (prefixWord ++ tailWord_175165) baseStart_175165 baseEnd_175165 := by
    simpa [prefixWord, tailWord_175165, baseEnd_175165] using wordTrace_append hprefix tailTrace_175165
  have hstable : (prefixWord ++ tailWord_175165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175165).length < 2 ^ (prefixWord ++ tailWord_175165).sum := by decide
  have hdescent : baseEnd_175165 < baseStart_175165 := by decide
  rcases family_descends (prefixWord ++ tailWord_175165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175168 : List Nat := [2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_175168 : Nat := 118140960795 + 175168 * 2 ^ 59
def prefixEnd_175168 : Nat := 4983230072969 + 3 ^ 40 * 175168 * 2
def baseEnd_175168 : Nat := 89945379286875888094423

theorem tailTrace_175168 : CollatzResearch.WordTrace tailWord_175168 prefixEnd_175168 89945379286875888094423 := by
  unfold tailWord_175168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194450914701863578875079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4259267886269151438500105 3194450914701863578875079)
  ·
    refine ⟨4791676372052795368312619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3194450914701863578875079 4791676372052795368312619)
    ·
      refine ⟨7187514558079193052468929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791676372052795368312619 7187514558079193052468929)
      ·
        refine ⟨5390635918559394789351697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7187514558079193052468929 5390635918559394789351697)
        ·
          refine ⟨4042976938919546092013773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5390635918559394789351697 4042976938919546092013773)
          ·
            refine ⟨1516116352094829784505165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4042976938919546092013773 1516116352094829784505165)
            ·
              refine ⟨568543632035561169189437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516116352094829784505165 568543632035561169189437)
              ·
                refine ⟨213203862013335438446039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568543632035561169189437 213203862013335438446039)
                ·
                  refine ⟨319805793020003157669059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213203862013335438446039 319805793020003157669059)
                  ·
                    refine ⟨479708689530004736503589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 319805793020003157669059 479708689530004736503589)
                    ·
                      refine ⟨89945379286875888094423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 479708689530004736503589 89945379286875888094423)
                      ·
                        rfl

theorem cell23_175168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_175168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175168 prefixEnd_175168 := by exact prefixLift 175168
  have htrace : WordTrace (prefixWord ++ tailWord_175168) baseStart_175168 baseEnd_175168 := by
    simpa [prefixWord, tailWord_175168, baseEnd_175168] using wordTrace_append hprefix tailTrace_175168
  have hstable : (prefixWord ++ tailWord_175168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175168).length < 2 ^ (prefixWord ++ tailWord_175168).sum := by decide
  have hdescent : baseEnd_175168 < baseStart_175168 := by decide
  rcases family_descends (prefixWord ++ tailWord_175168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175171 : List Nat := [1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5]
def baseStart_175171 : Nat := 118140960795 + 175171 * 2 ^ 59
def prefixEnd_175171 : Nat := 4983230072969 + 3 ^ 40 * 175171 * 2
def baseEnd_175171 : Nat := 89946919728839376356909

theorem tailTrace_175171 : CollatzResearch.WordTrace tailWord_175171 prefixEnd_175171 89946919728839376356909 := by
  unfold tailWord_175171
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389011248392858670109367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259340832261905780072911 6389011248392858670109367)
  ·
    refine ⟨9583516872589288005164051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6389011248392858670109367 9583516872589288005164051)
    ·
      refine ⟨14375275308883932007746077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583516872589288005164051 14375275308883932007746077)
      ·
        refine ⟨5390728240831474502904779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14375275308883932007746077 5390728240831474502904779)
        ·
          refine ⟨8086092361247211754357169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5390728240831474502904779 8086092361247211754357169)
          ·
            refine ⟨6064569270935408815767877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8086092361247211754357169 6064569270935408815767877)
            ·
              refine ⟨1137106738300389152956477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6064569270935408815767877 1137106738300389152956477)
              ·
                refine ⟨426415026862645932358679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137106738300389152956477 426415026862645932358679)
                ·
                  refine ⟨639622540293968898538019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426415026862645932358679 639622540293968898538019)
                  ·
                    refine ⟨959433810440953347807029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 639622540293968898538019 959433810440953347807029)
                    ·
                      refine ⟨89946919728839376356909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 959433810440953347807029 89946919728839376356909)
                      ·
                        rfl

theorem cell23_175171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_175171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175171 prefixEnd_175171 := by exact prefixLift 175171
  have htrace : WordTrace (prefixWord ++ tailWord_175171) baseStart_175171 baseEnd_175171 := by
    simpa [prefixWord, tailWord_175171, baseEnd_175171] using wordTrace_append hprefix tailTrace_175171
  have hstable : (prefixWord ++ tailWord_175171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175171).length < 2 ^ (prefixWord ++ tailWord_175171).sum := by decide
  have hdescent : baseEnd_175171 < baseStart_175171 := by decide
  rcases family_descends (prefixWord ++ tailWord_175171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175185 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 3, 2, 2]
def baseStart_175185 : Nat := 118140960795 + 175185 * 2 ^ 59
def prefixEnd_175185 : Nat := 4983230072969 + 3 ^ 40 * 175185 * 2
def baseEnd_175185 : Nat := 89954108458002321581845

theorem tailTrace_175185 : CollatzResearch.WordTrace tailWord_175185 prefixEnd_175185 89954108458002321581845 := by
  unfold tailWord_175185
  simp only [CollatzResearch.WordTrace]
  refine ⟨6389521870342139061119009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4259681246894759374079339 6389521870342139061119009)
  ·
    refine ⟨4792141402756604295839257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6389521870342139061119009 4792141402756604295839257)
    ·
      refine ⟨3594106052067453221879443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4792141402756604295839257 3594106052067453221879443)
      ·
        refine ⟨5391159078101179832819165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3594106052067453221879443 5391159078101179832819165)
        ·
          refine ⟨2021684654287942437307187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5391159078101179832819165 2021684654287942437307187)
          ·
            refine ⟨3032526981431913655960781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021684654287942437307187 3032526981431913655960781)
            ·
              refine ⟨1137197618036967620985293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3032526981431913655960781 1137197618036967620985293)
              ·
                refine ⟨426449106763862857869485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137197618036967620985293 426449106763862857869485)
                ·
                  refine ⟨159918415036448571701057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426449106763862857869485 159918415036448571701057)
                  ·
                    refine ⟨119938811277336428775793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159918415036448571701057 119938811277336428775793)
                    ·
                      refine ⟨89954108458002321581845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119938811277336428775793 89954108458002321581845)
                      ·
                        rfl

theorem cell23_175185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 3, 2, 2].length) (baseStart_175185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175185 prefixEnd_175185 := by exact prefixLift 175185
  have htrace : WordTrace (prefixWord ++ tailWord_175185) baseStart_175185 baseEnd_175185 := by
    simpa [prefixWord, tailWord_175185, baseEnd_175185] using wordTrace_append hprefix tailTrace_175185
  have hstable : (prefixWord ++ tailWord_175185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175185).length < 2 ^ (prefixWord ++ tailWord_175185).sum := by decide
  have hdescent : baseEnd_175185 < baseStart_175185 := by decide
  rcases family_descends (prefixWord ++ tailWord_175185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175188 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_175188 : Nat := 118140960795 + 175188 * 2 ^ 59
def prefixEnd_175188 : Nat := 4983230072969 + 3 ^ 40 * 175188 * 2
def baseEnd_175188 : Nat := 89955648899965809844331

theorem tailTrace_175188 : CollatzResearch.WordTrace tailWord_175188 prefixEnd_175188 89955648899965809844331 := by
  unfold tailWord_175188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3194815644665635286739109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4259754192887513715652145 3194815644665635286739109)
  ·
    refine ⟨599027933374806616263583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3194815644665635286739109 599027933374806616263583)
    ·
      refine ⟨898541900062209924395375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599027933374806616263583 898541900062209924395375)
      ·
        refine ⟨1347812850093314886593063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898541900062209924395375 1347812850093314886593063)
        ·
          refine ⟨2021719275139972329889595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347812850093314886593063 2021719275139972329889595)
          ·
            refine ⟨3032578912709958494834393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2021719275139972329889595 3032578912709958494834393)
            ·
              refine ⟨2274434184532468871125795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3032578912709958494834393 2274434184532468871125795)
              ·
                refine ⟨3411651276798703306688693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2274434184532468871125795 3411651276798703306688693)
                ·
                  refine ⟨319842307199878435002065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3411651276798703306688693 319842307199878435002065)
                  ·
                    refine ⟨239881730399908826251549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319842307199878435002065 239881730399908826251549)
                    ·
                      refine ⟨89955648899965809844331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239881730399908826251549 89955648899965809844331)
                      ·
                        rfl

theorem cell23_175188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_175188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175188 prefixEnd_175188 := by exact prefixLift 175188
  have htrace : WordTrace (prefixWord ++ tailWord_175188) baseStart_175188 baseEnd_175188 := by
    simpa [prefixWord, tailWord_175188, baseEnd_175188] using wordTrace_append hprefix tailTrace_175188
  have hstable : (prefixWord ++ tailWord_175188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175188).length < 2 ^ (prefixWord ++ tailWord_175188).sum := by decide
  have hdescent : baseEnd_175188 < baseStart_175188 := by decide
  rcases family_descends (prefixWord ++ tailWord_175188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175202 : List Nat := [3, 3, 2, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_175202 : Nat := 118140960795 + 175202 * 2 ^ 59
def prefixEnd_175202 : Nat := 4983230072969 + 3 ^ 40 * 175202 * 2
def baseEnd_175202 : Nat := 89962837629128755069267

theorem tailTrace_175202 : CollatzResearch.WordTrace tailWord_175202 prefixEnd_175202 89962837629128755069267 := by
  unfold tailWord_175202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597535477820137741121965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4260094607520367309658573 1597535477820137741121965)
  ·
    refine ⟨599075804182551652920737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1597535477820137741121965 599075804182551652920737)
    ·
      refine ⟨449306853136913739690553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 599075804182551652920737 449306853136913739690553)
      ·
        refine ⟨336980139852685304767915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449306853136913739690553 336980139852685304767915)
        ·
          refine ⟨505470209779027957151873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336980139852685304767915 505470209779027957151873)
          ·
            refine ⟨379102657334270967863905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505470209779027957151873 379102657334270967863905)
            ·
              refine ⟨284326993000703225897929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379102657334270967863905 284326993000703225897929)
              ·
                refine ⟨213245244750527419423447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284326993000703225897929 213245244750527419423447)
                ·
                  refine ⟨319867867125791129135171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213245244750527419423447 319867867125791129135171)
                  ·
                    refine ⟨479801800688686693702757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 319867867125791129135171 479801800688686693702757)
                    ·
                      refine ⟨89962837629128755069267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 479801800688686693702757 89962837629128755069267)
                      ·
                        rfl

theorem cell23_175202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_175202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175202 prefixEnd_175202 := by exact prefixLift 175202
  have htrace : WordTrace (prefixWord ++ tailWord_175202) baseStart_175202 baseEnd_175202 := by
    simpa [prefixWord, tailWord_175202, baseEnd_175202] using wordTrace_append hprefix tailTrace_175202
  have hstable : (prefixWord ++ tailWord_175202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175202).length < 2 ^ (prefixWord ++ tailWord_175202).sum := by decide
  have hdescent : baseEnd_175202 < baseStart_175202 := by decide
  rcases family_descends (prefixWord ++ tailWord_175202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175205 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 3]
def baseStart_175205 : Nat := 118140960795 + 175205 * 2 ^ 59
def prefixEnd_175205 : Nat := 4983230072969 + 3 ^ 40 * 175205 * 2
def baseEnd_175205 : Nat := 89964378071092243331753

theorem tailTrace_175205 : CollatzResearch.WordTrace tailWord_175205 prefixEnd_175205 89964378071092243331753 := by
  unfold tailWord_175205
  simp only [CollatzResearch.WordTrace]
  refine ⟨6390251330269682476847069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4260167553513121651231379 6390251330269682476847069)
  ·
    refine ⟨2396344248851130928817651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6390251330269682476847069 2396344248851130928817651)
    ·
      refine ⟨3594516373276696393226477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2396344248851130928817651 3594516373276696393226477)
      ·
        refine ⟨1347943639978761147459929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3594516373276696393226477 1347943639978761147459929)
        ·
          refine ⟨1010957729984070860594947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347943639978761147459929 1010957729984070860594947)
          ·
            refine ⟨1516436594976106290892421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010957729984070860594947 1516436594976106290892421)
            ·
              refine ⟨284331861558019929542329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1516436594976106290892421 284331861558019929542329)
              ·
                refine ⟨213248896168514947156747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284331861558019929542329 213248896168514947156747)
                ·
                  refine ⟨319873344252772420735121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213248896168514947156747 319873344252772420735121)
                  ·
                    refine ⟨239905008189579315551341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319873344252772420735121 239905008189579315551341)
                    ·
                      refine ⟨89964378071092243331753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239905008189579315551341 89964378071092243331753)
                      ·
                        rfl

theorem cell23_175205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_175205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175205 prefixEnd_175205 := by exact prefixLift 175205
  have htrace : WordTrace (prefixWord ++ tailWord_175205) baseStart_175205 baseEnd_175205 := by
    simpa [prefixWord, tailWord_175205, baseEnd_175205] using wordTrace_append hprefix tailTrace_175205
  have hstable : (prefixWord ++ tailWord_175205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175205).length < 2 ^ (prefixWord ++ tailWord_175205).sum := by decide
  have hdescent : baseEnd_175205 < baseStart_175205 := by decide
  rcases family_descends (prefixWord ++ tailWord_175205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175218 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3]
def baseStart_175218 : Nat := 118140960795 + 175218 * 2 ^ 59
def prefixEnd_175218 : Nat := 4983230072969 + 3 ^ 40 * 175218 * 2
def baseEnd_175218 : Nat := 89971053319600692469193

theorem tailTrace_175218 : CollatzResearch.WordTrace tailWord_175218 prefixEnd_175218 89971053319600692469193 := by
  unfold tailWord_175218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597681369805646424267577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4260483652815057131380205 1597681369805646424267577)
  ·
    refine ⟨1198261027354234818200683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1597681369805646424267577 1198261027354234818200683)
    ·
      refine ⟨1797391541031352227301025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198261027354234818200683 1797391541031352227301025)
      ·
        refine ⟨1348043655773514170475769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1797391541031352227301025 1348043655773514170475769)
        ·
          refine ⟨1011032741830135627856827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348043655773514170475769 1011032741830135627856827)
          ·
            refine ⟨1516549112745203441785241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011032741830135627856827 1516549112745203441785241)
            ·
              refine ⟨1137411834558902581338931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516549112745203441785241 1137411834558902581338931)
              ·
                refine ⟨1706117751838353872008397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137411834558902581338931 1706117751838353872008397)
                ·
                  refine ⟨639794156939382702003149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1706117751838353872008397 639794156939382702003149)
                  ·
                    refine ⟨239922808852268513251181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 639794156939382702003149 239922808852268513251181)
                    ·
                      refine ⟨89971053319600692469193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239922808852268513251181 89971053319600692469193)
                      ·
                        rfl

theorem cell23_175218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_175218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175218 prefixEnd_175218 := by exact prefixLift 175218
  have htrace : WordTrace (prefixWord ++ tailWord_175218) baseStart_175218 baseEnd_175218 := by
    simpa [prefixWord, tailWord_175218, baseEnd_175218] using wordTrace_append hprefix tailTrace_175218
  have hstable : (prefixWord ++ tailWord_175218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175218).length < 2 ^ (prefixWord ++ tailWord_175218).sum := by decide
  have hdescent : baseEnd_175218 < baseStart_175218 := by decide
  rcases family_descends (prefixWord ++ tailWord_175218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175230 : List Nat := [4, 2, 4, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_175230 : Nat := 118140960795 + 175230 * 2 ^ 59
def prefixEnd_175230 : Nat := 4983230072969 + 3 ^ 40 * 175230 * 2
def baseEnd_175230 : Nat := 89977215087454645519139

theorem tailTrace_175230 : CollatzResearch.WordTrace tailWord_175230 prefixEnd_175230 89977215087454645519139 := by
  unfold tailWord_175230
  simp only [CollatzResearch.WordTrace]
  refine ⟨798895394397388968313393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4260775436786074497671429 798895394397388968313393)
  ·
    refine ⟨599171545798041726235045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798895394397388968313393 599171545798041726235045)
    ·
      refine ⟨112344664837132823669071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 599171545798041726235045 112344664837132823669071)
      ·
        refine ⟨168516997255699235503607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112344664837132823669071 168516997255699235503607)
        ·
          refine ⟨252775495883548853255411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168516997255699235503607 252775495883548853255411)
          ·
            refine ⟨379163243825323279883117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252775495883548853255411 379163243825323279883117)
            ·
              refine ⟨142186216434496229956169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379163243825323279883117 142186216434496229956169)
              ·
                refine ⟨106639662325872172467127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142186216434496229956169 106639662325872172467127)
                ·
                  refine ⟨159959493488808258700691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106639662325872172467127 159959493488808258700691)
                  ·
                    refine ⟨239939240233212388051037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159959493488808258700691 239939240233212388051037)
                    ·
                      refine ⟨89977215087454645519139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239939240233212388051037 89977215087454645519139)
                      ·
                        rfl

theorem cell23_175230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_175230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175230 prefixEnd_175230 := by exact prefixLift 175230
  have htrace : WordTrace (prefixWord ++ tailWord_175230) baseStart_175230 baseEnd_175230 := by
    simpa [prefixWord, tailWord_175230, baseEnd_175230] using wordTrace_append hprefix tailTrace_175230
  have hstable : (prefixWord ++ tailWord_175230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175230).length < 2 ^ (prefixWord ++ tailWord_175230).sum := by decide
  have hdescent : baseEnd_175230 < baseStart_175230 := by decide
  rcases family_descends (prefixWord ++ tailWord_175230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175235 : List Nat := [1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 3]
def baseStart_175235 : Nat := 118140960795 + 175235 * 2 ^ 59
def prefixEnd_175235 : Nat := 4983230072969 + 3 ^ 40 * 175235 * 2
def baseEnd_175235 : Nat := 89979782490727125956615

theorem tailTrace_175235 : CollatzResearch.WordTrace tailWord_175235 prefixEnd_175235 89979782490727125956615 := by
  unfold tailWord_175235
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391345520160997600439159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4260897013440665066959439 6391345520160997600439159)
  ·
    refine ⟨9587018280241496400658739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391345520160997600439159 9587018280241496400658739)
    ·
      refine ⟨14380527420362244600988109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587018280241496400658739 14380527420362244600988109)
      ·
        refine ⟨5392697782635841725370541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14380527420362244600988109 5392697782635841725370541)
        ·
          refine ⟨2022261668488440647013953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5392697782635841725370541 2022261668488440647013953)
          ·
            refine ⟨1516696251366330485260465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022261668488440647013953 1516696251366330485260465)
            ·
              refine ⟨1137522188524747863945349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516696251366330485260465 1137522188524747863945349)
              ·
                refine ⟨213285410348390224489753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1137522188524747863945349 213285410348390224489753)
                ·
                  refine ⟨159964057761292668367315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213285410348390224489753 159964057761292668367315)
                  ·
                    refine ⟨239946086641939002550973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159964057761292668367315 239946086641939002550973)
                    ·
                      refine ⟨89979782490727125956615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 239946086641939002550973 89979782490727125956615)
                      ·
                        rfl

theorem cell23_175235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_175235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175235 prefixEnd_175235 := by exact prefixLift 175235
  have htrace : WordTrace (prefixWord ++ tailWord_175235) baseStart_175235 baseEnd_175235 := by
    simpa [prefixWord, tailWord_175235, baseEnd_175235] using wordTrace_append hprefix tailTrace_175235
  have hstable : (prefixWord ++ tailWord_175235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175235).length < 2 ^ (prefixWord ++ tailWord_175235).sum := by decide
  have hdescent : baseEnd_175235 < baseStart_175235 := by decide
  rcases family_descends (prefixWord ++ tailWord_175235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175236 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_175236 : Nat := 118140960795 + 175236 * 2 ^ 59
def prefixEnd_175236 : Nat := 4983230072969 + 3 ^ 40 * 175236 * 2
def baseEnd_175236 : Nat := 89980295971381622044111

theorem tailTrace_175236 : CollatzResearch.WordTrace tailWord_175236 prefixEnd_175236 89980295971381622044111 := by
  unfold tailWord_175236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195690996578687385612781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4260921328771583180817041 3195690996578687385612781)
  ·
    refine ⟨1198384123717007769604793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3195690996578687385612781 1198384123717007769604793)
    ·
      refine ⟨898788092787755827203595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1198384123717007769604793 898788092787755827203595)
      ·
        refine ⟨1348182139181633740805393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898788092787755827203595 1348182139181633740805393)
        ·
          refine ⟨1011136604386225305604045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348182139181633740805393 1011136604386225305604045)
          ·
            refine ⟨379176226644834489601517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1011136604386225305604045 379176226644834489601517)
            ·
              refine ⟨142191084991812933600569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379176226644834489601517 142191084991812933600569)
              ·
                refine ⟨106643313743859700200427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142191084991812933600569 106643313743859700200427)
                ·
                  refine ⟨159964970615789550300641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106643313743859700200427 159964970615789550300641)
                  ·
                    refine ⟨119973727961842162725481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 159964970615789550300641 119973727961842162725481)
                    ·
                      refine ⟨89980295971381622044111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 119973727961842162725481 89980295971381622044111)
                      ·
                        rfl

theorem cell23_175236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_175236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175236 prefixEnd_175236 := by exact prefixLift 175236
  have htrace : WordTrace (prefixWord ++ tailWord_175236) baseStart_175236 baseEnd_175236 := by
    simpa [prefixWord, tailWord_175236, baseEnd_175236] using wordTrace_append hprefix tailTrace_175236
  have hstable : (prefixWord ++ tailWord_175236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175236).length < 2 ^ (prefixWord ++ tailWord_175236).sum := by decide
  have hdescent : baseEnd_175236 < baseStart_175236 := by decide
  rcases family_descends (prefixWord ++ tailWord_175236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175251 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 2, 6]
def baseStart_175251 : Nat := 118140960795 + 175251 * 2 ^ 59
def prefixEnd_175251 : Nat := 4983230072969 + 3 ^ 40 * 175251 * 2
def baseEnd_175251 : Nat := 29995999393733021118847

theorem tailTrace_175251 : CollatzResearch.WordTrace tailWord_175251 prefixEnd_175251 29995999393733021118847 := by
  unfold tailWord_175251
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391929088103032333021607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4261286058735354888681071 6391929088103032333021607)
  ·
    refine ⟨9587893632154548499532411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391929088103032333021607 9587893632154548499532411)
    ·
      refine ⟨14381840448231822749298617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587893632154548499532411 14381840448231822749298617)
      ·
        refine ⟨10786380336173867061973963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14381840448231822749298617 10786380336173867061973963)
        ·
          refine ⟨16179570504260800592960945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10786380336173867061973963 16179570504260800592960945)
          ·
            refine ⟨12134677878195600444720709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16179570504260800592960945 12134677878195600444720709)
            ·
              refine ⟨2275252102161675083385133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12134677878195600444720709 2275252102161675083385133)
              ·
                refine ⟨853219538310628156269425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2275252102161675083385133 853219538310628156269425)
                ·
                  refine ⟨639914653732971117202069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853219538310628156269425 639914653732971117202069)
                  ·
                    refine ⟨29995999393733021118847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 639914653732971117202069 29995999393733021118847)
                    ·
                      rfl

theorem cell23_175251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 6].length) (baseStart_175251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175251 prefixEnd_175251 := by exact prefixLift 175251
  have htrace : WordTrace (prefixWord ++ tailWord_175251) baseStart_175251 baseEnd_175251 := by
    simpa [prefixWord, tailWord_175251, baseEnd_175251] using wordTrace_append hprefix tailTrace_175251
  have hstable : (prefixWord ++ tailWord_175251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175251).length < 2 ^ (prefixWord ++ tailWord_175251).sum := by decide
  have hdescent : baseEnd_175251 < baseStart_175251 := by decide
  rcases family_descends (prefixWord ++ tailWord_175251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175301 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_175301 : Nat := 118140960795 + 175301 * 2 ^ 59
def prefixEnd_175301 : Nat := 4983230072969 + 3 ^ 40 * 175301 * 2
def baseEnd_175301 : Nat := 90013672213923867731311

theorem tailTrace_175301 : CollatzResearch.WordTrace tailWord_175301 prefixEnd_175301 90013672213923867731311 := by
  unfold tailWord_175301
  simp only [CollatzResearch.WordTrace]
  refine ⟨6393752737921890872341757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4262501825281260581561171 6393752737921890872341757)
  ·
    refine ⟨2397657276720709077128159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6393752737921890872341757 2397657276720709077128159)
    ·
      refine ⟨3596485915081063615692239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397657276720709077128159 3596485915081063615692239)
      ·
        refine ⟨5394728872621595423538359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3596485915081063615692239 5394728872621595423538359)
        ·
          refine ⟨8092093308932393135307539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5394728872621595423538359 8092093308932393135307539)
          ·
            refine ⟨12138139963398589702961309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8092093308932393135307539 12138139963398589702961309)
            ·
              refine ⟨4551802486274471138610491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12138139963398589702961309 4551802486274471138610491)
              ·
                refine ⟨6827703729411706707915737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4551802486274471138610491 6827703729411706707915737)
                ·
                  refine ⟨5120777797058780030936803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6827703729411706707915737 5120777797058780030936803)
                  ·
                    refine ⟨7681166695588170046405205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5120777797058780030936803 7681166695588170046405205)
                    ·
                      refine ⟨90013672213923867731311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 7681166695588170046405205 90013672213923867731311)
                      ·
                        rfl

theorem cell23_175301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_175301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175301 prefixEnd_175301 := by exact prefixLift 175301
  have htrace : WordTrace (prefixWord ++ tailWord_175301) baseStart_175301 baseEnd_175301 := by
    simpa [prefixWord, tailWord_175301, baseEnd_175301] using wordTrace_append hprefix tailTrace_175301
  have hstable : (prefixWord ++ tailWord_175301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175301).length < 2 ^ (prefixWord ++ tailWord_175301).sum := by decide
  have hdescent : baseEnd_175301 < baseStart_175301 := by decide
  rcases family_descends (prefixWord ++ tailWord_175301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175328 : List Nat := [2, 1, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_175328 : Nat := 118140960795 + 175328 * 2 ^ 59
def prefixEnd_175328 : Nat := 4983230072969 + 3 ^ 40 * 175328 * 2
def baseEnd_175328 : Nat := 30009178730531754031229

theorem tailTrace_175328 : CollatzResearch.WordTrace tailWord_175328 prefixEnd_175328 30009178730531754031229 := by
  unfold tailWord_175328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197368754412037241787319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4263158339216049655716425 3197368754412037241787319)
  ·
    refine ⟨4796053131618055862680979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3197368754412037241787319 4796053131618055862680979)
    ·
      refine ⟨7194079697427083794021469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796053131618055862680979 7194079697427083794021469)
      ·
        refine ⟨2697779886535156422758051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7194079697427083794021469 2697779886535156422758051)
        ·
          refine ⟨4046669829802734634137077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697779886535156422758051 4046669829802734634137077)
          ·
            refine ⟨379375296544006371950351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4046669829802734634137077 379375296544006371950351)
            ·
              refine ⟨569062944816009557925527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379375296544006371950351 569062944816009557925527)
              ·
                refine ⟨853594417224014336888291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569062944816009557925527 853594417224014336888291)
                ·
                  refine ⟨1280391625836021505332437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 853594417224014336888291 1280391625836021505332437)
                  ·
                    refine ⟨30009178730531754031229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1280391625836021505332437 30009178730531754031229)
                    ·
                      rfl

theorem cell23_175328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_175328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175328 prefixEnd_175328 := by exact prefixLift 175328
  have htrace : WordTrace (prefixWord ++ tailWord_175328) baseStart_175328 baseEnd_175328 := by
    simpa [prefixWord, tailWord_175328, baseEnd_175328] using wordTrace_append hprefix tailTrace_175328
  have hstable : (prefixWord ++ tailWord_175328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175328).length < 2 ^ (prefixWord ++ tailWord_175328).sum := by decide
  have hdescent : baseEnd_175328 < baseStart_175328 := by decide
  rcases family_descends (prefixWord ++ tailWord_175328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175365 : List Nat := [1, 3, 1, 1, 2, 1, 3, 3, 2, 4, 2]
def baseStart_175365 : Nat := 118140960795 + 175365 * 2 ^ 59
def prefixEnd_175365 : Nat := 4983230072969 + 3 ^ 40 * 175365 * 2
def baseEnd_175365 : Nat := 90046534975811617331017

theorem tailTrace_175365 : CollatzResearch.WordTrace tailWord_175365 prefixEnd_175365 90046534975811617331017 := by
  unfold tailWord_175365
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396087009690029802671549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4264058006460019868447699 6396087009690029802671549)
  ·
    refine ⟨2398532628633761176001831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6396087009690029802671549 2398532628633761176001831)
    ·
      refine ⟨3597798942950641764002747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398532628633761176001831 3597798942950641764002747)
      ·
        refine ⟨5396698414425962646004121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597798942950641764002747 5396698414425962646004121)
        ·
          refine ⟨4047523810819471984503091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5396698414425962646004121 4047523810819471984503091)
          ·
            refine ⟨6071285716229207976754637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4047523810819471984503091 6071285716229207976754637)
            ·
              refine ⟨2276732143585952991282989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6071285716229207976754637 2276732143585952991282989)
              ·
                refine ⟨853774553844732371731121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2276732143585952991282989 853774553844732371731121)
                ·
                  refine ⟨640330915383549278798341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 853774553844732371731121 640330915383549278798341)
                  ·
                    refine ⟨120062046634415489774689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 640330915383549278798341 120062046634415489774689)
                    ·
                      refine ⟨90046534975811617331017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120062046634415489774689 90046534975811617331017)
                      ·
                        rfl

theorem cell23_175365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_175365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175365 prefixEnd_175365 := by exact prefixLift 175365
  have htrace : WordTrace (prefixWord ++ tailWord_175365) baseStart_175365 baseEnd_175365 := by
    simpa [prefixWord, tailWord_175365, baseEnd_175365] using wordTrace_append hprefix tailTrace_175365
  have hstable : (prefixWord ++ tailWord_175365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175365).length < 2 ^ (prefixWord ++ tailWord_175365).sum := by decide
  have hdescent : baseEnd_175365 < baseStart_175365 := by decide
  rcases family_descends (prefixWord ++ tailWord_175365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175388 : List Nat := [2, 2, 3, 1, 1, 1, 3, 2, 8]
def baseStart_175388 : Nat := 118140960795 + 175388 * 2 ^ 59
def prefixEnd_175388 : Nat := 4983230072969 + 3 ^ 40 * 175388 * 2
def baseEnd_175388 : Nat := 10006482781207225260379

theorem tailTrace_175388 : CollatzResearch.WordTrace tailWord_175388 prefixEnd_175388 10006482781207225260379 := by
  unfold tailWord_175388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3198462944303352365379409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4264617259071136487172545 3198462944303352365379409)
  ·
    refine ⟨2398847208227514274034557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3198462944303352365379409 2398847208227514274034557)
    ·
      refine ⟨899567703085317852762959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2398847208227514274034557 899567703085317852762959)
      ·
        refine ⟨1349351554627976779144439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899567703085317852762959 1349351554627976779144439)
        ·
          refine ⟨2024027331941965168716659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1349351554627976779144439 2024027331941965168716659)
          ·
            refine ⟨3036040997912947753074989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2024027331941965168716659 3036040997912947753074989)
            ·
              refine ⟨1138515374217355407403121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3036040997912947753074989 1138515374217355407403121)
              ·
                refine ⟨853886530663016555552341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1138515374217355407403121 853886530663016555552341)
                ·
                  refine ⟨10006482781207225260379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 853886530663016555552341 10006482781207225260379)
                  ·
                    rfl

theorem cell23_175388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_175388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175388 prefixEnd_175388 := by exact prefixLift 175388
  have htrace : WordTrace (prefixWord ++ tailWord_175388) baseStart_175388 baseEnd_175388 := by
    simpa [prefixWord, tailWord_175388, baseEnd_175388] using wordTrace_append hprefix tailTrace_175388
  have hstable : (prefixWord ++ tailWord_175388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175388).length < 2 ^ (prefixWord ++ tailWord_175388).sum := by decide
  have hdescent : baseEnd_175388 < baseStart_175388 := by decide
  rcases family_descends (prefixWord ++ tailWord_175388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175402 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_175402 : Nat := 118140960795 + 175402 * 2 ^ 59
def prefixEnd_175402 : Nat := 4983230072969 + 3 ^ 40 * 175402 * 2
def baseEnd_175402 : Nat := 90065533760027972568347

theorem tailTrace_175402 : CollatzResearch.WordTrace tailWord_175402 prefixEnd_175402 90065533760027972568347 := by
  unfold tailWord_175402
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599359127638996280442115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4264957673703990081178973 1599359127638996280442115)
  ·
    refine ⟨2399038691458494420663173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599359127638996280442115 2399038691458494420663173)
    ·
      refine ⟨449819754648467703874345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2399038691458494420663173 449819754648467703874345)
      ·
        refine ⟨337364815986350777905759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449819754648467703874345 337364815986350777905759)
        ·
          refine ⟨506047223979526166858639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337364815986350777905759 506047223979526166858639)
          ·
            refine ⟨759070835969289250287959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506047223979526166858639 759070835969289250287959)
            ·
              refine ⟨1138606253953933875431939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759070835969289250287959 1138606253953933875431939)
              ·
                refine ⟨1707909380930900813147909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138606253953933875431939 1707909380930900813147909)
                ·
                  refine ⟨320233008924543902465233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1707909380930900813147909 320233008924543902465233)
                  ·
                    refine ⟨240174756693407926848925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320233008924543902465233 240174756693407926848925)
                    ·
                      refine ⟨90065533760027972568347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240174756693407926848925 90065533760027972568347)
                      ·
                        rfl

theorem cell23_175402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_175402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175402 prefixEnd_175402 := by exact prefixLift 175402
  have htrace : WordTrace (prefixWord ++ tailWord_175402) baseStart_175402 baseEnd_175402 := by
    simpa [prefixWord, tailWord_175402, baseEnd_175402] using wordTrace_append hprefix tailTrace_175402
  have hstable : (prefixWord ++ tailWord_175402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175402).length < 2 ^ (prefixWord ++ tailWord_175402).sum := by decide
  have hdescent : baseEnd_175402 < baseStart_175402 := by decide
  rcases family_descends (prefixWord ++ tailWord_175402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175488 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_175488 : Nat := 118140960795 + 175488 * 2 ^ 59
def prefixEnd_175488 : Nat := 4983230072969 + 3 ^ 40 * 175488 * 2
def baseEnd_175488 : Nat := 90109693096314636092951

theorem tailTrace_175488 : CollatzResearch.WordTrace tailWord_175488 prefixEnd_175488 90109693096314636092951 := by
  unfold tailWord_175488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200286594122210904699559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4267048792162947872932745 3200286594122210904699559)
  ·
    refine ⟨4800429891183316357049339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3200286594122210904699559 4800429891183316357049339)
    ·
      refine ⟨7200644836774974535574009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4800429891183316357049339 7200644836774974535574009)
      ·
        refine ⟨5400483627581230901680507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7200644836774974535574009 5400483627581230901680507)
        ·
          refine ⟨8100725441371846352520761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5400483627581230901680507 8100725441371846352520761)
          ·
            refine ⟨6075544081028884764390571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8100725441371846352520761 6075544081028884764390571)
            ·
              refine ⟨9113316121543327146585857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075544081028884764390571 9113316121543327146585857)
              ·
                refine ⟨6834987091157495359939393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9113316121543327146585857 6834987091157495359939393)
                ·
                  refine ⟨5126240318368121519954545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6834987091157495359939393 5126240318368121519954545)
                  ·
                    refine ⟨3844680238776091139965909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5126240318368121519954545 3844680238776091139965909)
                    ·
                      refine ⟨90109693096314636092951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3844680238776091139965909 90109693096314636092951)
                      ·
                        rfl

theorem cell23_175488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_175488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175488 prefixEnd_175488 := by exact prefixLift 175488
  have htrace : WordTrace (prefixWord ++ tailWord_175488) baseStart_175488 baseEnd_175488 := by
    simpa [prefixWord, tailWord_175488, baseEnd_175488] using wordTrace_append hprefix tailTrace_175488
  have hstable : (prefixWord ++ tailWord_175488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175488).length < 2 ^ (prefixWord ++ tailWord_175488).sum := by decide
  have hdescent : baseEnd_175488 < baseStart_175488 := by decide
  rcases family_descends (prefixWord ++ tailWord_175488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175492 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_175492 : Nat := 118140960795 + 175492 * 2 ^ 59
def prefixEnd_175492 : Nat := 4983230072969 + 3 ^ 40 * 175492 * 2
def baseEnd_175492 : Nat := 90111747018932620442933

theorem tailTrace_175492 : CollatzResearch.WordTrace tailWord_175492 prefixEnd_175492 90111747018932620442933 := by
  unfold tailWord_175492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200359540114965246272365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4267146053486620328363153 3200359540114965246272365)
  ·
    refine ⟨1200134827543111967352137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3200359540114965246272365 1200134827543111967352137)
    ·
      refine ⟨900101120657333975514103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1200134827543111967352137 900101120657333975514103)
      ·
        refine ⟨1350151680986000963271155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900101120657333975514103 1350151680986000963271155)
        ·
          refine ⟨2025227521479001444906733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1350151680986000963271155 2025227521479001444906733)
          ·
            refine ⟨759460320554625541840025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2025227521479001444906733 759460320554625541840025)
            ·
              refine ⟨569595240415969156380019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759460320554625541840025 569595240415969156380019)
              ·
                refine ⟨854392860623953734570029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569595240415969156380019 854392860623953734570029)
                ·
                  refine ⟨320397322733982650463761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 854392860623953734570029 320397322733982650463761)
                  ·
                    refine ⟨240297992050486987847821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320397322733982650463761 240297992050486987847821)
                    ·
                      refine ⟨90111747018932620442933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240297992050486987847821 90111747018932620442933)
                      ·
                        rfl

theorem cell23_175492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_175492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175492 prefixEnd_175492 := by exact prefixLift 175492
  have htrace : WordTrace (prefixWord ++ tailWord_175492) baseStart_175492 baseEnd_175492 := by
    simpa [prefixWord, tailWord_175492, baseEnd_175492] using wordTrace_append hprefix tailTrace_175492
  have hstable : (prefixWord ++ tailWord_175492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175492).length < 2 ^ (prefixWord ++ tailWord_175492).sum := by decide
  have hdescent : baseEnd_175492 < baseStart_175492 := by decide
  rcases family_descends (prefixWord ++ tailWord_175492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175506 : List Nat := [3, 2, 3, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_175506 : Nat := 118140960795 + 175506 * 2 ^ 59
def prefixEnd_175506 : Nat := 4983230072969 + 3 ^ 40 * 175506 * 2
def baseEnd_175506 : Nat := 90118935748095565667869

theorem tailTrace_175506 : CollatzResearch.WordTrace tailWord_175506 prefixEnd_175506 90118935748095565667869 := by
  unfold tailWord_175506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600307425544802720888593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4267486468119473922369581 1600307425544802720888593)
  ·
    refine ⟨1200230569158602040666445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1600307425544802720888593 1200230569158602040666445)
    ·
      refine ⟨450086463434475765249917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1200230569158602040666445 450086463434475765249917)
      ·
        refine ⟨168782423787928411968719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 450086463434475765249917 168782423787928411968719)
        ·
          refine ⟨253173635681892617953079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168782423787928411968719 253173635681892617953079)
          ·
            refine ⟨379760453522838926929619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253173635681892617953079 379760453522838926929619)
            ·
              refine ⟨569640680284258390394429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379760453522838926929619 569640680284258390394429)
              ·
                refine ⟨213615255106596896397911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 569640680284258390394429 213615255106596896397911)
                ·
                  refine ⟨320422882659895344596867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213615255106596896397911 320422882659895344596867)
                  ·
                    refine ⟨480634323989843016895301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320422882659895344596867 480634323989843016895301)
                    ·
                      refine ⟨90118935748095565667869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 480634323989843016895301 90118935748095565667869)
                      ·
                        rfl

theorem cell23_175506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_175506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175506 prefixEnd_175506 := by exact prefixLift 175506
  have htrace : WordTrace (prefixWord ++ tailWord_175506) baseStart_175506 baseEnd_175506 := by
    simpa [prefixWord, tailWord_175506, baseEnd_175506] using wordTrace_append hprefix tailTrace_175506
  have hstable : (prefixWord ++ tailWord_175506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175506).length < 2 ^ (prefixWord ++ tailWord_175506).sum := by decide
  have hdescent : baseEnd_175506 < baseStart_175506 := by decide
  rcases family_descends (prefixWord ++ tailWord_175506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175509 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_175509 : Nat := 118140960795 + 175509 * 2 ^ 59
def prefixEnd_175509 : Nat := 4983230072969 + 3 ^ 40 * 175509 * 2
def baseEnd_175509 : Nat := 90120476190059053930355

theorem tailTrace_175509 : CollatzResearch.WordTrace tailWord_175509 prefixEnd_175509 90120476190059053930355 := by
  unfold tailWord_175509
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401339121168342395913581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4267559414112228263942387 6401339121168342395913581)
  ·
    refine ⟨2400502170438128398467593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6401339121168342395913581 2400502170438128398467593)
    ·
      refine ⟨1800376627828596298850695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2400502170438128398467593 1800376627828596298850695)
      ·
        refine ⟨2700564941742894448276043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800376627828596298850695 2700564941742894448276043)
        ·
          refine ⟨4050847412614341672414065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2700564941742894448276043 4050847412614341672414065)
          ·
            refine ⟨3038135559460756254310549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4050847412614341672414065 3038135559460756254310549)
            ·
              refine ⟨142412604349722949420807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3038135559460756254310549 142412604349722949420807)
              ·
                refine ⟨213618906524584424131211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142412604349722949420807 213618906524584424131211)
                ·
                  refine ⟨320428359786876636196817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213618906524584424131211 320428359786876636196817)
                  ·
                    refine ⟨240321269840157477147613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320428359786876636196817 240321269840157477147613)
                    ·
                      refine ⟨90120476190059053930355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240321269840157477147613 90120476190059053930355)
                      ·
                        rfl

theorem cell23_175509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_175509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175509 prefixEnd_175509 := by exact prefixLift 175509
  have htrace : WordTrace (prefixWord ++ tailWord_175509) baseStart_175509 baseEnd_175509 := by
    simpa [prefixWord, tailWord_175509, baseEnd_175509] using wordTrace_append hprefix tailTrace_175509
  have hstable : (prefixWord ++ tailWord_175509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175509).length < 2 ^ (prefixWord ++ tailWord_175509).sum := by decide
  have hdescent : baseEnd_175509 < baseStart_175509 := by decide
  rcases family_descends (prefixWord ++ tailWord_175509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175532 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_175532 : Nat := 118140960795 + 175532 * 2 ^ 59
def prefixEnd_175532 : Nat := 4983230072969 + 3 ^ 40 * 175532 * 2
def baseEnd_175532 : Nat := 90132286245112463942749

theorem tailTrace_175532 : CollatzResearch.WordTrace tailWord_175532 prefixEnd_175532 90132286245112463942749 := by
  unfold tailWord_175532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201089000042508662000425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4268118666723344882667233 3201089000042508662000425)
  ·
    refine ⟨2400816750031881496500319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3201089000042508662000425 2400816750031881496500319)
    ·
      refine ⟨3601225125047822244750479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400816750031881496500319 3601225125047822244750479)
      ·
        refine ⟨5401837687571733367125719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601225125047822244750479 5401837687571733367125719)
        ·
          refine ⟨8102756531357600050688579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5401837687571733367125719 8102756531357600050688579)
          ·
            refine ⟨12154134797036400076032869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8102756531357600050688579 12154134797036400076032869)
            ·
              refine ⟨2278900274444325014256163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12154134797036400076032869 2278900274444325014256163)
              ·
                refine ⟨3418350411666487521384245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2278900274444325014256163 3418350411666487521384245)
                ·
                  refine ⟨320470351093733205129773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418350411666487521384245 320470351093733205129773)
                  ·
                    refine ⟨120176381660149951923665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320470351093733205129773 120176381660149951923665)
                    ·
                      refine ⟨90132286245112463942749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120176381660149951923665 90132286245112463942749)
                      ·
                        rfl

theorem cell23_175532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_175532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175532 prefixEnd_175532 := by exact prefixLift 175532
  have htrace : WordTrace (prefixWord ++ tailWord_175532) baseStart_175532 baseEnd_175532 := by
    simpa [prefixWord, tailWord_175532, baseEnd_175532] using wordTrace_append hprefix tailTrace_175532
  have hstable : (prefixWord ++ tailWord_175532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175532).length < 2 ^ (prefixWord ++ tailWord_175532).sum := by decide
  have hdescent : baseEnd_175532 < baseStart_175532 := by decide
  rcases family_descends (prefixWord ++ tailWord_175532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175575 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4]
def baseStart_175575 : Nat := 118140960795 + 175575 * 2 ^ 59
def prefixEnd_175575 : Nat := 4983230072969 + 3 ^ 40 * 175575 * 2
def baseEnd_175575 : Nat := 90154365913255795705051

theorem tailTrace_175575 : CollatzResearch.WordTrace tailWord_175575 prefixEnd_175575 90154365913255795705051 := by
  unfold tailWord_175575
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403746338929235667816179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4269164225952823778544119 6403746338929235667816179)
  ·
    refine ⟨9605619508393853501724269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6403746338929235667816179 9605619508393853501724269)
    ·
      refine ⟨3602107315647695063146601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9605619508393853501724269 3602107315647695063146601)
      ·
        refine ⟨2701580486735771297359951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3602107315647695063146601 2701580486735771297359951)
        ·
          refine ⟨4052370730103656946039927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701580486735771297359951 4052370730103656946039927)
          ·
            refine ⟨6078556095155485419059891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4052370730103656946039927 6078556095155485419059891)
            ·
              refine ⟨9117834142733228128589837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6078556095155485419059891 9117834142733228128589837)
              ·
                refine ⟨3419187803524960548221189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9117834142733228128589837 3419187803524960548221189)
                ·
                  refine ⟨641097713160930102791473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3419187803524960548221189 641097713160930102791473)
                  ·
                    refine ⟨480823284870697577093605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 641097713160930102791473 480823284870697577093605)
                    ·
                      refine ⟨90154365913255795705051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 480823284870697577093605 90154365913255795705051)
                      ·
                        rfl

theorem cell23_175575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_175575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175575 prefixEnd_175575 := by exact prefixLift 175575
  have htrace : WordTrace (prefixWord ++ tailWord_175575) baseStart_175575 baseEnd_175575 := by
    simpa [prefixWord, tailWord_175575, baseEnd_175575] using wordTrace_append hprefix tailTrace_175575
  have hstable : (prefixWord ++ tailWord_175575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175575).length < 2 ^ (prefixWord ++ tailWord_175575).sum := by decide
  have hdescent : baseEnd_175575 < baseStart_175575 := by decide
  rcases family_descends (prefixWord ++ tailWord_175575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175625 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 5]
def baseStart_175625 : Nat := 118140960795 + 175625 * 2 ^ 59
def prefixEnd_175625 : Nat := 4983230072969 + 3 ^ 40 * 175625 * 2
def baseEnd_175625 : Nat := 90180039945980600079821

theorem tailTrace_175625 : CollatzResearch.WordTrace tailWord_175625 prefixEnd_175625 90180039945980600079821 := by
  unfold tailWord_175625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405569988748094207136329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4270379992498729471424219 6405569988748094207136329)
  ·
    refine ⟨4804177491561070655352247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6405569988748094207136329 4804177491561070655352247)
    ·
      refine ⟨7206266237341605983028371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804177491561070655352247 7206266237341605983028371)
      ·
        refine ⟨10809399356012408974542557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7206266237341605983028371 10809399356012408974542557)
        ·
          refine ⟨4053524758504653365453459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10809399356012408974542557 4053524758504653365453459)
          ·
            refine ⟨6080287137756980048180189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4053524758504653365453459 6080287137756980048180189)
            ·
              refine ⟨2280107676658867518067571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6080287137756980048180189 2280107676658867518067571)
              ·
                refine ⟨3420161514988301277101357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2280107676658867518067571 3420161514988301277101357)
                ·
                  refine ⟨1282560568120612978913009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3420161514988301277101357 1282560568120612978913009)
                  ·
                    refine ⟨961920426090459734184757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1282560568120612978913009 961920426090459734184757)
                    ·
                      refine ⟨90180039945980600079821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 961920426090459734184757 90180039945980600079821)
                      ·
                        rfl

theorem cell23_175625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 2, 5].length) (baseStart_175625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175625 prefixEnd_175625 := by exact prefixLift 175625
  have htrace : WordTrace (prefixWord ++ tailWord_175625) baseStart_175625 baseEnd_175625 := by
    simpa [prefixWord, tailWord_175625, baseEnd_175625] using wordTrace_append hprefix tailTrace_175625
  have hstable : (prefixWord ++ tailWord_175625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175625).length < 2 ^ (prefixWord ++ tailWord_175625).sum := by decide
  have hdescent : baseEnd_175625 < baseStart_175625 := by decide
  rcases family_descends (prefixWord ++ tailWord_175625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175669 : List Nat := [1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_175669 : Nat := 118140960795 + 175669 * 2 ^ 59
def prefixEnd_175669 : Nat := 4983230072969 + 3 ^ 40 * 175669 * 2
def baseEnd_175669 : Nat := 90202633094778427929619

theorem tailTrace_175669 : CollatzResearch.WordTrace tailWord_175669 prefixEnd_175669 90202633094778427929619 := by
  unfold tailWord_175669
  simp only [CollatzResearch.WordTrace]
  refine ⟨6407174800588689721738061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4271449867059126481158707 6407174800588689721738061)
  ·
    refine ⟨2402690550220758645651773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6407174800588689721738061 2402690550220758645651773)
    ·
      refine ⟨901008956332784492119415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2402690550220758645651773 901008956332784492119415)
      ·
        refine ⟨1351513434499176738179123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901008956332784492119415 1351513434499176738179123)
        ·
          refine ⟨2027270151748765107268685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351513434499176738179123 2027270151748765107268685)
          ·
            refine ⟨760226306905786915225757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2027270151748765107268685 760226306905786915225757)
            ·
              refine ⟨285084865089670093209659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 760226306905786915225757 285084865089670093209659)
              ·
                refine ⟨427627297634505139814489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285084865089670093209659 427627297634505139814489)
                ·
                  refine ⟨320720473225878854860867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 427627297634505139814489 320720473225878854860867)
                  ·
                    refine ⟨481080709838818282291301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320720473225878854860867 481080709838818282291301)
                    ·
                      refine ⟨90202633094778427929619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 481080709838818282291301 90202633094778427929619)
                      ·
                        rfl

theorem cell23_175669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_175669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175669 prefixEnd_175669 := by exact prefixLift 175669
  have htrace : WordTrace (prefixWord ++ tailWord_175669) baseStart_175669 baseEnd_175669 := by
    simpa [prefixWord, tailWord_175669, baseEnd_175669] using wordTrace_append hprefix tailTrace_175669
  have hstable : (prefixWord ++ tailWord_175669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175669).length < 2 ^ (prefixWord ++ tailWord_175669).sum := by decide
  have hdescent : baseEnd_175669 < baseStart_175669 := by decide
  rcases family_descends (prefixWord ++ tailWord_175669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175692 : List Nat := [2, 2, 1, 3, 1, 4, 1, 1, 8]
def baseStart_175692 : Nat := 118140960795 + 175692 * 2 ^ 59
def prefixEnd_175692 : Nat := 4983230072969 + 3 ^ 40 * 175692 * 2
def baseEnd_175692 : Nat := 10023827016647981993557

theorem tailTrace_175692 : CollatzResearch.WordTrace tailWord_175692 prefixEnd_175692 10023827016647981993557 := by
  unfold tailWord_175692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204006839752682324912665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4272009119670243099883553 3204006839752682324912665)
  ·
    refine ⟨2403005129814511743684499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3204006839752682324912665 2403005129814511743684499)
    ·
      refine ⟨3604507694721767615526749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2403005129814511743684499 3604507694721767615526749)
      ·
        refine ⟨1351690385520662855822531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3604507694721767615526749 1351690385520662855822531)
        ·
          refine ⟨2027535578280994283733797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351690385520662855822531 2027535578280994283733797)
          ·
            refine ⟨380162920927686428200087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2027535578280994283733797 380162920927686428200087)
            ·
              refine ⟨570244381391529642300131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380162920927686428200087 570244381391529642300131)
              ·
                refine ⟨855366572087294463450197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570244381391529642300131 855366572087294463450197)
                ·
                  refine ⟨10023827016647981993557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 855366572087294463450197 10023827016647981993557)
                  ·
                    rfl

theorem cell23_175692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_175692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175692 prefixEnd_175692 := by exact prefixLift 175692
  have htrace : WordTrace (prefixWord ++ tailWord_175692) baseStart_175692 baseEnd_175692 := by
    simpa [prefixWord, tailWord_175692, baseEnd_175692] using wordTrace_append hprefix tailTrace_175692
  have hstable : (prefixWord ++ tailWord_175692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175692).length < 2 ^ (prefixWord ++ tailWord_175692).sum := by decide
  have hdescent : baseEnd_175692 < baseStart_175692 := by decide
  rcases family_descends (prefixWord ++ tailWord_175692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175729 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 6, 3, 2]
def baseStart_175729 : Nat := 118140960795 + 175729 * 2 ^ 59
def prefixEnd_175729 : Nat := 4983230072969 + 3 ^ 40 * 175729 * 2
def baseEnd_175729 : Nat := 90233441934048193179343

theorem tailTrace_175729 : CollatzResearch.WordTrace tailWord_175729 prefixEnd_175729 90233441934048193179343 := by
  unfold tailWord_175729
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409363180371319968922241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4272908786914213312614827 6409363180371319968922241)
  ·
    refine ⟨4807022385278489976691681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6409363180371319968922241 4807022385278489976691681)
    ·
      refine ⟨3605266788958867482518761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4807022385278489976691681 3605266788958867482518761)
      ·
        refine ⟨2703950091719150611889071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3605266788958867482518761 2703950091719150611889071)
        ·
          refine ⟨4055925137578725917833607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2703950091719150611889071 4055925137578725917833607)
          ·
            refine ⟨6083887706368088876750411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4055925137578725917833607 6083887706368088876750411)
            ·
              refine ⟨9125831559552133315125617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083887706368088876750411 9125831559552133315125617)
              ·
                refine ⟨6844373669664099986344213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9125831559552133315125617 6844373669664099986344213)
                ·
                  refine ⟨320830015765504686859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6844373669664099986344213 320830015765504686859885)
                  ·
                    refine ⟨120311255912064257572457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320830015765504686859885 120311255912064257572457)
                    ·
                      refine ⟨90233441934048193179343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120311255912064257572457 90233441934048193179343)
                      ·
                        rfl

theorem cell23_175729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_175729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175729 prefixEnd_175729 := by exact prefixLift 175729
  have htrace : WordTrace (prefixWord ++ tailWord_175729) baseStart_175729 baseEnd_175729 := by
    simpa [prefixWord, tailWord_175729, baseEnd_175729] using wordTrace_append hprefix tailTrace_175729
  have hstable : (prefixWord ++ tailWord_175729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175729).length < 2 ^ (prefixWord ++ tailWord_175729).sum := by decide
  have hdescent : baseEnd_175729 < baseStart_175729 := by decide
  rcases family_descends (prefixWord ++ tailWord_175729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175776 : List Nat := [2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_175776 : Nat := 118140960795 + 175776 * 2 ^ 59
def prefixEnd_175776 : Nat := 4983230072969 + 3 ^ 40 * 175776 * 2
def baseEnd_175776 : Nat := 90257575524809509291627

theorem tailTrace_175776 : CollatzResearch.WordTrace tailWord_175776 prefixEnd_175776 90257575524809509291627 := by
  unfold tailWord_175776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3205538705600523497941591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4274051607467364663922121 3205538705600523497941591)
  ·
    refine ⟨4808308058400785246912387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3205538705600523497941591 4808308058400785246912387)
    ·
      refine ⟨7212462087601177870368581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808308058400785246912387 7212462087601177870368581)
      ·
        refine ⟨1352336641425220850694109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7212462087601177870368581 1352336641425220850694109)
        ·
          refine ⟨507126240534457819010291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1352336641425220850694109 507126240534457819010291)
          ·
            refine ⟨760689360801686728515437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507126240534457819010291 760689360801686728515437)
            ·
              refine ⟨285258510300632523193289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 760689360801686728515437 285258510300632523193289)
              ·
                refine ⟨213943882725474392394967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285258510300632523193289 213943882725474392394967)
                ·
                  refine ⟨320915824088211588592451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213943882725474392394967 320915824088211588592451)
                  ·
                    refine ⟨481373736132317382888677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320915824088211588592451 481373736132317382888677)
                    ·
                      refine ⟨90257575524809509291627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 481373736132317382888677 90257575524809509291627)
                      ·
                        rfl

theorem cell23_175776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_175776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175776 prefixEnd_175776 := by exact prefixLift 175776
  have htrace : WordTrace (prefixWord ++ tailWord_175776) baseStart_175776 baseEnd_175776 := by
    simpa [prefixWord, tailWord_175776, baseEnd_175776] using wordTrace_append hprefix tailTrace_175776
  have hstable : (prefixWord ++ tailWord_175776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175776).length < 2 ^ (prefixWord ++ tailWord_175776).sum := by decide
  have hdescent : baseEnd_175776 < baseStart_175776 := by decide
  rcases family_descends (prefixWord ++ tailWord_175776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175779 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3]
def baseStart_175779 : Nat := 118140960795 + 175779 * 2 ^ 59
def prefixEnd_175779 : Nat := 4983230072969 + 3 ^ 40 * 175779 * 2
def baseEnd_175779 : Nat := 90259115966772997554113

theorem tailTrace_175779 : CollatzResearch.WordTrace tailWord_175779 prefixEnd_175779 90259115966772997554113 := by
  unfold tailWord_175779
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411186830190178508242391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4274124553460119005494927 6411186830190178508242391)
  ·
    refine ⟨9616780245285267762363587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411186830190178508242391 9616780245285267762363587)
    ·
      refine ⟨14425170367927901643545381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9616780245285267762363587 14425170367927901643545381)
      ·
        refine ⟨2704719443986481558164759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14425170367927901643545381 2704719443986481558164759)
        ·
          refine ⟨4057079165979722337247139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704719443986481558164759 4057079165979722337247139)
          ·
            refine ⟨6085618748969583505870709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4057079165979722337247139 6085618748969583505870709)
            ·
              refine ⟨570526757715898453675379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6085618748969583505870709 570526757715898453675379)
              ·
                refine ⟨855790136573847680513069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570526757715898453675379 855790136573847680513069)
                ·
                  refine ⟨320921301215192880192401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 855790136573847680513069 320921301215192880192401)
                  ·
                    refine ⟨240690975911394660144301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 320921301215192880192401 240690975911394660144301)
                    ·
                      refine ⟨90259115966772997554113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240690975911394660144301 90259115966772997554113)
                      ·
                        rfl

theorem cell23_175779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_175779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175779 prefixEnd_175779 := by exact prefixLift 175779
  have htrace : WordTrace (prefixWord ++ tailWord_175779) baseStart_175779 baseEnd_175779 := by
    simpa [prefixWord, tailWord_175779, baseEnd_175779] using wordTrace_append hprefix tailTrace_175779
  have hstable : (prefixWord ++ tailWord_175779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175779).length < 2 ^ (prefixWord ++ tailWord_175779).sum := by decide
  have hdescent : baseEnd_175779 < baseStart_175779 := by decide
  rcases family_descends (prefixWord ++ tailWord_175779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175790 : List Nat := [4, 1, 4, 1, 2, 1, 3, 1, 1, 5]
def baseStart_175790 : Nat := 118140960795 + 175790 * 2 ^ 59
def prefixEnd_175790 : Nat := 4983230072969 + 3 ^ 40 * 175790 * 2
def baseEnd_175790 : Nat := 30088254751324151505521

theorem tailTrace_175790 : CollatzResearch.WordTrace tailWord_175790 prefixEnd_175790 30088254751324151505521 := by
  unfold tailWord_175790
  simp only [CollatzResearch.WordTrace]
  refine ⟨801448504143790923361603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4274392022100218257928549 801448504143790923361603)
  ·
    refine ⟨1202172756215686385042405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 801448504143790923361603 1202172756215686385042405)
    ·
      refine ⟨225407391790441197195451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1202172756215686385042405 225407391790441197195451)
      ·
        refine ⟨338111087685661795793177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225407391790441197195451 338111087685661795793177)
        ·
          refine ⟨253583315764246346844883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338111087685661795793177 253583315764246346844883)
          ·
            refine ⟨380374973646369520267325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253583315764246346844883 380374973646369520267325)
            ·
              refine ⟨142640615117388570100247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 380374973646369520267325 142640615117388570100247)
              ·
                refine ⟨213960922676082855150371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142640615117388570100247 213960922676082855150371)
                ·
                  refine ⟨320941384014124282725557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213960922676082855150371 320941384014124282725557)
                  ·
                    refine ⟨30088254751324151505521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 320941384014124282725557 30088254751324151505521)
                    ·
                      rfl

theorem cell23_175790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_175790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175790 prefixEnd_175790 := by exact prefixLift 175790
  have htrace : WordTrace (prefixWord ++ tailWord_175790) baseStart_175790 baseEnd_175790 := by
    simpa [prefixWord, tailWord_175790, baseEnd_175790] using wordTrace_append hprefix tailTrace_175790
  have hstable : (prefixWord ++ tailWord_175790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175790).length < 2 ^ (prefixWord ++ tailWord_175790).sum := by decide
  have hdescent : baseEnd_175790 < baseStart_175790 := by decide
  rcases family_descends (prefixWord ++ tailWord_175790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175826 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_175826 : Nat := 118140960795 + 175826 * 2 ^ 59
def prefixEnd_175826 : Nat := 4983230072969 + 3 ^ 40 * 175826 * 2
def baseEnd_175826 : Nat := 90283249557534313666397

theorem tailTrace_175826 : CollatzResearch.WordTrace tailWord_175826 prefixEnd_175826 90283249557534313666397 := by
  unfold tailWord_175826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1603225265254976383800833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4275267374013270356802221 1603225265254976383800833)
  ·
    refine ⟨1202418948941232287850625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1603225265254976383800833 1202418948941232287850625)
    ·
      refine ⟨901814211705924215887969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1202418948941232287850625 901814211705924215887969)
      ·
        refine ⟨676360658779443161915977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 901814211705924215887969 676360658779443161915977)
        ·
          refine ⟨507270494084582371436983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676360658779443161915977 507270494084582371436983)
          ·
            refine ⟨760905741126873557155475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507270494084582371436983 760905741126873557155475)
            ·
              refine ⟨1141358611690310335733213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 760905741126873557155475 1141358611690310335733213)
              ·
                refine ⟨428009479383866375899955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1141358611690310335733213 428009479383866375899955)
                ·
                  refine ⟨642014219075799563849933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 428009479383866375899955 642014219075799563849933)
                  ·
                    refine ⟨240755332153424836443725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 642014219075799563849933 240755332153424836443725)
                    ·
                      refine ⟨90283249557534313666397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240755332153424836443725 90283249557534313666397)
                      ·
                        rfl

theorem cell23_175826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_175826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175826 prefixEnd_175826 := by exact prefixLift 175826
  have htrace : WordTrace (prefixWord ++ tailWord_175826) baseStart_175826 baseEnd_175826 := by
    simpa [prefixWord, tailWord_175826, baseEnd_175826] using wordTrace_append hprefix tailTrace_175826
  have hstable : (prefixWord ++ tailWord_175826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175826).length < 2 ^ (prefixWord ++ tailWord_175826).sum := by decide
  have hdescent : baseEnd_175826 < baseStart_175826 := by decide
  rcases family_descends (prefixWord ++ tailWord_175826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175847 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 1, 2, 3]
def baseStart_175847 : Nat := 118140960795 + 175847 * 2 ^ 59
def prefixEnd_175847 : Nat := 4983230072969 + 3 ^ 40 * 175847 * 2
def baseEnd_175847 : Nat := 90294032651278731503801

theorem tailTrace_175847 : CollatzResearch.WordTrace tailWord_175847 prefixEnd_175847 90294032651278731503801 := by
  unfold tailWord_175847
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413666993943826121717795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4275777995962550747811863 6413666993943826121717795)
  ·
    refine ⟨9620500490915739182576693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6413666993943826121717795 9620500490915739182576693)
    ·
      refine ⟨901921921023350548366565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9620500490915739182576693 901921921023350548366565)
      ·
        refine ⟨169110360191878227818731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 901921921023350548366565 169110360191878227818731)
        ·
          refine ⟨253665540287817341728097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169110360191878227818731 253665540287817341728097)
          ·
            refine ⟨190249155215863006296073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 253665540287817341728097 190249155215863006296073)
            ·
              refine ⟨142686866411897254722055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190249155215863006296073 142686866411897254722055)
              ·
                refine ⟨214030299617845882083083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142686866411897254722055 214030299617845882083083)
                ·
                  refine ⟨321045449426768823124625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214030299617845882083083 321045449426768823124625)
                  ·
                    refine ⟨240784087070076617343469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321045449426768823124625 240784087070076617343469)
                    ·
                      refine ⟨90294032651278731503801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240784087070076617343469 90294032651278731503801)
                      ·
                        rfl

theorem cell23_175847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_175847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175847 prefixEnd_175847 := by exact prefixLift 175847
  have htrace : WordTrace (prefixWord ++ tailWord_175847) baseStart_175847 baseEnd_175847 := by
    simpa [prefixWord, tailWord_175847, baseEnd_175847] using wordTrace_append hprefix tailTrace_175847
  have hstable : (prefixWord ++ tailWord_175847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175847).length < 2 ^ (prefixWord ++ tailWord_175847).sum := by decide
  have hdescent : baseEnd_175847 < baseStart_175847 := by decide
  rcases family_descends (prefixWord ++ tailWord_175847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175869 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 3]
def baseStart_175869 : Nat := 118140960795 + 175869 * 2 ^ 59
def prefixEnd_175869 : Nat := 4983230072969 + 3 ^ 40 * 175869 * 2
def baseEnd_175869 : Nat := 90305329225677645428699

theorem tailTrace_175869 : CollatzResearch.WordTrace tailWord_175869 prefixEnd_175869 90305329225677645428699 := by
  unfold tailWord_175869
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414469399864123879018661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276312933242749252679107 6414469399864123879018661)
  ·
    refine ⟨1202713012474523227315999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6414469399864123879018661 1202713012474523227315999)
    ·
      refine ⟨1804069518711784840973999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1202713012474523227315999 1804069518711784840973999)
      ·
        refine ⟨2706104278067677261460999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804069518711784840973999 2706104278067677261460999)
        ·
          refine ⟨4059156417101515892191499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2706104278067677261460999 4059156417101515892191499)
          ·
            refine ⟨6088734625652273838287249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4059156417101515892191499 6088734625652273838287249)
            ·
              refine ⟨4566550969239205378715437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6088734625652273838287249 4566550969239205378715437)
              ·
                refine ⟨1712456613464702017018289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4566550969239205378715437 1712456613464702017018289)
                ·
                  refine ⟨1284342460098526512763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1712456613464702017018289 1284342460098526512763717)
                  ·
                    refine ⟨240814211268473721143197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1284342460098526512763717 240814211268473721143197)
                    ·
                      refine ⟨90305329225677645428699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 240814211268473721143197 90305329225677645428699)
                      ·
                        rfl

theorem cell23_175869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_175869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175869 prefixEnd_175869 := by exact prefixLift 175869
  have htrace : WordTrace (prefixWord ++ tailWord_175869) baseStart_175869 baseEnd_175869 := by
    simpa [prefixWord, tailWord_175869, baseEnd_175869] using wordTrace_append hprefix tailTrace_175869
  have hstable : (prefixWord ++ tailWord_175869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175869).length < 2 ^ (prefixWord ++ tailWord_175869).sum := by decide
  have hdescent : baseEnd_175869 < baseStart_175869 := by decide
  rcases family_descends (prefixWord ++ tailWord_175869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175872 : List Nat := [2, 1, 1, 2, 1, 1, 2, 2, 11]
def baseStart_175872 : Nat := 118140960795 + 175872 * 2 ^ 59
def prefixEnd_175872 : Nat := 4983230072969 + 3 ^ 40 * 175872 * 2
def baseEnd_175872 : Nat := 10034096629737903743465

theorem tailTrace_175872 : CollatzResearch.WordTrace tailWord_175872 prefixEnd_175872 10034096629737903743465 := by
  unfold tailWord_175872
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207289409426627695688935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4276385879235503594251913 3207289409426627695688935)
  ·
    refine ⟨4810934114139941543533403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207289409426627695688935 4810934114139941543533403)
    ·
      refine ⟨7216401171209912315300105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4810934114139941543533403 7216401171209912315300105)
      ·
        refine ⟨5412300878407434236475079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7216401171209912315300105 5412300878407434236475079)
        ·
          refine ⟨8118451317611151354712619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5412300878407434236475079 8118451317611151354712619)
          ·
            refine ⟨12177676976416727032068929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8118451317611151354712619 12177676976416727032068929)
            ·
              refine ⟨9133257732312545274051697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12177676976416727032068929 9133257732312545274051697)
              ·
                refine ⟨6849943299234408955538773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9133257732312545274051697 6849943299234408955538773)
                ·
                  refine ⟨10034096629737903743465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 6849943299234408955538773 10034096629737903743465)
                  ·
                    rfl

theorem cell23_175872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_175872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175872 prefixEnd_175872 := by exact prefixLift 175872
  have htrace : WordTrace (prefixWord ++ tailWord_175872) baseStart_175872 baseEnd_175872 := by
    simpa [prefixWord, tailWord_175872, baseEnd_175872] using wordTrace_append hprefix tailTrace_175872
  have hstable : (prefixWord ++ tailWord_175872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175872).length < 2 ^ (prefixWord ++ tailWord_175872).sum := by decide
  have hdescent : baseEnd_175872 < baseStart_175872 := by decide
  rcases family_descends (prefixWord ++ tailWord_175872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175883 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 2, 2, 2]
def baseStart_175883 : Nat := 118140960795 + 175883 * 2 ^ 59
def prefixEnd_175883 : Nat := 4983230072969 + 3 ^ 40 * 175883 * 2
def baseEnd_175883 : Nat := 90312517954840590653635

theorem tailTrace_175883 : CollatzResearch.WordTrace tailWord_175883 prefixEnd_175883 90312517954840590653635 := by
  unfold tailWord_175883
  simp only [CollatzResearch.WordTrace]
  refine ⟨6414980021813404270028303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4276653347875602846685535 6414980021813404270028303)
  ·
    refine ⟨9622470032720106405042455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6414980021813404270028303 9622470032720106405042455)
    ·
      refine ⟨14433705049080159607563683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9622470032720106405042455 14433705049080159607563683)
      ·
        refine ⟨21650557573620239411345525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14433705049080159607563683 21650557573620239411345525)
        ·
          refine ⟨2029739772526897444813643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21650557573620239411345525 2029739772526897444813643)
          ·
            refine ⟨3044609658790346167220465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029739772526897444813643 3044609658790346167220465)
            ·
              refine ⟨2283457244092759625415349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3044609658790346167220465 2283457244092759625415349)
              ·
                refine ⟨214074116633696214882689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2283457244092759625415349 214074116633696214882689)
                ·
                  refine ⟨160555587475272161162017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214074116633696214882689 160555587475272161162017)
                  ·
                    refine ⟨120416690606454120871513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160555587475272161162017 120416690606454120871513)
                    ·
                      refine ⟨90312517954840590653635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120416690606454120871513 90312517954840590653635)
                      ·
                        rfl

theorem cell23_175883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2, 2].length) (baseStart_175883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175883 prefixEnd_175883 := by exact prefixLift 175883
  have htrace : WordTrace (prefixWord ++ tailWord_175883) baseStart_175883 baseEnd_175883 := by
    simpa [prefixWord, tailWord_175883, baseEnd_175883] using wordTrace_append hprefix tailTrace_175883
  have hstable : (prefixWord ++ tailWord_175883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175883).length < 2 ^ (prefixWord ++ tailWord_175883).sum := by decide
  have hdescent : baseEnd_175883 < baseStart_175883 := by decide
  rcases family_descends (prefixWord ++ tailWord_175883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175919 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 2, 5]
def baseStart_175919 : Nat := 118140960795 + 175919 * 2 ^ 59
def prefixEnd_175919 : Nat := 4983230072969 + 3 ^ 40 * 175919 * 2
def baseEnd_175919 : Nat := 30110334419467483267823

theorem tailTrace_175919 : CollatzResearch.WordTrace tailWord_175919 prefixEnd_175919 30110334419467483267823 := by
  unfold tailWord_175919
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416293049682982418338811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4277528699788654945559207 6416293049682982418338811)
  ·
    refine ⟨9624439574524473627508217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6416293049682982418338811 9624439574524473627508217)
    ·
      refine ⟨7218329680893355220631163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9624439574524473627508217 7218329680893355220631163)
      ·
        refine ⟨10827494521340032830946745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218329680893355220631163 10827494521340032830946745)
        ·
          refine ⟨8120620891005024623210059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10827494521340032830946745 8120620891005024623210059)
          ·
            refine ⟨12180931336507536934815089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8120620891005024623210059 12180931336507536934815089)
            ·
              refine ⟨9135698502380652701111317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12180931336507536934815089 9135698502380652701111317)
              ·
                refine ⟨428235867299093095364593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9135698502380652701111317 428235867299093095364593)
                ·
                  refine ⟨321176900474319821523445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 428235867299093095364593 321176900474319821523445)
                  ·
                    refine ⟨30110334419467483267823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 321176900474319821523445 30110334419467483267823)
                    ·
                      rfl

theorem cell23_175919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 5].length) (baseStart_175919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175919 prefixEnd_175919 := by exact prefixLift 175919
  have htrace : WordTrace (prefixWord ++ tailWord_175919) baseStart_175919 baseEnd_175919 := by
    simpa [prefixWord, tailWord_175919, baseEnd_175919] using wordTrace_append hprefix tailTrace_175919
  have hstable : (prefixWord ++ tailWord_175919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175919).length < 2 ^ (prefixWord ++ tailWord_175919).sum := by decide
  have hdescent : baseEnd_175919 < baseStart_175919 := by decide
  rcases family_descends (prefixWord ++ tailWord_175919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175923 : List Nat := [1, 1, 1, 2, 8, 1, 1, 1, 7]
def baseStart_175923 : Nat := 118140960795 + 175923 * 2 ^ 59
def prefixEnd_175923 : Nat := 4983230072969 + 3 ^ 40 * 175923 * 2
def baseEnd_175923 : Nat := 10037006353446714905939

theorem tailTrace_175923 : CollatzResearch.WordTrace tailWord_175923 prefixEnd_175923 10037006353446714905939 := by
  unfold tailWord_175923
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416438941668491101484423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4277625961112327400989615 6416438941668491101484423)
  ·
    refine ⟨9624658412502736652226635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6416438941668491101484423 9624658412502736652226635)
    ·
      refine ⟨14436987618754104978339953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9624658412502736652226635 14436987618754104978339953)
      ·
        refine ⟨10827740714065578733754965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14436987618754104978339953 10827740714065578733754965)
        ·
          refine ⟨126887586492956000786191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 10827740714065578733754965 126887586492956000786191)
          ·
            refine ⟨190331379739434001179287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126887586492956000786191 190331379739434001179287)
            ·
              refine ⟨285497069609151001768931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190331379739434001179287 285497069609151001768931)
              ·
                refine ⟨428245604413726502653397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285497069609151001768931 428245604413726502653397)
                ·
                  refine ⟨10037006353446714905939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 428245604413726502653397 10037006353446714905939)
                  ·
                    rfl

theorem cell23_175923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 7].length) (baseStart_175923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175923 prefixEnd_175923 := by exact prefixLift 175923
  have htrace : WordTrace (prefixWord ++ tailWord_175923) baseStart_175923 baseEnd_175923 := by
    simpa [prefixWord, tailWord_175923, baseEnd_175923] using wordTrace_append hprefix tailTrace_175923
  have hstable : (prefixWord ++ tailWord_175923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175923).length < 2 ^ (prefixWord ++ tailWord_175923).sum := by decide
  have hdescent : baseEnd_175923 < baseStart_175923 := by decide
  rcases family_descends (prefixWord ++ tailWord_175923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175934 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_175934 : Nat := 118140960795 + 175934 * 2 ^ 59
def prefixEnd_175934 : Nat := 4983230072969 + 3 ^ 40 * 175934 * 2
def baseEnd_175934 : Nat := 90338705468219891115901

theorem tailTrace_175934 : CollatzResearch.WordTrace tailWord_175934 prefixEnd_175934 90338705468219891115901 := by
  unfold tailWord_175934
  simp only [CollatzResearch.WordTrace]
  refine ⟨802105018078579997516857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4277893429752426653423237 802105018078579997516857)
  ·
    refine ⟨601578763558934998137643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 802105018078579997516857 601578763558934998137643)
    ·
      refine ⟨902368145338402497206465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601578763558934998137643 902368145338402497206465)
      ·
        refine ⟨676776109003801872904849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 902368145338402497206465 676776109003801872904849)
        ·
          refine ⟨507582081752851404678637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676776109003801872904849 507582081752851404678637)
          ·
            refine ⟨190343280657319276754489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 507582081752851404678637 190343280657319276754489)
            ·
              refine ⟨142757460492989457565867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190343280657319276754489 142757460492989457565867)
              ·
                refine ⟨214136190739484186348801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142757460492989457565867 214136190739484186348801)
                ·
                  refine ⟨160602143054613139761601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214136190739484186348801 160602143054613139761601)
                  ·
                    refine ⟨120451607290959854821201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160602143054613139761601 120451607290959854821201)
                    ·
                      refine ⟨90338705468219891115901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120451607290959854821201 90338705468219891115901)
                      ·
                        rfl

theorem cell23_175934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_175934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175934 prefixEnd_175934 := by exact prefixLift 175934
  have htrace : WordTrace (prefixWord ++ tailWord_175934) baseStart_175934 baseEnd_175934 := by
    simpa [prefixWord, tailWord_175934, baseEnd_175934] using wordTrace_append hprefix tailTrace_175934
  have hstable : (prefixWord ++ tailWord_175934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175934).length < 2 ^ (prefixWord ++ tailWord_175934).sum := by decide
  have hdescent : baseEnd_175934 < baseStart_175934 := by decide
  rcases family_descends (prefixWord ++ tailWord_175934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_175969 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 6]
def baseStart_175969 : Nat := 118140960795 + 175969 * 2 ^ 59
def prefixEnd_175969 : Nat := 4983230072969 + 3 ^ 40 * 175969 * 2
def baseEnd_175969 : Nat := 90356677291127254178239

theorem tailTrace_175969 : CollatzResearch.WordTrace tailWord_175969 prefixEnd_175969 90356677291127254178239 := by
  unfold tailWord_175969
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418116699501840957658961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4278744466334560638439307 6418116699501840957658961)
  ·
    refine ⟨4813587524626380718244221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6418116699501840957658961 4813587524626380718244221)
    ·
      refine ⟨1805095321734892769341583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4813587524626380718244221 1805095321734892769341583)
      ·
        refine ⟨2707642982602339154012375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805095321734892769341583 2707642982602339154012375)
        ·
          refine ⟨4061464473903508731018563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2707642982602339154012375 4061464473903508731018563)
          ·
            refine ⟨6092196710855263096527845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4061464473903508731018563 6092196710855263096527845)
            ·
              refine ⟨1142286883285361830598971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6092196710855263096527845 1142286883285361830598971)
              ·
                refine ⟨1713430324928042745898457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1142286883285361830598971 1713430324928042745898457)
                ·
                  refine ⟨1285072743696032059423843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1713430324928042745898457 1285072743696032059423843)
                  ·
                    refine ⟨1927609115544048089135765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1285072743696032059423843 1927609115544048089135765)
                    ·
                      refine ⟨90356677291127254178239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1927609115544048089135765 90356677291127254178239)
                      ·
                        rfl

theorem cell23_175969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_175969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_175969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_175969 prefixEnd_175969 := by exact prefixLift 175969
  have htrace : WordTrace (prefixWord ++ tailWord_175969) baseStart_175969 baseEnd_175969 := by
    simpa [prefixWord, tailWord_175969, baseEnd_175969] using wordTrace_append hprefix tailTrace_175969
  have hstable : (prefixWord ++ tailWord_175969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_175969).length < 2 ^ (prefixWord ++ tailWord_175969).sum := by decide
  have hdescent : baseEnd_175969 < baseStart_175969 := by decide
  rcases family_descends (prefixWord ++ tailWord_175969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176030 : List Nat := [4, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_176030 : Nat := 118140960795 + 176030 * 2 ^ 59
def prefixEnd_176030 : Nat := 4983230072969 + 3 ^ 40 * 176030 * 2
def baseEnd_176030 : Nat := 10043111067894612835051

theorem tailTrace_176030 : CollatzResearch.WordTrace tailWord_176030 prefixEnd_176030 10043111067894612835051 := by
  unfold tailWord_176030
  simp only [CollatzResearch.WordTrace]
  refine ⟨802542694035106046953693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4280227701520565583753029 802542694035106046953693)
  ·
    refine ⟨300953510263164767607635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 802542694035106046953693 300953510263164767607635)
    ·
      refine ⟨451430265394747151411453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300953510263164767607635 451430265394747151411453)
      ·
        refine ⟨169286349523030181779295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 451430265394747151411453 169286349523030181779295)
        ·
          refine ⟨253929524284545272668943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169286349523030181779295 253929524284545272668943)
          ·
            refine ⟨380894286426817909003415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253929524284545272668943 380894286426817909003415)
            ·
              refine ⟨571341429640226863505123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380894286426817909003415 571341429640226863505123)
              ·
                refine ⟨857012144460340295257685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571341429640226863505123 857012144460340295257685)
                ·
                  refine ⟨10043111067894612835051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 857012144460340295257685 10043111067894612835051)
                  ·
                    rfl

theorem cell23_176030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_176030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176030 prefixEnd_176030 := by exact prefixLift 176030
  have htrace : WordTrace (prefixWord ++ tailWord_176030) baseStart_176030 baseEnd_176030 := by
    simpa [prefixWord, tailWord_176030, baseEnd_176030] using wordTrace_append hprefix tailTrace_176030
  have hstable : (prefixWord ++ tailWord_176030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176030).length < 2 ^ (prefixWord ++ tailWord_176030).sum := by decide
  have hdescent : baseEnd_176030 < baseStart_176030 := by decide
  rcases family_descends (prefixWord ++ tailWord_176030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176063 : List Nat := [1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 4]
def baseStart_176063 : Nat := 118140960795 + 176063 * 2 ^ 59
def prefixEnd_176063 : Nat := 4983230072969 + 3 ^ 40 * 176063 * 2
def baseEnd_176063 : Nat := 90404944472649886402807

theorem tailTrace_176063 : CollatzResearch.WordTrace tailWord_176063 prefixEnd_176063 90404944472649886402807 := by
  unfold tailWord_176063
  simp only [CollatzResearch.WordTrace]
  refine ⟨6421545161161295011580843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4281030107440863341053895 6421545161161295011580843)
  ·
    refine ⟨9632317741741942517371265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6421545161161295011580843 9632317741741942517371265)
    ·
      refine ⟨7224238306306456888028449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9632317741741942517371265 7224238306306456888028449)
      ·
        refine ⟨5418178729729842666021337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7224238306306456888028449 5418178729729842666021337)
        ·
          refine ⟨4063634047297381999516003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5418178729729842666021337 4063634047297381999516003)
          ·
            refine ⟨6095451070946072999274005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063634047297381999516003 6095451070946072999274005)
            ·
              refine ⟨285724268950597171840969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6095451070946072999274005 285724268950597171840969)
              ·
                refine ⟨214293201712947878880727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285724268950597171840969 214293201712947878880727)
                ·
                  refine ⟨321439802569421818321091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214293201712947878880727 321439802569421818321091)
                  ·
                    refine ⟨482159703854132727481637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321439802569421818321091 482159703854132727481637)
                    ·
                      refine ⟨90404944472649886402807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 482159703854132727481637 90404944472649886402807)
                      ·
                        rfl

theorem cell23_176063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_176063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176063 prefixEnd_176063 := by exact prefixLift 176063
  have htrace : WordTrace (prefixWord ++ tailWord_176063) baseStart_176063 baseEnd_176063 := by
    simpa [prefixWord, tailWord_176063, baseEnd_176063] using wordTrace_append hprefix tailTrace_176063
  have hstable : (prefixWord ++ tailWord_176063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176063).length < 2 ^ (prefixWord ++ tailWord_176063).sum := by decide
  have hdescent : baseEnd_176063 < baseStart_176063 := by decide
  rcases family_descends (prefixWord ++ tailWord_176063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176097 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 1, 2, 2]
def baseStart_176097 : Nat := 118140960795 + 176097 * 2 ^ 59
def prefixEnd_176097 : Nat := 4983230072969 + 3 ^ 40 * 176097 * 2
def baseEnd_176097 : Nat := 90422402814902753377651

theorem tailTrace_176097 : CollatzResearch.WordTrace tailWord_176097 prefixEnd_176097 90422402814902753377651 := by
  unfold tailWord_176097
  simp only [CollatzResearch.WordTrace]
  refine ⟨6422785243038118818318545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4281856828692079212212363 6422785243038118818318545)
  ·
    refine ⟨4817088932278589113738909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6422785243038118818318545 4817088932278589113738909)
    ·
      refine ⟨1806408349604470917652091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4817088932278589113738909 1806408349604470917652091)
      ·
        refine ⟨2709612524406706376478137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1806408349604470917652091 2709612524406706376478137)
        ·
          refine ⟨2032209393305029782358603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2709612524406706376478137 2032209393305029782358603)
          ·
            refine ⟨3048314089957544673537905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2032209393305029782358603 3048314089957544673537905)
            ·
              refine ⟨2286235567468158505153429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3048314089957544673537905 2286235567468158505153429)
              ·
                refine ⟨107167292225069929929067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2286235567468158505153429 107167292225069929929067)
                ·
                  refine ⟨160750938337604894893601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107167292225069929929067 160750938337604894893601)
                  ·
                    refine ⟨120563203753203671170201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160750938337604894893601 120563203753203671170201)
                    ·
                      refine ⟨90422402814902753377651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120563203753203671170201 90422402814902753377651)
                      ·
                        rfl

theorem cell23_176097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_176097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176097 prefixEnd_176097 := by exact prefixLift 176097
  have htrace : WordTrace (prefixWord ++ tailWord_176097) baseStart_176097 baseEnd_176097 := by
    simpa [prefixWord, tailWord_176097, baseEnd_176097] using wordTrace_append hprefix tailTrace_176097
  have hstable : (prefixWord ++ tailWord_176097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176097).length < 2 ^ (prefixWord ++ tailWord_176097).sum := by decide
  have hdescent : baseEnd_176097 < baseStart_176097 := by decide
  rcases family_descends (prefixWord ++ tailWord_176097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176103 : List Nat := [1, 1, 5, 2, 3, 1, 2, 8]
def baseStart_176103 : Nat := 118140960795 + 176103 * 2 ^ 59
def prefixEnd_176103 : Nat := 4983230072969 + 3 ^ 40 * 176103 * 2
def baseEnd_176103 : Nat := 3349091988845545551949

theorem tailTrace_176103 : CollatzResearch.WordTrace tailWord_176103 prefixEnd_176103 3349091988845545551949 := by
  unfold tailWord_176103
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423004081016381843036963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4282002720677587895357975 6423004081016381843036963)
  ·
    refine ⟨9634506121524572764555445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6423004081016381843036963 9634506121524572764555445)
    ·
      refine ⟨903234948892928696677073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9634506121524572764555445 903234948892928696677073)
      ·
        refine ⟨677426211669696522507805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 903234948892928696677073 677426211669696522507805)
        ·
          refine ⟨254034829376136195940427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677426211669696522507805 254034829376136195940427)
          ·
            refine ⟨381052244064204293910641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254034829376136195940427 381052244064204293910641)
            ·
              refine ⟨285789183048153220432981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381052244064204293910641 285789183048153220432981)
              ·
                refine ⟨3349091988845545551949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 285789183048153220432981 3349091988845545551949)
                ·
                  rfl

theorem cell23_176103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 8].length) (baseStart_176103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176103 prefixEnd_176103 := by exact prefixLift 176103
  have htrace : WordTrace (prefixWord ++ tailWord_176103) baseStart_176103 baseEnd_176103 := by
    simpa [prefixWord, tailWord_176103, baseEnd_176103] using wordTrace_append hprefix tailTrace_176103
  have hstable : (prefixWord ++ tailWord_176103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176103).length < 2 ^ (prefixWord ++ tailWord_176103).sum := by decide
  have hdescent : baseEnd_176103 < baseStart_176103 := by decide
  rcases family_descends (prefixWord ++ tailWord_176103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176106 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_176106 : Nat := 118140960795 + 176106 * 2 ^ 59
def prefixEnd_176106 : Nat := 4983230072969 + 3 ^ 40 * 176106 * 2
def baseEnd_176106 : Nat := 90427024140793218165109

theorem tailTrace_176106 : CollatzResearch.WordTrace tailWord_176106 prefixEnd_176106 90427024140793218165109 := by
  unfold tailWord_176106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1605778375001378338849043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4282075666670342236930781 1605778375001378338849043)
  ·
    refine ⟨2408667562502067508273565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1605778375001378338849043 2408667562502067508273565)
    ·
      refine ⟨903250335938275315602587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2408667562502067508273565 903250335938275315602587)
      ·
        refine ⟨1354875503907412973403881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903250335938275315602587 1354875503907412973403881)
        ·
          refine ⟨1016156627930559730052911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1354875503907412973403881 1016156627930559730052911)
          ·
            refine ⟨1524234941895839595079367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1016156627930559730052911 1524234941895839595079367)
            ·
              refine ⟨2286352412843759392619051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1524234941895839595079367 2286352412843759392619051)
              ·
                refine ⟨3429528619265639088928577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286352412843759392619051 3429528619265639088928577)
                ·
                  refine ⟨2572146464449229316696433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3429528619265639088928577 2572146464449229316696433)
                  ·
                    refine ⟨1929109848336921987522325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2572146464449229316696433 1929109848336921987522325)
                    ·
                      refine ⟨90427024140793218165109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1929109848336921987522325 90427024140793218165109)
                      ·
                        rfl

theorem cell23_176106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_176106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176106 prefixEnd_176106 := by exact prefixLift 176106
  have htrace : WordTrace (prefixWord ++ tailWord_176106) baseStart_176106 baseEnd_176106 := by
    simpa [prefixWord, tailWord_176106, baseEnd_176106] using wordTrace_append hprefix tailTrace_176106
  have hstable : (prefixWord ++ tailWord_176106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176106).length < 2 ^ (prefixWord ++ tailWord_176106).sum := by decide
  have hdescent : baseEnd_176106 < baseStart_176106 := by decide
  rcases family_descends (prefixWord ++ tailWord_176106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176141 : List Nat := [1, 7, 1, 2, 1, 1, 2, 2, 2, 4]
def baseStart_176141 : Nat := 118140960795 + 176141 * 2 ^ 59
def prefixEnd_176141 : Nat := 4983230072969 + 3 ^ 40 * 176141 * 2
def baseEnd_176141 : Nat := 30148331987900193742483

theorem tailTrace_176141 : CollatzResearch.WordTrace tailWord_176141 prefixEnd_176141 30148331987900193742483 := by
  unfold tailWord_176141
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424390054878714332920277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4282926703252476221946851 6424390054878714332920277)
  ·
    refine ⟨150571641911219867177819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 6424390054878714332920277 150571641911219867177819)
    ·
      refine ⟨225857462866829800766729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150571641911219867177819 225857462866829800766729)
      ·
        refine ⟨169393097150122350575047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225857462866829800766729 169393097150122350575047)
        ·
          refine ⟨254089645725183525862571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169393097150122350575047 254089645725183525862571)
          ·
            refine ⟨381134468587775288793857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254089645725183525862571 381134468587775288793857)
            ·
              refine ⟨285850851440831466595393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381134468587775288793857 285850851440831466595393)
              ·
                refine ⟨214388138580623599946545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285850851440831466595393 214388138580623599946545)
                ·
                  refine ⟨160791103935467699959909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214388138580623599946545 160791103935467699959909)
                  ·
                    refine ⟨30148331987900193742483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160791103935467699959909 30148331987900193742483)
                    ·
                      rfl

theorem cell23_176141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_176141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176141 prefixEnd_176141 := by exact prefixLift 176141
  have htrace : WordTrace (prefixWord ++ tailWord_176141) baseStart_176141 baseEnd_176141 := by
    simpa [prefixWord, tailWord_176141, baseEnd_176141] using wordTrace_append hprefix tailTrace_176141
  have hstable : (prefixWord ++ tailWord_176141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176141).length < 2 ^ (prefixWord ++ tailWord_176141).sum := by decide
  have hdescent : baseEnd_176141 < baseStart_176141 := by decide
  rcases family_descends (prefixWord ++ tailWord_176141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176148 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_176148 : Nat := 118140960795 + 176148 * 2 ^ 59
def prefixEnd_176148 : Nat := 4983230072969 + 3 ^ 40 * 176148 * 2
def baseEnd_176148 : Nat := 90448590328282053839917

theorem tailTrace_176148 : CollatzResearch.WordTrace tailWord_176148 prefixEnd_176148 90448590328282053839917 := by
  unfold tailWord_176148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212322682926677264212549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4283096910568903018950065 3212322682926677264212549)
  ·
    refine ⟨602310503048751987039853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3212322682926677264212549 602310503048751987039853)
    ·
      refine ⟨225866438643281995139945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 602310503048751987039853 225866438643281995139945)
      ·
        refine ⟨169399828982461496354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 225866438643281995139945 169399828982461496354959)
        ·
          refine ⟨254099743473692244532439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169399828982461496354959 254099743473692244532439)
          ·
            refine ⟨381149615210538366798659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254099743473692244532439 381149615210538366798659)
            ·
              refine ⟨571724422815807550197989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381149615210538366798659 571724422815807550197989)
              ·
                refine ⟨107198329277963915662123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 571724422815807550197989 107198329277963915662123)
                ·
                  refine ⟨160797493916945873493185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107198329277963915662123 160797493916945873493185)
                  ·
                    refine ⟨120598120437709405119889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160797493916945873493185 120598120437709405119889)
                    ·
                      refine ⟨90448590328282053839917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120598120437709405119889 90448590328282053839917)
                      ·
                        rfl

theorem cell23_176148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_176148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176148 prefixEnd_176148 := by exact prefixLift 176148
  have htrace : WordTrace (prefixWord ++ tailWord_176148) baseStart_176148 baseEnd_176148 := by
    simpa [prefixWord, tailWord_176148, baseEnd_176148] using wordTrace_append hprefix tailTrace_176148
  have hstable : (prefixWord ++ tailWord_176148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176148).length < 2 ^ (prefixWord ++ tailWord_176148).sum := by decide
  have hdescent : baseEnd_176148 < baseStart_176148 := by decide
  rcases family_descends (prefixWord ++ tailWord_176148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176153 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 5, 4, 2]
def baseStart_176153 : Nat := 118140960795 + 176153 * 2 ^ 59
def prefixEnd_176153 : Nat := 4983230072969 + 3 ^ 40 * 176153 * 2
def baseEnd_176153 : Nat := 90451157731554534277393

theorem tailTrace_176153 : CollatzResearch.WordTrace tailWord_176153 prefixEnd_176153 90451157731554534277393 := by
  unfold tailWord_176153
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424827730835240382357113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4283218487223493588238075 6424827730835240382357113)
  ·
    refine ⟨4818620798126430286767835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6424827730835240382357113 4818620798126430286767835)
    ·
      refine ⟨7227931197189645430151753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4818620798126430286767835 7227931197189645430151753)
      ·
        refine ⟨5420948397892234072613815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7227931197189645430151753 5420948397892234072613815)
        ·
          refine ⟨8131422596838351108920723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420948397892234072613815 8131422596838351108920723)
          ·
            refine ⟨12197133895257526663381085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8131422596838351108920723 12197133895257526663381085)
            ·
              refine ⟨4573925210721572498767907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12197133895257526663381085 4573925210721572498767907)
              ·
                refine ⟨6860887816082358748151861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4573925210721572498767907 6860887816082358748151861)
                ·
                  refine ⟨643208232757721132639237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6860887816082358748151861 643208232757721132639237)
                  ·
                    refine ⟨120601543642072712369857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 643208232757721132639237 120601543642072712369857)
                    ·
                      refine ⟨90451157731554534277393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120601543642072712369857 90451157731554534277393)
                      ·
                        rfl

theorem cell23_176153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4, 2].length) (baseStart_176153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176153 prefixEnd_176153 := by exact prefixLift 176153
  have htrace : WordTrace (prefixWord ++ tailWord_176153) baseStart_176153 baseEnd_176153 := by
    simpa [prefixWord, tailWord_176153, baseEnd_176153] using wordTrace_append hprefix tailTrace_176153
  have hstable : (prefixWord ++ tailWord_176153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176153).length < 2 ^ (prefixWord ++ tailWord_176153).sum := by decide
  have hdescent : baseEnd_176153 < baseStart_176153 := by decide
  rcases family_descends (prefixWord ++ tailWord_176153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176176 : List Nat := [2, 1, 1, 1, 2, 5, 1, 1, 9]
def baseStart_176176 : Nat := 118140960795 + 176176 * 2 ^ 59
def prefixEnd_176176 : Nat := 4983230072969 + 3 ^ 40 * 176176 * 2
def baseEnd_176176 : Nat := 10051440865178660476643

theorem tailTrace_176176 : CollatzResearch.WordTrace tailWord_176176 prefixEnd_176176 10051440865178660476643 := by
  unfold tailWord_176176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212833304875957655222191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4283777739834610206962921 3212833304875957655222191)
  ·
    refine ⟨4819249957313936482833287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3212833304875957655222191 4819249957313936482833287)
    ·
      refine ⟨7228874935970904724249931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4819249957313936482833287 7228874935970904724249931)
      ·
        refine ⟨10843312403956357086374897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7228874935970904724249931 10843312403956357086374897)
        ·
          refine ⟨8132484302967267814781173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10843312403956357086374897 8132484302967267814781173)
          ·
            refine ⟨762420403403181357635735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8132484302967267814781173 762420403403181357635735)
            ·
              refine ⟨1143630605104772036453603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 762420403403181357635735 1143630605104772036453603)
              ·
                refine ⟨1715445907657158054680405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1143630605104772036453603 1715445907657158054680405)
                ·
                  refine ⟨10051440865178660476643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1715445907657158054680405 10051440865178660476643)
                  ·
                    rfl

theorem cell23_176176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_176176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176176 prefixEnd_176176 := by exact prefixLift 176176
  have htrace : WordTrace (prefixWord ++ tailWord_176176) baseStart_176176 baseEnd_176176 := by
    simpa [prefixWord, tailWord_176176, baseEnd_176176] using wordTrace_append hprefix tailTrace_176176
  have hstable : (prefixWord ++ tailWord_176176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176176).length < 2 ^ (prefixWord ++ tailWord_176176).sum := by decide
  have hdescent : baseEnd_176176 < baseStart_176176 := by decide
  rcases family_descends (prefixWord ++ tailWord_176176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176186 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_176186 : Nat := 118140960795 + 176186 * 2 ^ 59
def prefixEnd_176186 : Nat := 4983230072969 + 3 ^ 40 * 176186 * 2
def baseEnd_176186 : Nat := 90468102593152905164741

theorem tailTrace_176186 : CollatzResearch.WordTrace tailWord_176186 prefixEnd_176186 90468102593152905164741 := by
  unfold tailWord_176186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606507834928921754577103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4284020893143791345538941 1606507834928921754577103)
  ·
    refine ⟨2409761752393382631865655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1606507834928921754577103 2409761752393382631865655)
    ·
      refine ⟨3614642628590073947798483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2409761752393382631865655 3614642628590073947798483)
      ·
        refine ⟨5421963942885110921697725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3614642628590073947798483 5421963942885110921697725)
        ·
          refine ⟨2033236478581916595636647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5421963942885110921697725 2033236478581916595636647)
          ·
            refine ⟨3049854717872874893454971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2033236478581916595636647 3049854717872874893454971)
            ·
              refine ⟨4574782076809312340182457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3049854717872874893454971 4574782076809312340182457)
              ·
                refine ⟨3431086557606984255136843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4574782076809312340182457 3431086557606984255136843)
                ·
                  refine ⟨5146629836410476382705265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3431086557606984255136843 5146629836410476382705265)
                  ·
                    refine ⟨3859972377307857287028949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5146629836410476382705265 3859972377307857287028949)
                    ·
                      refine ⟨90468102593152905164741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3859972377307857287028949 90468102593152905164741)
                      ·
                        rfl

theorem cell23_176186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_176186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176186 prefixEnd_176186 := by exact prefixLift 176186
  have htrace : WordTrace (prefixWord ++ tailWord_176186) baseStart_176186 baseEnd_176186 := by
    simpa [prefixWord, tailWord_176186, baseEnd_176186] using wordTrace_append hprefix tailTrace_176186
  have hstable : (prefixWord ++ tailWord_176186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176186).length < 2 ^ (prefixWord ++ tailWord_176186).sum := by decide
  have hdescent : baseEnd_176186 < baseStart_176186 := by decide
  rcases family_descends (prefixWord ++ tailWord_176186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176210 : List Nat := [3, 2, 2, 1, 4, 1, 2, 1, 7]
def baseStart_176210 : Nat := 118140960795 + 176210 * 2 ^ 59
def prefixEnd_176210 : Nat := 4983230072969 + 3 ^ 40 * 176210 * 2
def baseEnd_176210 : Nat := 10053380680984534584959

theorem tailTrace_176210 : CollatzResearch.WordTrace tailWord_176210 prefixEnd_176210 10053380680984534584959 := by
  unfold tailWord_176210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606726672907184779295521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4284604461085826078121389 1606726672907184779295521)
  ·
    refine ⟨1205045004680388584471641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1606726672907184779295521 1205045004680388584471641)
    ·
      refine ⟨903783753510291438353731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1205045004680388584471641 903783753510291438353731)
      ·
        refine ⟨1355675630265437157530597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 903783753510291438353731 1355675630265437157530597)
        ·
          refine ⟨254189180674769467036987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1355675630265437157530597 254189180674769467036987)
          ·
            refine ⟨381283771012154200555481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254189180674769467036987 381283771012154200555481)
            ·
              refine ⟨285962828259115650416611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381283771012154200555481 285962828259115650416611)
              ·
                refine ⟨428944242388673475624917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285962828259115650416611 428944242388673475624917)
                ·
                  refine ⟨10053380680984534584959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 428944242388673475624917 10053380680984534584959)
                  ·
                    rfl

theorem cell23_176210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_176210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176210 prefixEnd_176210 := by exact prefixLift 176210
  have htrace : WordTrace (prefixWord ++ tailWord_176210) baseStart_176210 baseEnd_176210 := by
    simpa [prefixWord, tailWord_176210, baseEnd_176210] using wordTrace_append hprefix tailTrace_176210
  have hstable : (prefixWord ++ tailWord_176210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176210).length < 2 ^ (prefixWord ++ tailWord_176210).sum := by decide
  have hdescent : baseEnd_176210 < baseStart_176210 := by decide
  rcases family_descends (prefixWord ++ tailWord_176210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176220 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_176220 : Nat := 118140960795 + 176220 * 2 ^ 59
def prefixEnd_176220 : Nat := 4983230072969 + 3 ^ 40 * 176220 * 2
def baseEnd_176220 : Nat := 90485560935405772139585

theorem tailTrace_176220 : CollatzResearch.WordTrace tailWord_176220 prefixEnd_176220 90485560935405772139585 := by
  unfold tailWord_176220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3213635710796255412523057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4284847614395007216697409 3213635710796255412523057)
  ·
    refine ⟨2410226783097191559392293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3213635710796255412523057 2410226783097191559392293)
    ·
      refine ⟨451917521830723417386055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2410226783097191559392293 451917521830723417386055)
      ·
        refine ⟨677876282746085126079083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451917521830723417386055 677876282746085126079083)
        ·
          refine ⟨1016814424119127689118625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677876282746085126079083 1016814424119127689118625)
          ·
            refine ⟨762610818089345766838969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016814424119127689118625 762610818089345766838969)
            ·
              refine ⟨571958113567009325129227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762610818089345766838969 571958113567009325129227)
              ·
                refine ⟨857937170350513987693841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 571958113567009325129227 857937170350513987693841)
                ·
                  refine ⟨643452877762885490770381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 857937170350513987693841 643452877762885490770381)
                  ·
                    refine ⟨241294829161082059038893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 643452877762885490770381 241294829161082059038893)
                    ·
                      refine ⟨90485560935405772139585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241294829161082059038893 90485560935405772139585)
                      ·
                        rfl

theorem cell23_176220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_176220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176220 prefixEnd_176220 := by exact prefixLift 176220
  have htrace : WordTrace (prefixWord ++ tailWord_176220) baseStart_176220 baseEnd_176220 := by
    simpa [prefixWord, tailWord_176220, baseEnd_176220] using wordTrace_append hprefix tailTrace_176220
  have hstable : (prefixWord ++ tailWord_176220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176220).length < 2 ^ (prefixWord ++ tailWord_176220).sum := by decide
  have hdescent : baseEnd_176220 < baseStart_176220 := by decide
  rcases family_descends (prefixWord ++ tailWord_176220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176260 : List Nat := [2, 3, 2, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_176260 : Nat := 118140960795 + 176260 * 2 ^ 59
def prefixEnd_176260 : Nat := 4983230072969 + 3 ^ 40 * 176260 * 2
def baseEnd_176260 : Nat := 90506100161585615639401

theorem tailTrace_176260 : CollatzResearch.WordTrace tailWord_176260 prefixEnd_176260 90506100161585615639401 := by
  unfold tailWord_176260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3214365170723798828251117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4285820227631731771001489 3214365170723798828251117)
  ·
    refine ⟨1205386939021424560594169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3214365170723798828251117 1205386939021424560594169)
    ·
      refine ⟨904040204266068420445627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1205386939021424560594169 904040204266068420445627)
      ·
        refine ⟨1356060306399102630668441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904040204266068420445627 1356060306399102630668441)
        ·
          refine ⟨1017045229799326973001331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356060306399102630668441 1017045229799326973001331)
          ·
            refine ⟨1525567844698990459501997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017045229799326973001331 1525567844698990459501997)
            ·
              refine ⟨572087941762121422313249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1525567844698990459501997 572087941762121422313249)
              ·
                refine ⟨429065956321591066734937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572087941762121422313249 429065956321591066734937)
                ·
                  refine ⟨321799467241193300051203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429065956321591066734937 321799467241193300051203)
                  ·
                    refine ⟨482699200861789950076805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321799467241193300051203 482699200861789950076805)
                    ·
                      refine ⟨90506100161585615639401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 482699200861789950076805 90506100161585615639401)
                      ·
                        rfl

theorem cell23_176260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_176260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176260 prefixEnd_176260 := by exact prefixLift 176260
  have htrace : WordTrace (prefixWord ++ tailWord_176260) baseStart_176260 baseEnd_176260 := by
    simpa [prefixWord, tailWord_176260, baseEnd_176260] using wordTrace_append hprefix tailTrace_176260
  have hstable : (prefixWord ++ tailWord_176260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176260).length < 2 ^ (prefixWord ++ tailWord_176260).sum := by decide
  have hdescent : baseEnd_176260 < baseStart_176260 := by decide
  rcases family_descends (prefixWord ++ tailWord_176260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176321 : List Nat := [1, 2, 6, 1, 2, 1, 1, 4, 1, 4]
def baseStart_176321 : Nat := 118140960795 + 176321 * 2 ^ 59
def prefixEnd_176321 : Nat := 4983230072969 + 3 ^ 40 * 176321 * 2
def baseEnd_176321 : Nat := 30179140827169958992207

theorem tailTrace_176321 : CollatzResearch.WordTrace tailWord_176321 prefixEnd_176321 30179140827169958992207 := by
  unfold tailWord_176321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6430955194226605074472817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4287303462817736716315211 6430955194226605074472817)
  ·
    refine ⟨4823216395669953805854613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6430955194226605074472817 4823216395669953805854613)
    ·
      refine ⟨226088268547029084649435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4823216395669953805854613 226088268547029084649435)
      ·
        refine ⟨339132402820543626974153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226088268547029084649435 339132402820543626974153)
        ·
          refine ⟨254349302115407720230615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 339132402820543626974153 254349302115407720230615)
          ·
            refine ⟨381523953173111580345923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254349302115407720230615 381523953173111580345923)
            ·
              refine ⟨572285929759667370518885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381523953173111580345923 572285929759667370518885)
              ·
                refine ⟨107303611829937631972291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 572285929759667370518885 107303611829937631972291)
                ·
                  refine ⟨160955417744906447958437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107303611829937631972291 160955417744906447958437)
                  ·
                    refine ⟨30179140827169958992207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160955417744906447958437 30179140827169958992207)
                    ·
                      rfl

theorem cell23_176321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_176321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176321 prefixEnd_176321 := by exact prefixLift 176321
  have htrace : WordTrace (prefixWord ++ tailWord_176321) baseStart_176321 baseEnd_176321 := by
    simpa [prefixWord, tailWord_176321, baseEnd_176321] using wordTrace_append hprefix tailTrace_176321
  have hstable : (prefixWord ++ tailWord_176321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176321).length < 2 ^ (prefixWord ++ tailWord_176321).sum := by decide
  have hdescent : baseEnd_176321 < baseStart_176321 := by decide
  rcases family_descends (prefixWord ++ tailWord_176321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176348 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_176348 : Nat := 118140960795 + 176348 * 2 ^ 59
def prefixEnd_176348 : Nat := 4983230072969 + 3 ^ 40 * 176348 * 2
def baseEnd_176348 : Nat := 90551286459181271338997

theorem tailTrace_176348 : CollatzResearch.WordTrace tailWord_176348 prefixEnd_176348 90551286459181271338997 := by
  unfold tailWord_176348
  simp only [CollatzResearch.WordTrace]
  refine ⟨3215969982564394342852849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4287959976752525790470465 3215969982564394342852849)
  ·
    refine ⟨2411977486923295757139637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3215969982564394342852849 2411977486923295757139637)
    ·
      refine ⟨226122889399058977231841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2411977486923295757139637 226122889399058977231841)
      ·
        refine ⟨169592167049294232923881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226122889399058977231841 169592167049294232923881)
        ·
          refine ⟨127194125286970674692911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169592167049294232923881 127194125286970674692911)
          ·
            refine ⟨190791187930456012039367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127194125286970674692911 190791187930456012039367)
            ·
              refine ⟨286186781895684018059051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190791187930456012039367 286186781895684018059051)
              ·
                refine ⟨429280172843526027088577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286186781895684018059051 429280172843526027088577)
                ·
                  refine ⟨321960129632644520316433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429280172843526027088577 321960129632644520316433)
                  ·
                    refine ⟨241470097224483390237325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 321960129632644520316433 241470097224483390237325)
                    ·
                      refine ⟨90551286459181271338997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241470097224483390237325 90551286459181271338997)
                      ·
                        rfl

theorem cell23_176348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_176348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176348 prefixEnd_176348 := by exact prefixLift 176348
  have htrace : WordTrace (prefixWord ++ tailWord_176348) baseStart_176348 baseEnd_176348 := by
    simpa [prefixWord, tailWord_176348, baseEnd_176348] using wordTrace_append hprefix tailTrace_176348
  have hstable : (prefixWord ++ tailWord_176348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176348).length < 2 ^ (prefixWord ++ tailWord_176348).sum := by decide
  have hdescent : baseEnd_176348 < baseStart_176348 := by decide
  rcases family_descends (prefixWord ++ tailWord_176348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176360 : List Nat := [2, 1, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_176360 : Nat := 118140960795 + 176360 * 2 ^ 59
def prefixEnd_176360 : Nat := 4983230072969 + 3 ^ 40 * 176360 * 2
def baseEnd_176360 : Nat := 30185816075678408129647

theorem tailTrace_176360 : CollatzResearch.WordTrace tailWord_176360 prefixEnd_176360 30185816075678408129647 := by
  unfold tailWord_176360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3216188820542657367571267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4288251760723543156761689 3216188820542657367571267)
  ·
    refine ⟨4824283230813986051356901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3216188820542657367571267 4824283230813986051356901)
    ·
      refine ⟨904553105777622384629419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4824283230813986051356901 904553105777622384629419)
      ·
        refine ⟨1356829658666433576944129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904553105777622384629419 1356829658666433576944129)
        ·
          refine ⟨1017622243999825182708097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1356829658666433576944129 1017622243999825182708097)
          ·
            refine ⟨763216682999868887031073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1017622243999825182708097 763216682999868887031073)
            ·
              refine ⟨572412512249901665273305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 763216682999868887031073 572412512249901665273305)
              ·
                refine ⟨429309384187426248954979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 572412512249901665273305 429309384187426248954979)
                ·
                  refine ⟨643964076281139373432469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429309384187426248954979 643964076281139373432469)
                  ·
                    refine ⟨30185816075678408129647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 643964076281139373432469 30185816075678408129647)
                    ·
                      rfl

theorem cell23_176360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_176360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176360 prefixEnd_176360 := by exact prefixLift 176360
  have htrace : WordTrace (prefixWord ++ tailWord_176360) baseStart_176360 baseEnd_176360 := by
    simpa [prefixWord, tailWord_176360, baseEnd_176360] using wordTrace_append hprefix tailTrace_176360
  have hstable : (prefixWord ++ tailWord_176360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176360).length < 2 ^ (prefixWord ++ tailWord_176360).sum := by decide
  have hdescent : baseEnd_176360 < baseStart_176360 := by decide
  rcases family_descends (prefixWord ++ tailWord_176360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176367 : List Nat := [1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 4]
def baseStart_176367 : Nat := 118140960795 + 176367 * 2 ^ 59
def prefixEnd_176367 : Nat := 4983230072969 + 3 ^ 40 * 176367 * 2
def baseEnd_176367 : Nat := 90561042591616697001409

theorem tailTrace_176367 : CollatzResearch.WordTrace tailWord_176367 prefixEnd_176367 90561042591616697001409 := by
  unfold tailWord_176367
  simp only [CollatzResearch.WordTrace]
  refine ⟨6432632952059954930647355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4288421968039969953764903 6432632952059954930647355)
  ·
    refine ⟨9648949428089932395971033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6432632952059954930647355 9648949428089932395971033)
    ·
      refine ⟨7236712071067449296978275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9648949428089932395971033 7236712071067449296978275)
      ·
        refine ⟨10855068106601173945467413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7236712071067449296978275 10855068106601173945467413)
        ·
          refine ⟨508831317496930028693785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10855068106601173945467413 508831317496930028693785)
          ·
            refine ⟨381623488122697521520339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508831317496930028693785 381623488122697521520339)
            ·
              refine ⟨572435232184046282280509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381623488122697521520339 572435232184046282280509)
              ·
                refine ⟨214663212069017355855191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572435232184046282280509 214663212069017355855191)
                ·
                  refine ⟨321994818103526033782787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 214663212069017355855191 321994818103526033782787)
                  ·
                    refine ⟨482992227155289050674181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 321994818103526033782787 482992227155289050674181)
                    ·
                      refine ⟨90561042591616697001409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 482992227155289050674181 90561042591616697001409)
                      ·
                        rfl

theorem cell23_176367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 1, 4].length) (baseStart_176367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176367 prefixEnd_176367 := by exact prefixLift 176367
  have htrace : WordTrace (prefixWord ++ tailWord_176367) baseStart_176367 baseEnd_176367 := by
    simpa [prefixWord, tailWord_176367, baseEnd_176367] using wordTrace_append hprefix tailTrace_176367
  have hstable : (prefixWord ++ tailWord_176367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176367).length < 2 ^ (prefixWord ++ tailWord_176367).sum := by decide
  have hdescent : baseEnd_176367 < baseStart_176367 := by decide
  rcases family_descends (prefixWord ++ tailWord_176367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176403 : List Nat := [1, 1, 1, 2, 1, 3, 1, 4, 2, 7]
def baseStart_176403 : Nat := 118140960795 + 176403 * 2 ^ 59
def prefixEnd_176403 : Nat := 4983230072969 + 3 ^ 40 * 176403 * 2
def baseEnd_176403 : Nat := 30193175965059518717081

theorem tailTrace_176403 : CollatzResearch.WordTrace tailWord_176403 prefixEnd_176403 30193175965059518717081 := by
  unfold tailWord_176403
  simp only [CollatzResearch.WordTrace]
  refine ⟨6433945979929533078957863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289297319953022052638575 6433945979929533078957863)
  ·
    refine ⟨9650918969894299618436795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6433945979929533078957863 9650918969894299618436795)
    ·
      refine ⟨14476378454841449427655193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9650918969894299618436795 14476378454841449427655193)
      ·
        refine ⟨10857283841131087070741395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14476378454841449427655193 10857283841131087070741395)
        ·
          refine ⟨16285925761696630606112093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10857283841131087070741395 16285925761696630606112093)
          ·
            refine ⟨6107222160636236477292035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16285925761696630606112093 6107222160636236477292035)
            ·
              refine ⟨9160833240954354715938053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6107222160636236477292035 9160833240954354715938053)
              ·
                refine ⟨1717656232678941509238385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9160833240954354715938053 1717656232678941509238385)
                ·
                  refine ⟨1288242174509206131928789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1717656232678941509238385 1288242174509206131928789)
                  ·
                    refine ⟨30193175965059518717081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1288242174509206131928789 30193175965059518717081)
                    ·
                      rfl

theorem cell23_176403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_176403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176403 prefixEnd_176403 := by exact prefixLift 176403
  have htrace : WordTrace (prefixWord ++ tailWord_176403) baseStart_176403 baseEnd_176403 := by
    simpa [prefixWord, tailWord_176403, baseEnd_176403] using wordTrace_append hprefix tailTrace_176403
  have hstable : (prefixWord ++ tailWord_176403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176403).length < 2 ^ (prefixWord ++ tailWord_176403).sum := by decide
  have hdescent : baseEnd_176403 < baseStart_176403 := by decide
  rcases family_descends (prefixWord ++ tailWord_176403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176407 : List Nat := [1, 1, 3, 4, 1, 4, 2, 7]
def baseStart_176407 : Nat := 118140960795 + 176407 * 2 ^ 59
def prefixEnd_176407 : Nat := 4983230072969 + 3 ^ 40 * 176407 * 2
def baseEnd_176407 : Nat := 3354873400659131129675

theorem tailTrace_176407 : CollatzResearch.WordTrace tailWord_176407 prefixEnd_176407 3354873400659131129675 := by
  unfold tailWord_176407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434091871915041762103475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289394581276694508068983 6434091871915041762103475)
  ·
    refine ⟨9651137807872562643155213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6434091871915041762103475 9651137807872562643155213)
    ·
      refine ⟨3619176677952210991183205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9651137807872562643155213 3619176677952210991183205)
      ·
        refine ⟨678595627116039560846851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3619176677952210991183205 678595627116039560846851)
        ·
          refine ⟨1017893440674059341270277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678595627116039560846851 1017893440674059341270277)
          ·
            refine ⟨190855020126386126488177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1017893440674059341270277 190855020126386126488177)
            ·
              refine ⟨143141265094789594866133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190855020126386126488177 143141265094789594866133)
              ·
                refine ⟨3354873400659131129675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 143141265094789594866133 3354873400659131129675)
                ·
                  rfl

theorem cell23_176407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 7].length) (baseStart_176407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176407 prefixEnd_176407 := by exact prefixLift 176407
  have htrace : WordTrace (prefixWord ++ tailWord_176407) baseStart_176407 baseEnd_176407 := by
    simpa [prefixWord, tailWord_176407, baseEnd_176407] using wordTrace_append hprefix tailTrace_176407
  have hstable : (prefixWord ++ tailWord_176407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176407).length < 2 ^ (prefixWord ++ tailWord_176407).sum := by decide
  have hdescent : baseEnd_176407 < baseStart_176407 := by decide
  rcases family_descends (prefixWord ++ tailWord_176407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176417 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 3]
def baseStart_176417 : Nat := 118140960795 + 176417 * 2 ^ 59
def prefixEnd_176417 : Nat := 4983230072969 + 3 ^ 40 * 176417 * 2
def baseEnd_176417 : Nat := 90586716624341501376179

theorem tailTrace_176417 : CollatzResearch.WordTrace tailWord_176417 prefixEnd_176417 90586716624341501376179 := by
  unfold tailWord_176417
  simp only [CollatzResearch.WordTrace]
  refine ⟨6434456601878813469967505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4289637734585875646645003 6434456601878813469967505)
  ·
    refine ⟨4825842451409110102475629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6434456601878813469967505 4825842451409110102475629)
    ·
      refine ⟨1809690919278416288428361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4825842451409110102475629 1809690919278416288428361)
      ·
        refine ⟨1357268189458812216321271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1809690919278416288428361 1357268189458812216321271)
        ·
          refine ⟨2035902284188218324481907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1357268189458812216321271 2035902284188218324481907)
          ·
            refine ⟨3053853426282327486722861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2035902284188218324481907 3053853426282327486722861)
            ·
              refine ⟨1145195034855872807521073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3053853426282327486722861 1145195034855872807521073)
              ·
                refine ⟨858896276141904605640805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1145195034855872807521073 858896276141904605640805)
                ·
                  refine ⟨161043051776607113557651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 858896276141904605640805 161043051776607113557651)
                  ·
                    refine ⟨241564577664910670336477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161043051776607113557651 241564577664910670336477)
                    ·
                      refine ⟨90586716624341501376179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241564577664910670336477 90586716624341501376179)
                      ·
                        rfl

theorem cell23_176417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_176417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176417 prefixEnd_176417 := by exact prefixLift 176417
  have htrace : WordTrace (prefixWord ++ tailWord_176417) baseStart_176417 baseEnd_176417 := by
    simpa [prefixWord, tailWord_176417, baseEnd_176417] using wordTrace_append hprefix tailTrace_176417
  have hstable : (prefixWord ++ tailWord_176417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176417).length < 2 ^ (prefixWord ++ tailWord_176417).sum := by decide
  have hdescent : baseEnd_176417 < baseStart_176417 := by decide
  rcases family_descends (prefixWord ++ tailWord_176417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176418 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_176418 : Nat := 118140960795 + 176418 * 2 ^ 59
def prefixEnd_176418 : Nat := 4983230072969 + 3 ^ 40 * 176418 * 2
def baseEnd_176418 : Nat := 90587230104995997463675

theorem tailTrace_176418 : CollatzResearch.WordTrace tailWord_176418 prefixEnd_176418 90587230104995997463675 := by
  unfold tailWord_176418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1608623268718797660188477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4289662049916793760502605 1608623268718797660188477)
  ·
    refine ⟨603233725769549122570679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1608623268718797660188477 603233725769549122570679)
    ·
      refine ⟨904850588654323683856019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603233725769549122570679 904850588654323683856019)
      ·
        refine ⟨1357275882981485525784029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 904850588654323683856019 1357275882981485525784029)
        ·
          refine ⟨508978456118057072169011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1357275882981485525784029 508978456118057072169011)
          ·
            refine ⟨763467684177085608253517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508978456118057072169011 763467684177085608253517)
            ·
              refine ⟨286300381566407103095069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 763467684177085608253517 286300381566407103095069)
              ·
                refine ⟨107362643087402663660651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286300381566407103095069 107362643087402663660651)
                ·
                  refine ⟨161043964631103995490977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107362643087402663660651 161043964631103995490977)
                  ·
                    refine ⟨120782973473327996618233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161043964631103995490977 120782973473327996618233)
                    ·
                      refine ⟨90587230104995997463675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120782973473327996618233 90587230104995997463675)
                      ·
                        rfl

theorem cell23_176418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_176418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176418 prefixEnd_176418 := by exact prefixLift 176418
  have htrace : WordTrace (prefixWord ++ tailWord_176418) baseStart_176418 baseEnd_176418 := by
    simpa [prefixWord, tailWord_176418, baseEnd_176418] using wordTrace_append hprefix tailTrace_176418
  have hstable : (prefixWord ++ tailWord_176418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176418).length < 2 ^ (prefixWord ++ tailWord_176418).sum := by decide
  have hdescent : baseEnd_176418 < baseStart_176418 := by decide
  rcases family_descends (prefixWord ++ tailWord_176418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176457 : List Nat := [1, 2, 1, 1, 2, 3, 1, 5, 1, 4, 2]
def baseStart_176457 : Nat := 118140960795 + 176457 * 2 ^ 59
def prefixEnd_176457 : Nat := 4983230072969 + 3 ^ 40 * 176457 * 2
def baseEnd_176457 : Nat := 90607255850521344875995

theorem tailTrace_176457 : CollatzResearch.WordTrace tailWord_176457 prefixEnd_176457 90607255850521344875995 := by
  unfold tailWord_176457
  simp only [CollatzResearch.WordTrace]
  refine ⟨6435915521733900301423625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4290610347822600200949083 6435915521733900301423625)
  ·
    refine ⟨4826936641300425226067719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6435915521733900301423625 4826936641300425226067719)
    ·
      refine ⟨7240404961950637839101579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4826936641300425226067719 7240404961950637839101579)
      ·
        refine ⟨10860607442925956758652369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7240404961950637839101579 10860607442925956758652369)
        ·
          refine ⟨8145455582194467568989277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10860607442925956758652369 8145455582194467568989277)
          ·
            refine ⟨3054545843322925338370979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8145455582194467568989277 3054545843322925338370979)
            ·
              refine ⟨4581818764984388007556469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3054545843322925338370979 4581818764984388007556469)
              ·
                refine ⟨429545509217286375708419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4581818764984388007556469 429545509217286375708419)
                ·
                  refine ⟨644318263825929563562629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 429545509217286375708419 644318263825929563562629)
                  ·
                    refine ⟨120809674467361793167993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 644318263825929563562629 120809674467361793167993)
                    ·
                      refine ⟨90607255850521344875995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120809674467361793167993 90607255850521344875995)
                      ·
                        rfl

theorem cell23_176457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 4, 2].length) (baseStart_176457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176457 prefixEnd_176457 := by exact prefixLift 176457
  have htrace : WordTrace (prefixWord ++ tailWord_176457) baseStart_176457 baseEnd_176457 := by
    simpa [prefixWord, tailWord_176457, baseEnd_176457] using wordTrace_append hprefix tailTrace_176457
  have hstable : (prefixWord ++ tailWord_176457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176457).length < 2 ^ (prefixWord ++ tailWord_176457).sum := by decide
  have hdescent : baseEnd_176457 < baseStart_176457 := by decide
  rcases family_descends (prefixWord ++ tailWord_176457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176460 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_176460 : Nat := 118140960795 + 176460 * 2 ^ 59
def prefixEnd_176460 : Nat := 4983230072969 + 3 ^ 40 * 176460 * 2
def baseEnd_176460 : Nat := 90608796292484833138481

theorem tailTrace_176460 : CollatzResearch.WordTrace tailWord_176460 prefixEnd_176460 90608796292484833138481 := by
  unfold tailWord_176460
  simp only [CollatzResearch.WordTrace]
  refine ⟨3218012470361515906891417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4290683293815354542521889 3218012470361515906891417)
  ·
    refine ⟨2413509352771136930168563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3218012470361515906891417 2413509352771136930168563)
    ·
      refine ⟨3620264029156705395252845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2413509352771136930168563 3620264029156705395252845)
      ·
        refine ⟨1357599010933764523219817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3620264029156705395252845 1357599010933764523219817)
        ·
          refine ⟨1018199258200323392414863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1357599010933764523219817 1018199258200323392414863)
          ·
            refine ⟨1527298887300485088622295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1018199258200323392414863 1527298887300485088622295)
            ·
              refine ⟨2290948330950727632933443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1527298887300485088622295 2290948330950727632933443)
              ·
                refine ⟨3436422496426091449400165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2290948330950727632933443 3436422496426091449400165)
                ·
                  refine ⟨644329218079892146762531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3436422496426091449400165 644329218079892146762531)
                  ·
                    refine ⟨966493827119838220143797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 644329218079892146762531 966493827119838220143797)
                    ·
                      refine ⟨90608796292484833138481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 966493827119838220143797 90608796292484833138481)
                      ·
                        rfl

theorem cell23_176460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_176460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176460 prefixEnd_176460 := by exact prefixLift 176460
  have htrace : WordTrace (prefixWord ++ tailWord_176460) baseStart_176460 baseEnd_176460 := by
    simpa [prefixWord, tailWord_176460, baseEnd_176460] using wordTrace_append hprefix tailTrace_176460
  have hstable : (prefixWord ++ tailWord_176460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176460).length < 2 ^ (prefixWord ++ tailWord_176460).sum := by decide
  have hdescent : baseEnd_176460 < baseStart_176460 := by decide
  rcases family_descends (prefixWord ++ tailWord_176460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176507 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3]
def baseStart_176507 : Nat := 118140960795 + 176507 * 2 ^ 59
def prefixEnd_176507 : Nat := 4983230072969 + 3 ^ 40 * 176507 * 2
def baseEnd_176507 : Nat := 90632929883246149250765

theorem tailTrace_176507 : CollatzResearch.WordTrace tailWord_176507 prefixEnd_176507 90632929883246149250765 := by
  unfold tailWord_176507
  simp only [CollatzResearch.WordTrace]
  refine ⟨6437739171552758840743775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4291826114368505893829183 6437739171552758840743775)
  ·
    refine ⟨9656608757329138261115663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6437739171552758840743775 9656608757329138261115663)
    ·
      refine ⟨14484913135993707391673495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9656608757329138261115663 14484913135993707391673495)
      ·
        refine ⟨21727369703990561087510243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14484913135993707391673495 21727369703990561087510243)
        ·
          refine ⟨32591054555985841631265365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21727369703990561087510243 32591054555985841631265365)
          ·
            refine ⟨381926420577959081616391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 32591054555985841631265365 381926420577959081616391)
            ·
              refine ⟨572889630866938622424587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381926420577959081616391 572889630866938622424587)
              ·
                refine ⟨859334446300407933636881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 572889630866938622424587 859334446300407933636881)
                ·
                  refine ⟨644500834725305950227661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 859334446300407933636881 644500834725305950227661)
                  ·
                    refine ⟨241687813021989731335373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 644500834725305950227661 241687813021989731335373)
                    ·
                      refine ⟨90632929883246149250765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241687813021989731335373 90632929883246149250765)
                      ·
                        rfl

theorem cell23_176507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 3, 3].length) (baseStart_176507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176507 prefixEnd_176507 := by exact prefixLift 176507
  have htrace : WordTrace (prefixWord ++ tailWord_176507) baseStart_176507 baseEnd_176507 := by
    simpa [prefixWord, tailWord_176507, baseEnd_176507] using wordTrace_append hprefix tailTrace_176507
  have hstable : (prefixWord ++ tailWord_176507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176507).length < 2 ^ (prefixWord ++ tailWord_176507).sum := by decide
  have hdescent : baseEnd_176507 < baseStart_176507 := by decide
  rcases family_descends (prefixWord ++ tailWord_176507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176517 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 4, 5, 2]
def baseStart_176517 : Nat := 118140960795 + 176517 * 2 ^ 59
def prefixEnd_176517 : Nat := 4983230072969 + 3 ^ 40 * 176517 * 2
def baseEnd_176517 : Nat := 90638064689791110125719

theorem tailTrace_176517 : CollatzResearch.WordTrace tailWord_176517 prefixEnd_176517 90638064689791110125719 := by
  unfold tailWord_176517
  simp only [CollatzResearch.WordTrace]
  refine ⟨6438103901516530548607805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4292069267677687032405203 6438103901516530548607805)
  ·
    refine ⟨2414288963068698955727927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6438103901516530548607805 2414288963068698955727927)
    ·
      refine ⟨3621433444603048433591891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2414288963068698955727927 3621433444603048433591891)
      ·
        refine ⟨5432150166904572650387837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3621433444603048433591891 5432150166904572650387837)
        ·
          refine ⟨2037056312589214743895439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5432150166904572650387837 2037056312589214743895439)
          ·
            refine ⟨3055584468883822115843159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037056312589214743895439 3055584468883822115843159)
            ·
              refine ⟨4583376703325733173764739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3055584468883822115843159 4583376703325733173764739)
              ·
                refine ⟨6875065054988599760647109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4583376703325733173764739 6875065054988599760647109)
                ·
                  refine ⟨1289074697810362455121333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6875065054988599760647109 1289074697810362455121333)
                  ·
                    refine ⟨120850752919721480167625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1289074697810362455121333 120850752919721480167625)
                    ·
                      refine ⟨90638064689791110125719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120850752919721480167625 90638064689791110125719)
                      ·
                        rfl

theorem cell23_176517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_176517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176517 prefixEnd_176517 := by exact prefixLift 176517
  have htrace : WordTrace (prefixWord ++ tailWord_176517) baseStart_176517 baseEnd_176517 := by
    simpa [prefixWord, tailWord_176517, baseEnd_176517] using wordTrace_append hprefix tailTrace_176517
  have hstable : (prefixWord ++ tailWord_176517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176517).length < 2 ^ (prefixWord ++ tailWord_176517).sum := by decide
  have hdescent : baseEnd_176517 < baseStart_176517 := by decide
  rcases family_descends (prefixWord ++ tailWord_176517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176567 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3]
def baseStart_176567 : Nat := 118140960795 + 176567 * 2 ^ 59
def prefixEnd_176567 : Nat := 4983230072969 + 3 ^ 40 * 176567 * 2
def baseEnd_176567 : Nat := 90663738722515914500489

theorem tailTrace_176567 : CollatzResearch.WordTrace tailWord_176567 prefixEnd_176567 90663738722515914500489 := by
  unfold tailWord_176567
  simp only [CollatzResearch.WordTrace]
  refine ⟨6439927551335389087927955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4293285034223592725285303 6439927551335389087927955)
  ·
    refine ⟨9659891327003083631891933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6439927551335389087927955 9659891327003083631891933)
    ·
      refine ⟨3622459247626156361959475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9659891327003083631891933 3622459247626156361959475)
      ·
        refine ⟨5433688871439234542939213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3622459247626156361959475 5433688871439234542939213)
        ·
          refine ⟨2037633326789712953602205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5433688871439234542939213 2037633326789712953602205)
          ·
            refine ⟨764112497546142357600827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2037633326789712953602205 764112497546142357600827)
            ·
              refine ⟨1146168746319213536401241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764112497546142357600827 1146168746319213536401241)
              ·
                refine ⟨859626559739410152300931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1146168746319213536401241 859626559739410152300931)
                ·
                  refine ⟨1289439839609115228451397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 859626559739410152300931 1289439839609115228451397)
                  ·
                    refine ⟨241769969926709105334637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1289439839609115228451397 241769969926709105334637)
                    ·
                      refine ⟨90663738722515914500489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241769969926709105334637 90663738722515914500489)
                      ·
                        rfl

theorem cell23_176567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_176567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176567 prefixEnd_176567 := by exact prefixLift 176567
  have htrace : WordTrace (prefixWord ++ tailWord_176567) baseStart_176567 baseEnd_176567 := by
    simpa [prefixWord, tailWord_176567, baseEnd_176567] using wordTrace_append hprefix tailTrace_176567
  have hstable : (prefixWord ++ tailWord_176567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176567).length < 2 ^ (prefixWord ++ tailWord_176567).sum := by decide
  have hdescent : baseEnd_176567 < baseStart_176567 := by decide
  rcases family_descends (prefixWord ++ tailWord_176567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176574 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 3, 4]
def baseStart_176574 : Nat := 118140960795 + 176574 * 2 ^ 59
def prefixEnd_176574 : Nat := 4983230072969 + 3 ^ 40 * 176574 * 2
def baseEnd_176574 : Nat := 30222444362365795704319

theorem tailTrace_176574 : CollatzResearch.WordTrace tailWord_176574 prefixEnd_176574 30222444362365795704319 := by
  unfold tailWord_176574
  simp only [CollatzResearch.WordTrace]
  refine ⟨805022857788753660429097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4293455241540019522288517 805022857788753660429097)
  ·
    refine ⟨603767143341565245321823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 805022857788753660429097 603767143341565245321823)
    ·
      refine ⟨905650715012347867982735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603767143341565245321823 905650715012347867982735)
      ·
        refine ⟨1358476072518521801974103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905650715012347867982735 1358476072518521801974103)
        ·
          refine ⟨2037714108777782702961155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1358476072518521801974103 2037714108777782702961155)
          ·
            refine ⟨3056571163166674054441733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2037714108777782702961155 3056571163166674054441733)
            ·
              refine ⟨573107093093751385207825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3056571163166674054441733 573107093093751385207825)
              ·
                refine ⟨429830319820313538905869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573107093093751385207825 429830319820313538905869)
                ·
                  refine ⟨161186369932617577089701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 429830319820313538905869 161186369932617577089701)
                  ·
                    refine ⟨30222444362365795704319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161186369932617577089701 30222444362365795704319)
                    ·
                      rfl

theorem cell23_176574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_176574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176574 prefixEnd_176574 := by exact prefixLift 176574
  have htrace : WordTrace (prefixWord ++ tailWord_176574) baseStart_176574 baseEnd_176574 := by
    simpa [prefixWord, tailWord_176574, baseEnd_176574] using wordTrace_append hprefix tailTrace_176574
  have hstable : (prefixWord ++ tailWord_176574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176574).length < 2 ^ (prefixWord ++ tailWord_176574).sum := by decide
  have hdescent : baseEnd_176574 < baseStart_176574 := by decide
  rcases family_descends (prefixWord ++ tailWord_176574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176621 : List Nat := [1, 5, 1, 3, 1, 1, 4, 1, 6]
def baseStart_176621 : Nat := 118140960795 + 176621 * 2 ^ 59
def prefixEnd_176621 : Nat := 4983230072969 + 3 ^ 40 * 176621 * 2
def baseEnd_176621 : Nat := 10076829630873189247249

theorem tailTrace_176621 : CollatzResearch.WordTrace tailWord_176621 prefixEnd_176621 10076829630873189247249 := by
  unfold tailWord_176621
  simp only [CollatzResearch.WordTrace]
  refine ⟨6441897093139756310393717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4294598062093170873595811 6441897093139756310393717)
  ·
    refine ⟨603927852481852154099411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6441897093139756310393717 603927852481852154099411)
    ·
      refine ⟨905891778722778231149117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 603927852481852154099411 905891778722778231149117)
      ·
        refine ⟨339709417021041836680919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 905891778722778231149117 339709417021041836680919)
        ·
          refine ⟨509564125531562755021379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 339709417021041836680919 509564125531562755021379)
          ·
            refine ⟨764346188297344132532069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509564125531562755021379 764346188297344132532069)
            ·
              refine ⟨143314910305752024849763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 764346188297344132532069 143314910305752024849763)
              ·
                refine ⟨214972365458628037274645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143314910305752024849763 214972365458628037274645)
                ·
                  refine ⟨10076829630873189247249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 214972365458628037274645 10076829630873189247249)
                  ·
                    rfl

theorem cell23_176621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_176621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176621 prefixEnd_176621 := by exact prefixLift 176621
  have htrace : WordTrace (prefixWord ++ tailWord_176621) baseStart_176621 baseEnd_176621 := by
    simpa [prefixWord, tailWord_176621, baseEnd_176621] using wordTrace_append hprefix tailTrace_176621
  have hstable : (prefixWord ++ tailWord_176621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176621).length < 2 ^ (prefixWord ++ tailWord_176621).sum := by decide
  have hdescent : baseEnd_176621 < baseStart_176621 := by decide
  rcases family_descends (prefixWord ++ tailWord_176621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176624 : List Nat := [2, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2]
def baseStart_176624 : Nat := 118140960795 + 176624 * 2 ^ 59
def prefixEnd_176624 : Nat := 4983230072969 + 3 ^ 40 * 176624 * 2
def baseEnd_176624 : Nat := 90693007119822191487727

theorem tailTrace_176624 : CollatzResearch.WordTrace tailWord_176624 prefixEnd_176624 90693007119822191487727 := by
  unfold tailWord_176624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3221003256064443911376463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4294671008085925215168617 3221003256064443911376463)
  ·
    refine ⟨4831504884096665867064695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3221003256064443911376463 4831504884096665867064695)
    ·
      refine ⟨7247257326144998800597043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4831504884096665867064695 7247257326144998800597043)
      ·
        refine ⟨10870885989217498200895565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7247257326144998800597043 10870885989217498200895565)
        ·
          refine ⟨4076582245956561825335837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10870885989217498200895565 4076582245956561825335837)
          ·
            refine ⟨1528718342233710684500939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4076582245956561825335837 1528718342233710684500939)
            ·
              refine ⟨2293077513350566026751409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1528718342233710684500939 2293077513350566026751409)
              ·
                refine ⟨1719808135012924520063557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2293077513350566026751409 1719808135012924520063557)
                ·
                  refine ⟨322464025314923347511917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1719808135012924520063557 322464025314923347511917)
                  ·
                    refine ⟨120924009493096255316969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322464025314923347511917 120924009493096255316969)
                    ·
                      refine ⟨90693007119822191487727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120924009493096255316969 90693007119822191487727)
                      ·
                        rfl

theorem cell23_176624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 4, 3, 2].length) (baseStart_176624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176624 prefixEnd_176624 := by exact prefixLift 176624
  have htrace : WordTrace (prefixWord ++ tailWord_176624) baseStart_176624 baseEnd_176624 := by
    simpa [prefixWord, tailWord_176624, baseEnd_176624] using wordTrace_append hprefix tailTrace_176624
  have hstable : (prefixWord ++ tailWord_176624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176624).length < 2 ^ (prefixWord ++ tailWord_176624).sum := by decide
  have hdescent : baseEnd_176624 < baseStart_176624 := by decide
  rcases family_descends (prefixWord ++ tailWord_176624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176641 : List Nat := [1, 2, 4, 1, 3, 1, 1, 3, 2, 3, 2]
def baseStart_176641 : Nat := 118140960795 + 176641 * 2 ^ 59
def prefixEnd_176641 : Nat := 4983230072969 + 3 ^ 40 * 176641 * 2
def baseEnd_176641 : Nat := 90701736290948624975149

theorem tailTrace_176641 : CollatzResearch.WordTrace tailWord_176641 prefixEnd_176641 90701736290948624975149 := by
  unfold tailWord_176641
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442626553067299726121777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4295084368711533150747851 6442626553067299726121777)
  ·
    refine ⟨4831969914800474794591333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6442626553067299726121777 4831969914800474794591333)
    ·
      refine ⟨905994359025089023985875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4831969914800474794591333 905994359025089023985875)
      ·
        refine ⟨1358991538537633535978813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 905994359025089023985875 1358991538537633535978813)
        ·
          refine ⟨509621826951612575992055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1358991538537633535978813 509621826951612575992055)
          ·
            refine ⟨764432740427418863988083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 509621826951612575992055 764432740427418863988083)
            ·
              refine ⟨1146649110641128295982125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764432740427418863988083 1146649110641128295982125)
              ·
                refine ⟨429993416490423110993297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1146649110641128295982125 429993416490423110993297)
                ·
                  refine ⟨322495062367817333244973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 429993416490423110993297 322495062367817333244973)
                  ·
                    refine ⟨120935648387931499966865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322495062367817333244973 120935648387931499966865)
                    ·
                      refine ⟨90701736290948624975149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120935648387931499966865 90701736290948624975149)
                      ·
                        rfl

theorem cell23_176641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_176641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176641 prefixEnd_176641 := by exact prefixLift 176641
  have htrace : WordTrace (prefixWord ++ tailWord_176641) baseStart_176641 baseEnd_176641 := by
    simpa [prefixWord, tailWord_176641, baseEnd_176641] using wordTrace_append hprefix tailTrace_176641
  have hstable : (prefixWord ++ tailWord_176641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176641).length < 2 ^ (prefixWord ++ tailWord_176641).sum := by decide
  have hdescent : baseEnd_176641 < baseStart_176641 := by decide
  rcases family_descends (prefixWord ++ tailWord_176641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176651 : List Nat := [1, 1, 1, 1, 7, 2, 3, 1, 1, 5]
def baseStart_176651 : Nat := 118140960795 + 176651 * 2 ^ 59
def prefixEnd_176651 : Nat := 4983230072969 + 3 ^ 40 * 176651 * 2
def baseEnd_176651 : Nat := 30235623699164528616701

theorem tailTrace_176651 : CollatzResearch.WordTrace tailWord_176651 prefixEnd_176651 30235623699164528616701 := by
  unfold tailWord_176651
  simp only [CollatzResearch.WordTrace]
  refine ⟨6442991283031071433985807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4295327522020714289323871 6442991283031071433985807)
  ·
    refine ⟨9664486924546607150978711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6442991283031071433985807 9664486924546607150978711)
    ·
      refine ⟨14496730386819910726468067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9664486924546607150978711 14496730386819910726468067)
      ·
        refine ⟨21745095580229866089702101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14496730386819910726468067 21745095580229866089702101)
        ·
          refine ⟨509650677661637486477393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 21745095580229866089702101 509650677661637486477393)
          ·
            refine ⟨382238008246228114858045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 509650677661637486477393 382238008246228114858045)
            ·
              refine ⟨143339253092335543071767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 382238008246228114858045 143339253092335543071767)
              ·
                refine ⟨215008879638503314607651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143339253092335543071767 215008879638503314607651)
                ·
                  refine ⟨322513319457754971911477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215008879638503314607651 322513319457754971911477)
                  ·
                    refine ⟨30235623699164528616701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 322513319457754971911477 30235623699164528616701)
                    ·
                      rfl

theorem cell23_176651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 1, 5].length) (baseStart_176651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176651 prefixEnd_176651 := by exact prefixLift 176651
  have htrace : WordTrace (prefixWord ++ tailWord_176651) baseStart_176651 baseEnd_176651 := by
    simpa [prefixWord, tailWord_176651, baseEnd_176651] using wordTrace_append hprefix tailTrace_176651
  have hstable : (prefixWord ++ tailWord_176651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176651).length < 2 ^ (prefixWord ++ tailWord_176651).sum := by decide
  have hdescent : baseEnd_176651 < baseStart_176651 := by decide
  rcases family_descends (prefixWord ++ tailWord_176651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176657 : List Nat := [1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 5]
def baseStart_176657 : Nat := 118140960795 + 176657 * 2 ^ 59
def prefixEnd_176657 : Nat := 4983230072969 + 3 ^ 40 * 176657 * 2
def baseEnd_176657 : Nat := 90709951981420562375075

theorem tailTrace_176657 : CollatzResearch.WordTrace tailWord_176657 prefixEnd_176657 90709951981420562375075 := by
  unfold tailWord_176657
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443210121009334458704225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4295473414006222972469483 6443210121009334458704225)
  ·
    refine ⟨4832407590757000844028169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6443210121009334458704225 4832407590757000844028169)
    ·
      refine ⟨3624305693067750633021127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4832407590757000844028169 3624305693067750633021127)
      ·
        refine ⟨5436458539601625949531691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3624305693067750633021127 5436458539601625949531691)
        ·
          refine ⟨8154687809402438924297537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5436458539601625949531691 8154687809402438924297537)
          ·
            refine ⟨6116015857051829193223153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8154687809402438924297537 6116015857051829193223153)
            ·
              refine ⟨4587011892788871894917365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6116015857051829193223153 4587011892788871894917365)
              ·
                refine ⟨430032364948956740148503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4587011892788871894917365 430032364948956740148503)
                ·
                  refine ⟨645048547423435110222755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430032364948956740148503 645048547423435110222755)
                  ·
                    refine ⟨967572821135152665334133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 645048547423435110222755 967572821135152665334133)
                    ·
                      refine ⟨90709951981420562375075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 967572821135152665334133 90709951981420562375075)
                      ·
                        rfl

theorem cell23_176657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_176657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176657 prefixEnd_176657 := by exact prefixLift 176657
  have htrace : WordTrace (prefixWord ++ tailWord_176657) baseStart_176657 baseEnd_176657 := by
    simpa [prefixWord, tailWord_176657, baseEnd_176657] using wordTrace_append hprefix tailTrace_176657
  have hstable : (prefixWord ++ tailWord_176657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176657).length < 2 ^ (prefixWord ++ tailWord_176657).sum := by decide
  have hdescent : baseEnd_176657 < baseStart_176657 := by decide
  rcases family_descends (prefixWord ++ tailWord_176657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176671 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 3, 2, 2]
def baseStart_176671 : Nat := 118140960795 + 176671 * 2 ^ 59
def prefixEnd_176671 : Nat := 4983230072969 + 3 ^ 40 * 176671 * 2
def baseEnd_176671 : Nat := 90717140710583507600011

theorem tailTrace_176671 : CollatzResearch.WordTrace tailWord_176671 prefixEnd_176671 90717140710583507600011 := by
  unfold tailWord_176671
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443720742958614849713867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4295813828639076566475911 6443720742958614849713867)
  ·
    refine ⟨9665581114437922274570801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6443720742958614849713867 9665581114437922274570801)
    ·
      refine ⟨7249185835828441705928101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9665581114437922274570801 7249185835828441705928101)
      ·
        refine ⟨1359222344217832819861519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7249185835828441705928101 1359222344217832819861519)
        ·
          refine ⟨2038833516326749229792279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1359222344217832819861519 2038833516326749229792279)
          ·
            refine ⟨3058250274490123844688419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038833516326749229792279 3058250274490123844688419)
            ·
              refine ⟨4587375411735185767032629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3058250274490123844688419 4587375411735185767032629)
              ·
                refine ⟨430066444850173665659309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4587375411735185767032629 430066444850173665659309)
                ·
                  refine ⟨161274916818815124622241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430066444850173665659309 161274916818815124622241)
                  ·
                    refine ⟨120956187614111343466681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161274916818815124622241 120956187614111343466681)
                    ·
                      refine ⟨90717140710583507600011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120956187614111343466681 90717140710583507600011)
                      ·
                        rfl

theorem cell23_176671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_176671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176671 prefixEnd_176671 := by exact prefixLift 176671
  have htrace : WordTrace (prefixWord ++ tailWord_176671) baseStart_176671 baseEnd_176671 := by
    simpa [prefixWord, tailWord_176671, baseEnd_176671] using wordTrace_append hprefix tailTrace_176671
  have hstable : (prefixWord ++ tailWord_176671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176671).length < 2 ^ (prefixWord ++ tailWord_176671).sum := by decide
  have hdescent : baseEnd_176671 < baseStart_176671 := by decide
  rcases family_descends (prefixWord ++ tailWord_176671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176677 : List Nat := [1, 3, 1, 2, 2, 1, 5, 8]
def baseStart_176677 : Nat := 118140960795 + 176677 * 2 ^ 59
def prefixEnd_176677 : Nat := 4983230072969 + 3 ^ 40 * 176677 * 2
def baseEnd_176677 : Nat := 3360008207204092004629

theorem tailTrace_176677 : CollatzResearch.WordTrace tailWord_176677 prefixEnd_176677 3360008207204092004629 := by
  unfold tailWord_176677
  simp only [CollatzResearch.WordTrace]
  refine ⟨6443939580936877874432285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4295959720624585249621523 6443939580936877874432285)
  ·
    refine ⟨2416477342851329202912107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6443939580936877874432285 2416477342851329202912107)
    ·
      refine ⟨3624716014276993804368161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2416477342851329202912107 3624716014276993804368161)
      ·
        refine ⟨2718537010707745353276121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3624716014276993804368161 2718537010707745353276121)
        ·
          refine ⟨2038902758030809014957091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2718537010707745353276121 2038902758030809014957091)
          ·
            refine ⟨3058354137046213522435637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2038902758030809014957091 3058354137046213522435637)
            ·
              refine ⟨286720700348082517728341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3058354137046213522435637 286720700348082517728341)
              ·
                refine ⟨3360008207204092004629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 286720700348082517728341 3360008207204092004629)
                ·
                  rfl

theorem cell23_176677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 8].length) (baseStart_176677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176677 prefixEnd_176677 := by exact prefixLift 176677
  have htrace : WordTrace (prefixWord ++ tailWord_176677) baseStart_176677 baseEnd_176677 := by
    simpa [prefixWord, tailWord_176677, baseEnd_176677] using wordTrace_append hprefix tailTrace_176677
  have hstable : (prefixWord ++ tailWord_176677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176677).length < 2 ^ (prefixWord ++ tailWord_176677).sum := by decide
  have hdescent : baseEnd_176677 < baseStart_176677 := by decide
  rcases family_descends (prefixWord ++ tailWord_176677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176692 : List Nat := [2, 5, 1, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_176692 : Nat := 118140960795 + 176692 * 2 ^ 59
def prefixEnd_176692 : Nat := 4983230072969 + 3 ^ 40 * 176692 * 2
def baseEnd_176692 : Nat := 90727923804327925437415

theorem tailTrace_176692 : CollatzResearch.WordTrace tailWord_176692 prefixEnd_176692 90727923804327925437415 := by
  unfold tailWord_176692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222243337941267718114165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4296324450588356957485553 3222243337941267718114165)
  ·
    refine ⟨302085312931993848573203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3222243337941267718114165 302085312931993848573203)
    ·
      refine ⟨453127969397990772859805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302085312931993848573203 453127969397990772859805)
      ·
        refine ⟨169922988524246539822427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 453127969397990772859805 169922988524246539822427)
        ·
          refine ⟨254884482786369809733641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 169922988524246539822427 254884482786369809733641)
          ·
            refine ⟨191163362089777357300231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 254884482786369809733641 191163362089777357300231)
            ·
              refine ⟨286745043134666035950347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191163362089777357300231 286745043134666035950347)
              ·
                refine ⟨430117564701999053925521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286745043134666035950347 430117564701999053925521)
                ·
                  refine ⟨322588173526499290444141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430117564701999053925521 322588173526499290444141)
                  ·
                    refine ⟨120970565072437233916553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 322588173526499290444141 120970565072437233916553)
                    ·
                      refine ⟨90727923804327925437415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120970565072437233916553 90727923804327925437415)
                      ·
                        rfl

theorem cell23_176692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_176692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176692 prefixEnd_176692 := by exact prefixLift 176692
  have htrace : WordTrace (prefixWord ++ tailWord_176692) baseStart_176692 baseEnd_176692 := by
    simpa [prefixWord, tailWord_176692, baseEnd_176692] using wordTrace_append hprefix tailTrace_176692
  have hstable : (prefixWord ++ tailWord_176692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176692).length < 2 ^ (prefixWord ++ tailWord_176692).sum := by decide
  have hdescent : baseEnd_176692 < baseStart_176692 := by decide
  rcases family_descends (prefixWord ++ tailWord_176692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176702 : List Nat := [4, 2, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_176702 : Nat := 118140960795 + 176702 * 2 ^ 59
def prefixEnd_176702 : Nat := 4983230072969 + 3 ^ 40 * 176702 * 2
def baseEnd_176702 : Nat := 30244352870290962104123

theorem tailTrace_176702 : CollatzResearch.WordTrace tailWord_176702 prefixEnd_176702 30244352870290962104123 := by
  unfold tailWord_176702
  simp only [CollatzResearch.WordTrace]
  refine ⟨805606425730788393011545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4296567603897538096061573 805606425730788393011545)
  ·
    refine ⟨604204819298091294758659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 805606425730788393011545 604204819298091294758659)
    ·
      refine ⟨906307228947136942137989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 604204819298091294758659 906307228947136942137989)
      ·
        refine ⟨169932605427588176650873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 906307228947136942137989 169932605427588176650873)
        ·
          refine ⟨127449454070691132488155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 169932605427588176650873 127449454070691132488155)
          ·
            refine ⟨191174181106036698732233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127449454070691132488155 191174181106036698732233)
            ·
              refine ⟨143380635829527524049175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191174181106036698732233 143380635829527524049175)
              ·
                refine ⟨215070953744291286073763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143380635829527524049175 215070953744291286073763)
                ·
                  refine ⟨322606430616436929110645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215070953744291286073763 322606430616436929110645)
                  ·
                    refine ⟨30244352870290962104123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 322606430616436929110645 30244352870290962104123)
                    ·
                      rfl

theorem cell23_176702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_176702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176702 prefixEnd_176702 := by exact prefixLift 176702
  have htrace : WordTrace (prefixWord ++ tailWord_176702) baseStart_176702 baseEnd_176702 := by
    simpa [prefixWord, tailWord_176702, baseEnd_176702] using wordTrace_append hprefix tailTrace_176702
  have hstable : (prefixWord ++ tailWord_176702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176702).length < 2 ^ (prefixWord ++ tailWord_176702).sum := by decide
  have hdescent : baseEnd_176702 < baseStart_176702 := by decide
  rcases family_descends (prefixWord ++ tailWord_176702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176704 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3]
def baseStart_176704 : Nat := 118140960795 + 176704 * 2 ^ 59
def prefixEnd_176704 : Nat := 4983230072969 + 3 ^ 40 * 176704 * 2
def baseEnd_176704 : Nat := 90734085572181878487359

theorem tailTrace_176704 : CollatzResearch.WordTrace tailWord_176704 prefixEnd_176704 90734085572181878487359 := by
  unfold tailWord_176704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3222462175919530742832583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4296616234559374323776777 3222462175919530742832583)
  ·
    refine ⟨4833693263879296114248875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3222462175919530742832583 4833693263879296114248875)
    ·
      refine ⟨7250539895818944171373313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4833693263879296114248875 7250539895818944171373313)
      ·
        refine ⟨5437904921864208128529985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7250539895818944171373313 5437904921864208128529985)
        ·
          refine ⟨4078428691398156096397489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5437904921864208128529985 4078428691398156096397489)
          ·
            refine ⟨3058821518548617072298117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4078428691398156096397489 3058821518548617072298117)
            ·
              refine ⟨573529034727865701055897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3058821518548617072298117 573529034727865701055897)
              ·
                refine ⟨430146776045899275791923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 573529034727865701055897 430146776045899275791923)
                ·
                  refine ⟨645220164068848913687885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430146776045899275791923 645220164068848913687885)
                  ·
                    refine ⟨241957561525818342632957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645220164068848913687885 241957561525818342632957)
                    ·
                      refine ⟨90734085572181878487359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241957561525818342632957 90734085572181878487359)
                      ·
                        rfl

theorem cell23_176704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_176704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176704 prefixEnd_176704 := by exact prefixLift 176704
  have htrace : WordTrace (prefixWord ++ tailWord_176704) baseStart_176704 baseEnd_176704 := by
    simpa [prefixWord, tailWord_176704, baseEnd_176704] using wordTrace_append hprefix tailTrace_176704
  have hstable : (prefixWord ++ tailWord_176704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176704).length < 2 ^ (prefixWord ++ tailWord_176704).sum := by decide
  have hdescent : baseEnd_176704 < baseStart_176704 := by decide
  rcases family_descends (prefixWord ++ tailWord_176704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176705 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 1, 2, 2]
def baseStart_176705 : Nat := 118140960795 + 176705 * 2 ^ 59
def prefixEnd_176705 : Nat := 4983230072969 + 3 ^ 40 * 176705 * 2
def baseEnd_176705 : Nat := 90734599052836374574855

theorem tailTrace_176705 : CollatzResearch.WordTrace tailWord_176705 prefixEnd_176705 90734599052836374574855 := by
  unfold tailWord_176705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6444960824835438656451569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4296640549890292437634379 6444960824835438656451569)
  ·
    refine ⟨4833720618626578992338677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6444960824835438656451569 4833720618626578992338677)
    ·
      refine ⟨453161307996241780531751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4833720618626578992338677 453161307996241780531751)
      ·
        refine ⟨679741961994362670797627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 453161307996241780531751 679741961994362670797627)
        ·
          refine ⟨1019612942991544006196441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 679741961994362670797627 1019612942991544006196441)
          ·
            refine ⟨764709707243658004647331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1019612942991544006196441 764709707243658004647331)
            ·
              refine ⟨1147064560865487006970997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 764709707243658004647331 1147064560865487006970997)
              ·
                refine ⟨107537302581139406903531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1147064560865487006970997 107537302581139406903531)
                ·
                  refine ⟨161305953871709110355297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107537302581139406903531 161305953871709110355297)
                  ·
                    refine ⟨120979465403781832766473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161305953871709110355297 120979465403781832766473)
                    ·
                      refine ⟨90734599052836374574855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 120979465403781832766473 90734599052836374574855)
                      ·
                        rfl

theorem cell23_176705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_176705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176705 prefixEnd_176705 := by exact prefixLift 176705
  have htrace : WordTrace (prefixWord ++ tailWord_176705) baseStart_176705 baseEnd_176705 := by
    simpa [prefixWord, tailWord_176705, baseEnd_176705] using wordTrace_append hprefix tailTrace_176705
  have hstable : (prefixWord ++ tailWord_176705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176705).length < 2 ^ (prefixWord ++ tailWord_176705).sum := by decide
  have hdescent : baseEnd_176705 < baseStart_176705 := by decide
  rcases family_descends (prefixWord ++ tailWord_176705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176721 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 3]
def baseStart_176721 : Nat := 118140960795 + 176721 * 2 ^ 59
def prefixEnd_176721 : Nat := 4983230072969 + 3 ^ 40 * 176721 * 2
def baseEnd_176721 : Nat := 90742814743308311974781

theorem tailTrace_176721 : CollatzResearch.WordTrace tailWord_176721 prefixEnd_176721 90742814743308311974781 := by
  unfold tailWord_176721
  simp only [CollatzResearch.WordTrace]
  refine ⟨6445544392777473389034017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4297029595184982259356011 6445544392777473389034017)
  ·
    refine ⟨4834158294583105041775513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6445544392777473389034017 4834158294583105041775513)
    ·
      refine ⟨3625618720937328781331635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4834158294583105041775513 3625618720937328781331635)
      ·
        refine ⟨5438428081405993171997453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3625618720937328781331635 5438428081405993171997453)
        ·
          refine ⟨2039410530527247439499045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5438428081405993171997453 2039410530527247439499045)
          ·
            refine ⟨382389474473858894906071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2039410530527247439499045 382389474473858894906071)
            ·
              refine ⟨573584211710788342359107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382389474473858894906071 573584211710788342359107)
              ·
                refine ⟨860376317566182513538661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573584211710788342359107 860376317566182513538661)
                ·
                  refine ⟨161320559543659221288499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 860376317566182513538661 161320559543659221288499)
                  ·
                    refine ⟨241980839315488831932749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161320559543659221288499 241980839315488831932749)
                    ·
                      refine ⟨90742814743308311974781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 241980839315488831932749 90742814743308311974781)
                      ·
                        rfl

theorem cell23_176721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_176721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176721 prefixEnd_176721 := by exact prefixLift 176721
  have htrace : WordTrace (prefixWord ++ tailWord_176721) baseStart_176721 baseEnd_176721 := by
    simpa [prefixWord, tailWord_176721, baseEnd_176721] using wordTrace_append hprefix tailTrace_176721
  have hstable : (prefixWord ++ tailWord_176721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176721).length < 2 ^ (prefixWord ++ tailWord_176721).sum := by decide
  have hdescent : baseEnd_176721 < baseStart_176721 := by decide
  rcases family_descends (prefixWord ++ tailWord_176721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176777 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 9]
def baseStart_176777 : Nat := 118140960795 + 176777 * 2 ^ 59
def prefixEnd_176777 : Nat := 4983230072969 + 3 ^ 40 * 176777 * 2
def baseEnd_176777 : Nat := 90771569659960092874523

theorem tailTrace_176777 : CollatzResearch.WordTrace tailWord_176777 prefixEnd_176777 90771569659960092874523 := by
  unfold tailWord_176777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6447586880574594953072585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4298391253716396635381723 6447586880574594953072585)
  ·
    refine ⟨4835690160430946214804439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6447586880574594953072585 4835690160430946214804439)
    ·
      refine ⟨7253535240646419322206659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4835690160430946214804439 7253535240646419322206659)
      ·
        refine ⟨10880302860969628983309989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7253535240646419322206659 10880302860969628983309989)
        ·
          refine ⟨2040056786431805434370623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10880302860969628983309989 2040056786431805434370623)
          ·
            refine ⟨3060085179647708151555935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2040056786431805434370623 3060085179647708151555935)
            ·
              refine ⟨4590127769471562227333903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3060085179647708151555935 4590127769471562227333903)
              ·
                refine ⟨6885191654207343341000855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4590127769471562227333903 6885191654207343341000855)
                ·
                  refine ⟨10327787481311015011501283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6885191654207343341000855 10327787481311015011501283)
                  ·
                    refine ⟨15491681221966522517251925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10327787481311015011501283 15491681221966522517251925)
                    ·
                      refine ⟨90771569659960092874523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 15491681221966522517251925 90771569659960092874523)
                      ·
                        rfl

theorem cell23_176777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_176777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176777 prefixEnd_176777 := by exact prefixLift 176777
  have htrace : WordTrace (prefixWord ++ tailWord_176777) baseStart_176777 baseEnd_176777 := by
    simpa [prefixWord, tailWord_176777, baseEnd_176777] using wordTrace_append hprefix tailTrace_176777
  have hstable : (prefixWord ++ tailWord_176777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176777).length < 2 ^ (prefixWord ++ tailWord_176777).sum := by decide
  have hdescent : baseEnd_176777 < baseStart_176777 := by decide
  rcases family_descends (prefixWord ++ tailWord_176777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176845 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_176845 : Nat := 118140960795 + 176845 * 2 ^ 59
def prefixEnd_176845 : Nat := 4983230072969 + 3 ^ 40 * 176845 * 2
def baseEnd_176845 : Nat := 90806486344465826824211

theorem tailTrace_176845 : CollatzResearch.WordTrace tailWord_176845 prefixEnd_176845 90806486344465826824211 := by
  unfold tailWord_176845
  simp only [CollatzResearch.WordTrace]
  refine ⟨6450067044328242566547989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4300044696218828377698659 6450067044328242566547989)
  ·
    refine ⟨302346892702886370306937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6450067044328242566547989 302346892702886370306937)
    ·
      refine ⟨226760169527164777730203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302346892702886370306937 226760169527164777730203)
      ·
        refine ⟨340140254290747166595305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226760169527164777730203 340140254290747166595305)
        ·
          refine ⟨255105190718060374946479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340140254290747166595305 255105190718060374946479)
          ·
            refine ⟨382657786077090562419719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255105190718060374946479 382657786077090562419719)
            ·
              refine ⟨573986679115635843629579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 382657786077090562419719 573986679115635843629579)
              ·
                refine ⟨860980018673453765444369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 573986679115635843629579 860980018673453765444369)
                ·
                  refine ⟨645735014005090324083277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 860980018673453765444369 645735014005090324083277)
                  ·
                    refine ⟨242150630251908871531229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 645735014005090324083277 242150630251908871531229)
                    ·
                      refine ⟨90806486344465826824211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242150630251908871531229 90806486344465826824211)
                      ·
                        rfl

theorem cell23_176845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_176845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176845 prefixEnd_176845 := by exact prefixLift 176845
  have htrace : WordTrace (prefixWord ++ tailWord_176845) baseStart_176845 baseEnd_176845 := by
    simpa [prefixWord, tailWord_176845, baseEnd_176845] using wordTrace_append hprefix tailTrace_176845
  have hstable : (prefixWord ++ tailWord_176845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176845).length < 2 ^ (prefixWord ++ tailWord_176845).sum := by decide
  have hdescent : baseEnd_176845 < baseStart_176845 := by decide
  rcases family_descends (prefixWord ++ tailWord_176845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176868 : List Nat := [2, 3, 1, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_176868 : Nat := 118140960795 + 176868 * 2 ^ 59
def prefixEnd_176868 : Nat := 4983230072969 + 3 ^ 40 * 176868 * 2
def baseEnd_176868 : Nat := 90818296399519236836605

theorem tailTrace_176868 : CollatzResearch.WordTrace tailWord_176868 prefixEnd_176868 90818296399519236836605 := by
  unfold tailWord_176868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225452961622458747317629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4300603948829944996423505 3225452961622458747317629)
  ·
    refine ⟨1209544860608422030244111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3225452961622458747317629 1209544860608422030244111)
    ·
      refine ⟨1814317290912633045366167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1209544860608422030244111 1814317290912633045366167)
      ·
        refine ⟨2721475936368949568049251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1814317290912633045366167 2721475936368949568049251)
        ·
          refine ⟨4082213904553424352073877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2721475936368949568049251 4082213904553424352073877)
          ·
            refine ⟨191353776775941766503463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 4082213904553424352073877 191353776775941766503463)
            ·
              refine ⟨287030665163912649755195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191353776775941766503463 287030665163912649755195)
              ·
                refine ⟨430545997745868974632793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287030665163912649755195 430545997745868974632793)
                ·
                  refine ⟨322909498309401730974595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 430545997745868974632793 322909498309401730974595)
                  ·
                    refine ⟨484364247464102596461893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 322909498309401730974595 484364247464102596461893)
                    ·
                      refine ⟨90818296399519236836605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 484364247464102596461893 90818296399519236836605)
                      ·
                        rfl

theorem cell23_176868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_176868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176868 prefixEnd_176868 := by exact prefixLift 176868
  have htrace : WordTrace (prefixWord ++ tailWord_176868) baseStart_176868 baseEnd_176868 := by
    simpa [prefixWord, tailWord_176868, baseEnd_176868] using wordTrace_append hprefix tailTrace_176868
  have hstable : (prefixWord ++ tailWord_176868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176868).length < 2 ^ (prefixWord ++ tailWord_176868).sum := by decide
  have hdescent : baseEnd_176868 < baseStart_176868 := by decide
  rcases family_descends (prefixWord ++ tailWord_176868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176874 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 8]
def baseStart_176874 : Nat := 118140960795 + 176874 * 2 ^ 59
def prefixEnd_176874 : Nat := 4983230072969 + 3 ^ 40 * 176874 * 2
def baseEnd_176874 : Nat := 10091264142605134817953

theorem tailTrace_176874 : CollatzResearch.WordTrace tailWord_176874 prefixEnd_176874 10091264142605134817953 := by
  unfold tailWord_176874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1612781190305795129838419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4300749840815453679569117 1612781190305795129838419)
  ·
    refine ⟨2419171785458692694757629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1612781190305795129838419 2419171785458692694757629)
    ·
      refine ⟨907189419547009760534111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2419171785458692694757629 907189419547009760534111)
      ·
        refine ⟨1360784129320514640801167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907189419547009760534111 1360784129320514640801167)
        ·
          refine ⟨2041176193980771961201751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1360784129320514640801167 2041176193980771961201751)
          ·
            refine ⟨3061764290971157941802627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2041176193980771961201751 3061764290971157941802627)
            ·
              refine ⟨4592646436456736912703941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3061764290971157941802627 4592646436456736912703941)
              ·
                refine ⟨861121206835638171131989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4592646436456736912703941 861121206835638171131989)
                ·
                  refine ⟨10091264142605134817953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 861121206835638171131989 10091264142605134817953)
                  ·
                    rfl

theorem cell23_176874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 8].length) (baseStart_176874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176874 prefixEnd_176874 := by exact prefixLift 176874
  have htrace : WordTrace (prefixWord ++ tailWord_176874) baseStart_176874 baseEnd_176874 := by
    simpa [prefixWord, tailWord_176874, baseEnd_176874] using wordTrace_append hprefix tailTrace_176874
  have hstable : (prefixWord ++ tailWord_176874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176874).length < 2 ^ (prefixWord ++ tailWord_176874).sum := by decide
  have hdescent : baseEnd_176874 < baseStart_176874 := by decide
  rcases family_descends (prefixWord ++ tailWord_176874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176911 : List Nat := [1, 1, 2, 1, 1, 1, 5, 1, 3, 5, 2]
def baseStart_176911 : Nat := 118140960795 + 176911 * 2 ^ 59
def prefixEnd_176911 : Nat := 4983230072969 + 3 ^ 40 * 176911 * 2
def baseEnd_176911 : Nat := 90840376067662568598907

theorem tailTrace_176911 : CollatzResearch.WordTrace tailWord_176911 prefixEnd_176911 90840376067662568598907 := by
  unfold tailWord_176911
  simp only [CollatzResearch.WordTrace]
  refine ⟨6452474262089135838450587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4301649508059423892300391 6452474262089135838450587)
  ·
    refine ⟨9678711393133703757675881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6452474262089135838450587 9678711393133703757675881)
    ·
      refine ⟨7259033544850277818256911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9678711393133703757675881 7259033544850277818256911)
      ·
        refine ⟨10888550317275416727385367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7259033544850277818256911 10888550317275416727385367)
        ·
          refine ⟨16332825475913125091078051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10888550317275416727385367 16332825475913125091078051)
          ·
            refine ⟨24499238213869687636617077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16332825475913125091078051 24499238213869687636617077)
            ·
              refine ⟨2296803582550283215932851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24499238213869687636617077 2296803582550283215932851)
              ·
                refine ⟨3445205373825424823899277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2296803582550283215932851 3445205373825424823899277)
                ·
                  refine ⟨1291952015184534308962229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3445205373825424823899277 1291952015184534308962229)
                  ·
                    refine ⟨121120501423550091465209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1291952015184534308962229 121120501423550091465209)
                    ·
                      refine ⟨90840376067662568598907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121120501423550091465209 90840376067662568598907)
                      ·
                        rfl

theorem cell23_176911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 5, 2].length) (baseStart_176911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176911 prefixEnd_176911 := by exact prefixLift 176911
  have htrace : WordTrace (prefixWord ++ tailWord_176911) baseStart_176911 baseEnd_176911 := by
    simpa [prefixWord, tailWord_176911, baseEnd_176911] using wordTrace_append hprefix tailTrace_176911
  have hstable : (prefixWord ++ tailWord_176911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176911).length < 2 ^ (prefixWord ++ tailWord_176911).sum := by decide
  have hdescent : baseEnd_176911 < baseStart_176911 := by decide
  rcases family_descends (prefixWord ++ tailWord_176911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176928 : List Nat := [2, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2]
def baseStart_176928 : Nat := 118140960795 + 176928 * 2 ^ 59
def prefixEnd_176928 : Nat := 4983230072969 + 3 ^ 40 * 176928 * 2
def baseEnd_176928 : Nat := 90849105238789002086329

theorem tailTrace_176928 : CollatzResearch.WordTrace tailWord_176928 prefixEnd_176928 90849105238789002086329 := by
  unfold tailWord_176928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226547151513773870909719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4302062868685031827879625 3226547151513773870909719)
  ·
    refine ⟨4839820727270660806364579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3226547151513773870909719 4839820727270660806364579)
    ·
      refine ⟨7259731090905991209546869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4839820727270660806364579 7259731090905991209546869)
      ·
        refine ⟨680599789772436675895019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7259731090905991209546869 680599789772436675895019)
        ·
          refine ⟨1020899684658655013842529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 680599789772436675895019 1020899684658655013842529)
          ·
            refine ⟨765674763493991260381897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1020899684658655013842529 765674763493991260381897)
            ·
              refine ⟨574256072620493445286423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 765674763493991260381897 574256072620493445286423)
              ·
                refine ⟨861384108930740167929635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574256072620493445286423 861384108930740167929635)
                ·
                  refine ⟨1292076163396110251894453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 861384108930740167929635 1292076163396110251894453)
                  ·
                    refine ⟨121132140318385336115105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1292076163396110251894453 121132140318385336115105)
                    ·
                      refine ⟨90849105238789002086329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121132140318385336115105 90849105238789002086329)
                      ·
                        rfl

theorem cell23_176928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_176928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176928 prefixEnd_176928 := by exact prefixLift 176928
  have htrace : WordTrace (prefixWord ++ tailWord_176928) baseStart_176928 baseEnd_176928 := by
    simpa [prefixWord, tailWord_176928, baseEnd_176928] using wordTrace_append hprefix tailTrace_176928
  have hstable : (prefixWord ++ tailWord_176928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176928).length < 2 ^ (prefixWord ++ tailWord_176928).sum := by decide
  have hdescent : baseEnd_176928 < baseStart_176928 := by decide
  rcases family_descends (prefixWord ++ tailWord_176928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176951 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 4, 4]
def baseStart_176951 : Nat := 118140960795 + 176951 * 2 ^ 59
def prefixEnd_176951 : Nat := 4983230072969 + 3 ^ 40 * 176951 * 2
def baseEnd_176951 : Nat := 30286971764614137366241

theorem tailTrace_176951 : CollatzResearch.WordTrace tailWord_176951 prefixEnd_176951 30286971764614137366241 := by
  unfold tailWord_176951
  simp only [CollatzResearch.WordTrace]
  refine ⟨6453933181944222669906707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4302622121296148446604471 6453933181944222669906707)
  ·
    refine ⟨9680899772916334004860061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6453933181944222669906707 9680899772916334004860061)
    ·
      refine ⟨3630337414843625251822523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9680899772916334004860061 3630337414843625251822523)
      ·
        refine ⟨5445506122265437877733785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630337414843625251822523 5445506122265437877733785)
        ·
          refine ⟨4084129591699078408300339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5445506122265437877733785 4084129591699078408300339)
          ·
            refine ⟨6126194387548617612450509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4084129591699078408300339 6126194387548617612450509)
            ·
              refine ⟨2297322895330731604668941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6126194387548617612450509 2297322895330731604668941)
              ·
                refine ⟨861496085749024351750853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2297322895330731604668941 861496085749024351750853)
                ·
                  refine ⟨161530516077942065953285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861496085749024351750853 161530516077942065953285)
                  ·
                    refine ⟨30286971764614137366241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161530516077942065953285 30286971764614137366241)
                    ·
                      rfl

theorem cell23_176951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 4].length) (baseStart_176951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176951 prefixEnd_176951 := by exact prefixLift 176951
  have htrace : WordTrace (prefixWord ++ tailWord_176951) baseStart_176951 baseEnd_176951 := by
    simpa [prefixWord, tailWord_176951, baseEnd_176951] using wordTrace_append hprefix tailTrace_176951
  have hstable : (prefixWord ++ tailWord_176951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176951).length < 2 ^ (prefixWord ++ tailWord_176951).sum := by decide
  have hdescent : baseEnd_176951 < baseStart_176951 := by decide
  rcases family_descends (prefixWord ++ tailWord_176951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176952 : List Nat := [2, 1, 2, 1, 3, 2, 5, 2, 1, 1, 3]
def baseStart_176952 : Nat := 118140960795 + 176952 * 2 ^ 59
def prefixEnd_176952 : Nat := 4983230072969 + 3 ^ 40 * 176952 * 2
def baseEnd_176952 : Nat := 90861428774496908186219

theorem tailTrace_176952 : CollatzResearch.WordTrace tailWord_176952 prefixEnd_176952 90861428774496908186219 := by
  unfold tailWord_176952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3226984827470299920346555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4302646436627066560462073 3226984827470299920346555)
  ·
    refine ⟨4840477241205449880519833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3226984827470299920346555 4840477241205449880519833)
    ·
      refine ⟨3630357930904087410389875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4840477241205449880519833 3630357930904087410389875)
      ·
        refine ⟨5445536896356131115584813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3630357930904087410389875 5445536896356131115584813)
        ·
          refine ⟨2042076336133549168344305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5445536896356131115584813 2042076336133549168344305)
          ·
            refine ⟨1531557252100161876258229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042076336133549168344305 1531557252100161876258229)
            ·
              refine ⟨143583492384390175899209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1531557252100161876258229 143583492384390175899209)
              ·
                refine ⟨107687619288292631924407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143583492384390175899209 107687619288292631924407)
                ·
                  refine ⟨161531428932438947886611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107687619288292631924407 161531428932438947886611)
                  ·
                    refine ⟨242297143398658421829917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161531428932438947886611 242297143398658421829917)
                    ·
                      refine ⟨90861428774496908186219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242297143398658421829917 90861428774496908186219)
                      ·
                        rfl

theorem cell23_176952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 2, 1, 1, 3].length) (baseStart_176952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176952 prefixEnd_176952 := by exact prefixLift 176952
  have htrace : WordTrace (prefixWord ++ tailWord_176952) baseStart_176952 baseEnd_176952 := by
    simpa [prefixWord, tailWord_176952, baseEnd_176952] using wordTrace_append hprefix tailTrace_176952
  have hstable : (prefixWord ++ tailWord_176952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176952).length < 2 ^ (prefixWord ++ tailWord_176952).sum := by decide
  have hdescent : baseEnd_176952 < baseStart_176952 := by decide
  rcases family_descends (prefixWord ++ tailWord_176952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176968 : List Nat := [2, 1, 3, 1, 1, 3, 3, 3, 2, 4]
def baseStart_176968 : Nat := 118140960795 + 176968 * 2 ^ 59
def prefixEnd_176968 : Nat := 4983230072969 + 3 ^ 40 * 176968 * 2
def baseEnd_176968 : Nat := 30289881488322948528715

theorem tailTrace_176968 : CollatzResearch.WordTrace tailWord_176968 prefixEnd_176968 30289881488322948528715 := by
  unfold tailWord_176968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227276611441317286637779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4303035481921756382183705 3227276611441317286637779)
  ·
    refine ⟨4840914917161975929956669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227276611441317286637779 4840914917161975929956669)
    ·
      refine ⟨1815343093935740973733751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4840914917161975929956669 1815343093935740973733751)
      ·
        refine ⟨2723014640903611460600627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1815343093935740973733751 2723014640903611460600627)
        ·
          refine ⟨4084521961355417190900941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723014640903611460600627 4084521961355417190900941)
          ·
            refine ⟨1531695735508281446587853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4084521961355417190900941 1531695735508281446587853)
            ·
              refine ⟨574385900815605542470445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1531695735508281446587853 574385900815605542470445)
              ·
                refine ⟨215394712805852078426417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 574385900815605542470445 215394712805852078426417)
                ·
                  refine ⟨161546034604389058819813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215394712805852078426417 161546034604389058819813)
                  ·
                    refine ⟨30289881488322948528715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161546034604389058819813 30289881488322948528715)
                    ·
                      rfl

theorem cell23_176968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_176968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176968 prefixEnd_176968 := by exact prefixLift 176968
  have htrace : WordTrace (prefixWord ++ tailWord_176968) baseStart_176968 baseEnd_176968 := by
    simpa [prefixWord, tailWord_176968, baseEnd_176968] using wordTrace_append hprefix tailTrace_176968
  have hstable : (prefixWord ++ tailWord_176968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176968).length < 2 ^ (prefixWord ++ tailWord_176968).sum := by decide
  have hdescent : baseEnd_176968 < baseStart_176968 := by decide
  rcases family_descends (prefixWord ++ tailWord_176968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176978 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_176978 : Nat := 118140960795 + 176978 * 2 ^ 59
def prefixEnd_176978 : Nat := 4983230072969 + 3 ^ 40 * 176978 * 2
def baseEnd_176978 : Nat := 90874779271513806461099

theorem tailTrace_176978 : CollatzResearch.WordTrace tailWord_176978 prefixEnd_176978 90874779271513806461099 := by
  unfold tailWord_176978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1613729488211601570284897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4303278635230937520759725 1613729488211601570284897)
  ·
    refine ⟨1210297116158701177713673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1613729488211601570284897 1210297116158701177713673)
    ·
      refine ⟨907722837119025883285255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1210297116158701177713673 907722837119025883285255)
      ·
        refine ⟨1361584255678538824927883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 907722837119025883285255 1361584255678538824927883)
        ·
          refine ⟨2042376383517808237391825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1361584255678538824927883 2042376383517808237391825)
          ·
            refine ⟨1531782287638356178043869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2042376383517808237391825 1531782287638356178043869)
            ·
              refine ⟨574418357864383566766451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1531782287638356178043869 574418357864383566766451)
              ·
                refine ⟨861627536796575350149677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574418357864383566766451 861627536796575350149677)
                ·
                  refine ⟨323110326298715756306129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 861627536796575350149677 323110326298715756306129)
                  ·
                    refine ⟨242332744724036817229597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 323110326298715756306129 242332744724036817229597)
                    ·
                      refine ⟨90874779271513806461099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242332744724036817229597 90874779271513806461099)
                      ·
                        rfl

theorem cell23_176978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_176978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176978 prefixEnd_176978 := by exact prefixLift 176978
  have htrace : WordTrace (prefixWord ++ tailWord_176978) baseStart_176978 baseEnd_176978 := by
    simpa [prefixWord, tailWord_176978, baseEnd_176978] using wordTrace_append hprefix tailTrace_176978
  have hstable : (prefixWord ++ tailWord_176978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176978).length < 2 ^ (prefixWord ++ tailWord_176978).sum := by decide
  have hdescent : baseEnd_176978 < baseStart_176978 := by decide
  rcases family_descends (prefixWord ++ tailWord_176978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176988 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_176988 : Nat := 118140960795 + 176988 * 2 ^ 59
def prefixEnd_176988 : Nat := 4983230072969 + 3 ^ 40 * 176988 * 2
def baseEnd_176988 : Nat := 90879914078058767336053

theorem tailTrace_176988 : CollatzResearch.WordTrace tailWord_176988 prefixEnd_176988 90879914078058767336053 := by
  unfold tailWord_176988
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227641341405088994501809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4303521788540118659335745 3227641341405088994501809)
  ·
    refine ⟨2420731006053816745876357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3227641341405088994501809 2420731006053816745876357)
    ·
      refine ⟨453887063635090639851817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2420731006053816745876357 453887063635090639851817)
      ·
        refine ⟨340415297726317979888863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 453887063635090639851817 340415297726317979888863)
        ·
          refine ⟨510622946589476969833295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340415297726317979888863 510622946589476969833295)
          ·
            refine ⟨765934419884215454749943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510622946589476969833295 765934419884215454749943)
            ·
              refine ⟨1148901629826323182124915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 765934419884215454749943 1148901629826323182124915)
              ·
                refine ⟨1723352444739484773187373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1148901629826323182124915 1723352444739484773187373)
                ·
                  refine ⟨646257166777306789945265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1723352444739484773187373 646257166777306789945265)
                  ·
                    refine ⟨484692875082980092458949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646257166777306789945265 484692875082980092458949)
                    ·
                      refine ⟨90879914078058767336053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 484692875082980092458949 90879914078058767336053)
                      ·
                        rfl

theorem cell23_176988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_176988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176988 prefixEnd_176988 := by exact prefixLift 176988
  have htrace : WordTrace (prefixWord ++ tailWord_176988) baseStart_176988 baseEnd_176988 := by
    simpa [prefixWord, tailWord_176988, baseEnd_176988] using wordTrace_append hprefix tailTrace_176988
  have hstable : (prefixWord ++ tailWord_176988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176988).length < 2 ^ (prefixWord ++ tailWord_176988).sum := by decide
  have hdescent : baseEnd_176988 < baseStart_176988 := by decide
  rcases family_descends (prefixWord ++ tailWord_176988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_176992 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 1, 2, 2]
def baseStart_176992 : Nat := 118140960795 + 176992 * 2 ^ 59
def prefixEnd_176992 : Nat := 4983230072969 + 3 ^ 40 * 176992 * 2
def baseEnd_176992 : Nat := 90881968000676751686035

theorem tailTrace_176992 : CollatzResearch.WordTrace tailWord_176992 prefixEnd_176992 90881968000676751686035 := by
  unfold tailWord_176992
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227714287397843336074615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4303619049863791114766153 3227714287397843336074615)
  ·
    refine ⟨4841571431096765004111923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3227714287397843336074615 4841571431096765004111923)
    ·
      refine ⟨7262357146645147506167885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4841571431096765004111923 7262357146645147506167885)
      ·
        refine ⟨2723383929991930314812957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7262357146645147506167885 2723383929991930314812957)
        ·
          refine ⟨1021268973746973868054859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2723383929991930314812957 1021268973746973868054859)
          ·
            refine ⟨1531903460620460802082289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1021268973746973868054859 1531903460620460802082289)
            ·
              refine ⟨1148927595465345601561717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1531903460620460802082289 1148927595465345601561717)
              ·
                refine ⟨107711962074876150146411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1148927595465345601561717 107711962074876150146411)
                ·
                  refine ⟨161567943112314225219617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107711962074876150146411 161567943112314225219617)
                  ·
                    refine ⟨121175957334235668914713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161567943112314225219617 121175957334235668914713)
                    ·
                      refine ⟨90881968000676751686035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121175957334235668914713 90881968000676751686035)
                      ·
                        rfl

theorem cell23_176992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_176992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_176992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_176992 prefixEnd_176992 := by exact prefixLift 176992
  have htrace : WordTrace (prefixWord ++ tailWord_176992) baseStart_176992 baseEnd_176992 := by
    simpa [prefixWord, tailWord_176992, baseEnd_176992] using wordTrace_append hprefix tailTrace_176992
  have hstable : (prefixWord ++ tailWord_176992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_176992).length < 2 ^ (prefixWord ++ tailWord_176992).sum := by decide
  have hdescent : baseEnd_176992 < baseStart_176992 := by decide
  rcases family_descends (prefixWord ++ tailWord_176992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177008 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3]
def baseStart_177008 : Nat := 118140960795 + 177008 * 2 ^ 59
def prefixEnd_177008 : Nat := 4983230072969 + 3 ^ 40 * 177008 * 2
def baseEnd_177008 : Nat := 90890183691148689085961

theorem tailTrace_177008 : CollatzResearch.WordTrace tailWord_177008 prefixEnd_177008 90890183691148689085961 := by
  unfold tailWord_177008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3228006071368860702365839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4304008095158480936487785 3228006071368860702365839)
  ·
    refine ⟨4842009107053291053548759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3228006071368860702365839 4842009107053291053548759)
    ·
      refine ⟨7263013660579936580323139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4842009107053291053548759 7263013660579936580323139)
      ·
        refine ⟨10894520490869904870484709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7263013660579936580323139 10894520490869904870484709)
        ·
          refine ⟨2042722592038107163215883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10894520490869904870484709 2042722592038107163215883)
          ·
            refine ⟨3064083888057160744823825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2042722592038107163215883 3064083888057160744823825)
            ·
              refine ⟨2298062916042870558617869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3064083888057160744823825 2298062916042870558617869)
              ·
                refine ⟨861773593516076459481701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2298062916042870558617869 861773593516076459481701)
                ·
                  refine ⟨161582548784264336152819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 861773593516076459481701 161582548784264336152819)
                  ·
                    refine ⟨242373823176396504229229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161582548784264336152819 242373823176396504229229)
                    ·
                      refine ⟨90890183691148689085961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242373823176396504229229 90890183691148689085961)
                      ·
                        rfl

theorem cell23_177008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 4, 1, 3].length) (baseStart_177008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177008 prefixEnd_177008 := by exact prefixLift 177008
  have htrace : WordTrace (prefixWord ++ tailWord_177008) baseStart_177008 baseEnd_177008 := by
    simpa [prefixWord, tailWord_177008, baseEnd_177008] using wordTrace_append hprefix tailTrace_177008
  have hstable : (prefixWord ++ tailWord_177008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177008).length < 2 ^ (prefixWord ++ tailWord_177008).sum := by decide
  have hdescent : baseEnd_177008 < baseStart_177008 := by decide
  rcases family_descends (prefixWord ++ tailWord_177008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177009 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 1, 2, 2]
def baseStart_177009 : Nat := 118140960795 + 177009 * 2 ^ 59
def prefixEnd_177009 : Nat := 4983230072969 + 3 ^ 40 * 177009 * 2
def baseEnd_177009 : Nat := 90890697171803185173457

theorem tailTrace_177009 : CollatzResearch.WordTrace tailWord_177009 prefixEnd_177009 90890697171803185173457 := by
  unfold tailWord_177009
  simp only [CollatzResearch.WordTrace]
  refine ⟨6456048615734098575518081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4304032410489399050345387 6456048615734098575518081)
  ·
    refine ⟨4842036461800573931638561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6456048615734098575518081 4842036461800573931638561)
    ·
      refine ⟨3631527346350430448728921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4842036461800573931638561 3631527346350430448728921)
      ·
        refine ⟨2723645509762822836546691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3631527346350430448728921 2723645509762822836546691)
        ·
          refine ⟨4085468264644234254820037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2723645509762822836546691 4085468264644234254820037)
          ·
            refine ⟨766025299620793922778757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4085468264644234254820037 766025299620793922778757)
            ·
              refine ⟨143629743678898860521017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 766025299620793922778757 143629743678898860521017)
              ·
                refine ⟨107722307759174145390763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 143629743678898860521017 107722307759174145390763)
                ·
                  refine ⟨161583461638761218086145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107722307759174145390763 161583461638761218086145)
                  ·
                    refine ⟨121187596229070913564609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161583461638761218086145 121187596229070913564609)
                    ·
                      refine ⟨90890697171803185173457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121187596229070913564609 90890697171803185173457)
                      ·
                        rfl

theorem cell23_177009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_177009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177009 prefixEnd_177009 := by exact prefixLift 177009
  have htrace : WordTrace (prefixWord ++ tailWord_177009) baseStart_177009 baseEnd_177009 := by
    simpa [prefixWord, tailWord_177009, baseEnd_177009] using wordTrace_append hprefix tailTrace_177009
  have hstable : (prefixWord ++ tailWord_177009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177009).length < 2 ^ (prefixWord ++ tailWord_177009).sum := by decide
  have hdescent : baseEnd_177009 < baseStart_177009 := by decide
  rcases family_descends (prefixWord ++ tailWord_177009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177022 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_177022 : Nat := 118140960795 + 177022 * 2 ^ 59
def prefixEnd_177022 : Nat := 4983230072969 + 3 ^ 40 * 177022 * 2
def baseEnd_177022 : Nat := 90897372420311634310897

theorem tailTrace_177022 : CollatzResearch.WordTrace tailWord_177022 prefixEnd_177022 90897372420311634310897 := by
  unfold tailWord_177022
  simp only [CollatzResearch.WordTrace]
  refine ⟨807065345585875224467665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4304348509791334530494213 807065345585875224467665)
  ·
    refine ⟨605299009189406418350749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 807065345585875224467665 605299009189406418350749)
    ·
      refine ⟨226987128446027406881531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 605299009189406418350749 226987128446027406881531)
      ·
        refine ⟨340480692669041110322297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 226987128446027406881531 340480692669041110322297)
        ·
          refine ⟨255360519501780832741723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 340480692669041110322297 255360519501780832741723)
          ·
            refine ⟨383040779252671249112585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255360519501780832741723 383040779252671249112585)
            ·
              refine ⟨287280584439503436834439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 383040779252671249112585 287280584439503436834439)
              ·
                refine ⟨430920876659255155251659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287280584439503436834439 430920876659255155251659)
                ·
                  refine ⟨646381314988882732877489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 430920876659255155251659 646381314988882732877489)
                  ·
                    refine ⟨484785986241662049658117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 646381314988882732877489 484785986241662049658117)
                    ·
                      refine ⟨90897372420311634310897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 484785986241662049658117 90897372420311634310897)
                      ·
                        rfl

theorem cell23_177022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_177022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177022 prefixEnd_177022 := by exact prefixLift 177022
  have htrace : WordTrace (prefixWord ++ tailWord_177022) baseStart_177022 baseEnd_177022 := by
    simpa [prefixWord, tailWord_177022, baseEnd_177022] using wordTrace_append hprefix tailTrace_177022
  have hstable : (prefixWord ++ tailWord_177022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177022).length < 2 ^ (prefixWord ++ tailWord_177022).sum := by decide
  have hdescent : baseEnd_177022 < baseStart_177022 := by decide
  rcases family_descends (prefixWord ++ tailWord_177022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177026 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_177026 : Nat := 118140960795 + 177026 * 2 ^ 59
def prefixEnd_177026 : Nat := 4983230072969 + 3 ^ 40 * 177026 * 2
def baseEnd_177026 : Nat := 90899426342929618660879

theorem tailTrace_177026 : CollatzResearch.WordTrace tailWord_177026 prefixEnd_177026 90899426342929618660879 := by
  unfold tailWord_177026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614167164168127619721733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4304445771115006985924621 1614167164168127619721733)
  ·
    refine ⟨302656343281523928697825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1614167164168127619721733 302656343281523928697825)
    ·
      refine ⟨226992257461142946523369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302656343281523928697825 226992257461142946523369)
      ·
        refine ⟨170244193095857209892527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 226992257461142946523369 170244193095857209892527)
        ·
          refine ⟨255366289643785814838791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170244193095857209892527 255366289643785814838791)
          ·
            refine ⟨383049434465678722258187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 255366289643785814838791 383049434465678722258187)
            ·
              refine ⟨574574151698518083387281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 383049434465678722258187 574574151698518083387281)
              ·
                refine ⟨430930613773888562540461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 574574151698518083387281 430930613773888562540461)
                ·
                  refine ⟨161598980165208210952673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 430930613773888562540461 161598980165208210952673)
                  ·
                    refine ⟨121199235123906158214505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161598980165208210952673 121199235123906158214505)
                    ·
                      refine ⟨90899426342929618660879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121199235123906158214505 90899426342929618660879)
                      ·
                        rfl

theorem cell23_177026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_177026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177026 prefixEnd_177026 := by exact prefixLift 177026
  have htrace : WordTrace (prefixWord ++ tailWord_177026) baseStart_177026 baseEnd_177026 := by
    simpa [prefixWord, tailWord_177026, baseEnd_177026] using wordTrace_append hprefix tailTrace_177026
  have hstable : (prefixWord ++ tailWord_177026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177026).length < 2 ^ (prefixWord ++ tailWord_177026).sum := by decide
  have hdescent : baseEnd_177026 < baseStart_177026 := by decide
  rcases family_descends (prefixWord ++ tailWord_177026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177046 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_177046 : Nat := 118140960795 + 177046 * 2 ^ 59
def prefixEnd_177046 : Nat := 4983230072969 + 3 ^ 40 * 177046 * 2
def baseEnd_177046 : Nat := 90909695956019540410787

theorem tailTrace_177046 : CollatzResearch.WordTrace tailWord_177046 prefixEnd_177046 90909695956019540410787 := by
  unfold tailWord_177046
  simp only [CollatzResearch.WordTrace]
  refine ⟨403587382287503368413437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4304932077733369263076661 403587382287503368413437)
  ·
    refine ⟨151345268357813763155039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 403587382287503368413437 151345268357813763155039)
    ·
      refine ⟨227017902536720644732559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151345268357813763155039 227017902536720644732559)
      ·
        refine ⟨340526853805080967098839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227017902536720644732559 340526853805080967098839)
        ·
          refine ⟨510790280707621450648259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340526853805080967098839 510790280707621450648259)
          ·
            refine ⟨766185421061432175972389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510790280707621450648259 766185421061432175972389)
            ·
              refine ⟨143659766449018532994823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 766185421061432175972389 143659766449018532994823)
              ·
                refine ⟨215489649673527799492235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143659766449018532994823 215489649673527799492235)
                ·
                  refine ⟨323234474510291699238353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215489649673527799492235 323234474510291699238353)
                  ·
                    refine ⟨242425855882718774428765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 323234474510291699238353 242425855882718774428765)
                    ·
                      refine ⟨90909695956019540410787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242425855882718774428765 90909695956019540410787)
                      ·
                        rfl

theorem cell23_177046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_177046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177046 prefixEnd_177046 := by exact prefixLift 177046
  have htrace : WordTrace (prefixWord ++ tailWord_177046) baseStart_177046 baseEnd_177046 := by
    simpa [prefixWord, tailWord_177046, baseEnd_177046] using wordTrace_append hprefix tailTrace_177046
  have hstable : (prefixWord ++ tailWord_177046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177046).length < 2 ^ (prefixWord ++ tailWord_177046).sum := by decide
  have hdescent : baseEnd_177046 < baseStart_177046 := by decide
  rcases family_descends (prefixWord ++ tailWord_177046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177058 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_177058 : Nat := 118140960795 + 177058 * 2 ^ 59
def prefixEnd_177058 : Nat := 4983230072969 + 3 ^ 40 * 177058 * 2
def baseEnd_177058 : Nat := 30305285907957831153577

theorem tailTrace_177058 : CollatzResearch.WordTrace tailWord_177058 prefixEnd_177058 30305285907957831153577 := by
  unfold tailWord_177058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1614458948139144986012957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4305223861704386629367885 1614458948139144986012957)
  ·
    refine ⟨605422105552179369754859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1614458948139144986012957 605422105552179369754859)
    ·
      refine ⟨908133158328269054632289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 605422105552179369754859 908133158328269054632289)
      ·
        refine ⟨681099868746201790974217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 908133158328269054632289 681099868746201790974217)
        ·
          refine ⟨510824901559651343230663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 681099868746201790974217 510824901559651343230663)
          ·
            refine ⟨766237352339477014845995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 510824901559651343230663 766237352339477014845995)
            ·
              refine ⟨1149356028509215522268993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 766237352339477014845995 1149356028509215522268993)
              ·
                refine ⟨862017021381911641701745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1149356028509215522268993 862017021381911641701745)
                ·
                  refine ⟨646512766036433731276309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 862017021381911641701745 646512766036433731276309)
                  ·
                    refine ⟨30305285907957831153577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 646512766036433731276309 30305285907957831153577)
                    ·
                      rfl

theorem cell23_177058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_177058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177058 prefixEnd_177058 := by exact prefixLift 177058
  have htrace : WordTrace (prefixWord ++ tailWord_177058) baseStart_177058 baseEnd_177058 := by
    simpa [prefixWord, tailWord_177058, baseEnd_177058] using wordTrace_append hprefix tailTrace_177058
  have hstable : (prefixWord ++ tailWord_177058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177058).length < 2 ^ (prefixWord ++ tailWord_177058).sum := by decide
  have hdescent : baseEnd_177058 < baseStart_177058 := by decide
  rcases family_descends (prefixWord ++ tailWord_177058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177065 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 4, 2, 2]
def baseStart_177065 : Nat := 118140960795 + 177065 * 2 ^ 59
def prefixEnd_177065 : Nat := 4983230072969 + 3 ^ 40 * 177065 * 2
def baseEnd_177065 : Nat := 90919452088454966073199

theorem tailTrace_177065 : CollatzResearch.WordTrace tailWord_177065 prefixEnd_177065 90919452088454966073199 := by
  unfold tailWord_177065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6458091103531220139556649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4305394069020813426371099 6458091103531220139556649)
  ·
    refine ⟨4843568327648415104667487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6458091103531220139556649 4843568327648415104667487)
    ·
      refine ⟨7265352491472622657001231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4843568327648415104667487 7265352491472622657001231)
      ·
        refine ⟨10898028737208933985501847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7265352491472622657001231 10898028737208933985501847)
        ·
          refine ⟨16347043105813400978252771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10898028737208933985501847 16347043105813400978252771)
          ·
            refine ⟨24520564658720101467379157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16347043105813400978252771 24520564658720101467379157)
            ·
              refine ⟨574700734188752378141699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 24520564658720101467379157 574700734188752378141699)
              ·
                refine ⟨862051101283128567212549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 574700734188752378141699 862051101283128567212549)
                ·
                  refine ⟨161634581490586606352353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 862051101283128567212549 161634581490586606352353)
                  ·
                    refine ⟨121225936117939954764265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161634581490586606352353 121225936117939954764265)
                    ·
                      refine ⟨90919452088454966073199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121225936117939954764265 90919452088454966073199)
                      ·
                        rfl

theorem cell23_177065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2, 2].length) (baseStart_177065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177065 prefixEnd_177065 := by exact prefixLift 177065
  have htrace : WordTrace (prefixWord ++ tailWord_177065) baseStart_177065 baseEnd_177065 := by
    simpa [prefixWord, tailWord_177065, baseEnd_177065] using wordTrace_append hprefix tailTrace_177065
  have hstable : (prefixWord ++ tailWord_177065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177065).length < 2 ^ (prefixWord ++ tailWord_177065).sum := by decide
  have hdescent : baseEnd_177065 < baseStart_177065 := by decide
  rcases family_descends (prefixWord ++ tailWord_177065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177076 : List Nat := [2, 5, 2, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_177076 : Nat := 118140960795 + 177076 * 2 ^ 59
def prefixEnd_177076 : Nat := 4983230072969 + 3 ^ 40 * 177076 * 2
def baseEnd_177076 : Nat := 90925100375654423035649

theorem tailTrace_177076 : CollatzResearch.WordTrace tailWord_177076 prefixEnd_177076 90925100375654423035649 := by
  unfold tailWord_177076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3229246153245684509103541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4305661537660912678804721 3229246153245684509103541)
  ·
    refine ⟨302741826866782922728457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3229246153245684509103541 302741826866782922728457)
    ·
      refine ⟨227056370150087192046343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 302741826866782922728457 227056370150087192046343)
      ·
        refine ⟨340584555225130788069515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227056370150087192046343 340584555225130788069515)
        ·
          refine ⟨510876832837696182104273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340584555225130788069515 510876832837696182104273)
          ·
            refine ⟨383157624628272136578205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 510876832837696182104273 383157624628272136578205)
            ·
              refine ⟨143684109235602051216827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383157624628272136578205 143684109235602051216827)
              ·
                refine ⟨215526163853403076825241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143684109235602051216827 215526163853403076825241)
                ·
                  refine ⟨161644622890052307618931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215526163853403076825241 161644622890052307618931)
                  ·
                    refine ⟨242466934335078461428397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161644622890052307618931 242466934335078461428397)
                    ·
                      refine ⟨90925100375654423035649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242466934335078461428397 90925100375654423035649)
                      ·
                        rfl

theorem cell23_177076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_177076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177076 prefixEnd_177076 := by exact prefixLift 177076
  have htrace : WordTrace (prefixWord ++ tailWord_177076) baseStart_177076 baseEnd_177076 := by
    simpa [prefixWord, tailWord_177076, baseEnd_177076] using wordTrace_append hprefix tailTrace_177076
  have hstable : (prefixWord ++ tailWord_177076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177076).length < 2 ^ (prefixWord ++ tailWord_177076).sum := by decide
  have hdescent : baseEnd_177076 < baseStart_177076 := by decide
  rcases family_descends (prefixWord ++ tailWord_177076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177094 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2]
def baseStart_177094 : Nat := 118140960795 + 177094 * 2 ^ 59
def prefixEnd_177094 : Nat := 4983230072969 + 3 ^ 40 * 177094 * 2
def baseEnd_177094 : Nat := 90934343027435352610567

theorem tailTrace_177094 : CollatzResearch.WordTrace tailWord_177094 prefixEnd_177094 90934343027435352610567 := by
  unfold tailWord_177094
  simp only [CollatzResearch.WordTrace]
  refine ⟨201848400638317440386323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4306099213617438728241557 201848400638317440386323)
  ·
    refine ⟨302772600957476160579485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 201848400638317440386323 302772600957476160579485)
    ·
      refine ⟨113539725359053560217307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 302772600957476160579485 113539725359053560217307)
      ·
        refine ⟨170309588038580340325961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113539725359053560217307 170309588038580340325961)
        ·
          refine ⟨127732191028935255244471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170309588038580340325961 127732191028935255244471)
          ·
            refine ⟨191598286543402882866707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127732191028935255244471 191598286543402882866707)
            ·
              refine ⟨287397429815104324300061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191598286543402882866707 287397429815104324300061)
              ·
                refine ⟨107774036180664121612523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287397429815104324300061 107774036180664121612523)
                ·
                  refine ⟨161661054270996182418785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107774036180664121612523 161661054270996182418785)
                  ·
                    refine ⟨121245790703247136814089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 161661054270996182418785 121245790703247136814089)
                    ·
                      refine ⟨90934343027435352610567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121245790703247136814089 90934343027435352610567)
                      ·
                        rfl

theorem cell23_177094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_177094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177094 prefixEnd_177094 := by exact prefixLift 177094
  have htrace : WordTrace (prefixWord ++ tailWord_177094) baseStart_177094 baseEnd_177094 := by
    simpa [prefixWord, tailWord_177094, baseEnd_177094] using wordTrace_append hprefix tailTrace_177094
  have hstable : (prefixWord ++ tailWord_177094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177094).length < 2 ^ (prefixWord ++ tailWord_177094).sum := by decide
  have hdescent : baseEnd_177094 < baseStart_177094 := by decide
  rcases family_descends (prefixWord ++ tailWord_177094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177122 : List Nat := [3, 3, 3, 1, 1, 3, 1, 1, 7]
def baseStart_177122 : Nat := 118140960795 + 177122 * 2 ^ 59
def prefixEnd_177122 : Nat := 4983230072969 + 3 ^ 40 * 177122 * 2
def baseEnd_177122 : Nat := 10105413387306804784493

theorem tailTrace_177122 : CollatzResearch.WordTrace tailWord_177122 prefixEnd_177122 10105413387306804784493 := by
  unfold tailWord_177122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1615042516081179718595405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4306780042883145916254413 1615042516081179718595405)
  ·
    refine ⟨605640943530442394473277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1615042516081179718595405 605640943530442394473277)
    ·
      refine ⟨227115353823915897927479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 605640943530442394473277 227115353823915897927479)
      ·
        refine ⟨340673030735873846891219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227115353823915897927479 340673030735873846891219)
        ·
          refine ⟨511009546103810770336829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340673030735873846891219 511009546103810770336829)
          ·
            refine ⟨191628579788929038876311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511009546103810770336829 191628579788929038876311)
            ·
              refine ⟨287442869683393558314467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191628579788929038876311 287442869683393558314467)
              ·
                refine ⟨431164304525090337471701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287442869683393558314467 431164304525090337471701)
                ·
                  refine ⟨10105413387306804784493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 431164304525090337471701 10105413387306804784493)
                  ·
                    rfl

theorem cell23_177122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_177122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177122 prefixEnd_177122 := by exact prefixLift 177122
  have htrace : WordTrace (prefixWord ++ tailWord_177122) baseStart_177122 baseEnd_177122 := by
    simpa [prefixWord, tailWord_177122, baseEnd_177122] using wordTrace_append hprefix tailTrace_177122
  have hstable : (prefixWord ++ tailWord_177122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177122).length < 2 ^ (prefixWord ++ tailWord_177122).sum := by decide
  have hdescent : baseEnd_177122 < baseStart_177122 := by decide
  rcases family_descends (prefixWord ++ tailWord_177122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177151 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6]
def baseStart_177151 : Nat := 118140960795 + 177151 * 2 ^ 59
def prefixEnd_177151 : Nat := 4983230072969 + 3 ^ 40 * 177151 * 2
def baseEnd_177151 : Nat := 90963611424741629597803

theorem tailTrace_177151 : CollatzResearch.WordTrace tailWord_177151 prefixEnd_177151 90963611424741629597803 := by
  unfold tailWord_177151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461227781219656827187307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4307485187479771218124871 6461227781219656827187307)
  ·
    refine ⟨9691841671829485240780961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6461227781219656827187307 9691841671829485240780961)
    ·
      refine ⟨7268881253872113930585721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9691841671829485240780961 7268881253872113930585721)
      ·
        refine ⟨5451660940404085447939291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7268881253872113930585721 5451660940404085447939291)
        ·
          refine ⟨8177491410606128171908937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451660940404085447939291 8177491410606128171908937)
          ·
            refine ⟨6133118557954596128931703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8177491410606128171908937 6133118557954596128931703)
            ·
              refine ⟨9199677836931894193397555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133118557954596128931703 9199677836931894193397555)
              ·
                refine ⟨13799516755397841290096333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199677836931894193397555 13799516755397841290096333)
                ·
                  refine ⟨5174818783274190483786125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13799516755397841290096333 5174818783274190483786125)
                  ·
                    refine ⟨1940557043727821431419797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5174818783274190483786125 1940557043727821431419797)
                    ·
                      refine ⟨90963611424741629597803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1940557043727821431419797 90963611424741629597803)
                      ·
                        rfl

theorem cell23_177151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_177151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177151 prefixEnd_177151 := by exact prefixLift 177151
  have htrace : WordTrace (prefixWord ++ tailWord_177151) baseStart_177151 baseEnd_177151 := by
    simpa [prefixWord, tailWord_177151, baseEnd_177151] using wordTrace_append hprefix tailTrace_177151
  have hstable : (prefixWord ++ tailWord_177151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177151).length < 2 ^ (prefixWord ++ tailWord_177151).sum := by decide
  have hdescent : baseEnd_177151 < baseStart_177151 := by decide
  rcases family_descends (prefixWord ++ tailWord_177151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177161 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 10]
def baseStart_177161 : Nat := 118140960795 + 177161 * 2 ^ 59
def prefixEnd_177161 : Nat := 4983230072969 + 3 ^ 40 * 177161 * 2
def baseEnd_177161 : Nat := 10107638470142954496973

theorem tailTrace_177161 : CollatzResearch.WordTrace tailWord_177161 prefixEnd_177161 10107638470142954496973 := by
  unfold tailWord_177161
  simp only [CollatzResearch.WordTrace]
  refine ⟨6461592511183428535051337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4307728340788952356700891 6461592511183428535051337)
  ·
    refine ⟨4846194383387571401288503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6461592511183428535051337 4846194383387571401288503)
    ·
      refine ⟨7269291575081357101932755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846194383387571401288503 7269291575081357101932755)
      ·
        refine ⟨10903937362622035652899133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269291575081357101932755 10903937362622035652899133)
        ·
          refine ⟨4088976510983263369837175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10903937362622035652899133 4088976510983263369837175)
          ·
            refine ⟨6133464766474895054755763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088976510983263369837175 6133464766474895054755763)
            ·
              refine ⟨9200197149712342582133645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133464766474895054755763 9200197149712342582133645)
              ·
                refine ⟨3450073931142128468300117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9200197149712342582133645 3450073931142128468300117)
                ·
                  refine ⟨10107638470142954496973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 3450073931142128468300117 10107638470142954496973)
                  ·
                    rfl

theorem cell23_177161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 10].length) (baseStart_177161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177161 prefixEnd_177161 := by exact prefixLift 177161
  have htrace : WordTrace (prefixWord ++ tailWord_177161) baseStart_177161 baseEnd_177161 := by
    simpa [prefixWord, tailWord_177161, baseEnd_177161] using wordTrace_append hprefix tailTrace_177161
  have hstable : (prefixWord ++ tailWord_177161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177161).length < 2 ^ (prefixWord ++ tailWord_177161).sum := by decide
  have hdescent : baseEnd_177161 < baseStart_177161 := by decide
  rcases family_descends (prefixWord ++ tailWord_177161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177246 : List Nat := [4, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_177246 : Nat := 118140960795 + 177246 * 2 ^ 59
def prefixEnd_177246 : Nat := 4983230072969 + 3 ^ 40 * 177246 * 2
def baseEnd_177246 : Nat := 10112488009657639767763

theorem tailTrace_177246 : CollatzResearch.WordTrace tailWord_177246 prefixEnd_177246 10112488009657639767763 := by
  unfold tailWord_177246
  simp only [CollatzResearch.WordTrace]
  refine ⟨808086589484436006486949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4309795143916992034597061 808086589484436006486949)
  ·
    refine ⟨151516235528331751216303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 808086589484436006486949 151516235528331751216303)
    ·
      refine ⟨227274353292497626824455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151516235528331751216303 227274353292497626824455)
      ·
        refine ⟨340911529938746440236683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227274353292497626824455 340911529938746440236683)
        ·
          refine ⟨511367294908119660355025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 340911529938746440236683 511367294908119660355025)
          ·
            refine ⟨383525471181089745266269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 511367294908119660355025 383525471181089745266269)
            ·
              refine ⟨143822051692908654474851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 383525471181089745266269 143822051692908654474851)
              ·
                refine ⟨215733077539362981712277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143822051692908654474851 215733077539362981712277)
                ·
                  refine ⟨10112488009657639767763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 215733077539362981712277 10112488009657639767763)
                  ·
                    rfl

theorem cell23_177246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_177246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177246 prefixEnd_177246 := by exact prefixLift 177246
  have htrace : WordTrace (prefixWord ++ tailWord_177246) baseStart_177246 baseEnd_177246 := by
    simpa [prefixWord, tailWord_177246, baseEnd_177246] using wordTrace_append hprefix tailTrace_177246
  have hstable : (prefixWord ++ tailWord_177246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177246).length < 2 ^ (prefixWord ++ tailWord_177246).sum := by decide
  have hdescent : baseEnd_177246 < baseStart_177246 := by decide
  rcases family_descends (prefixWord ++ tailWord_177246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177255 : List Nat := [1, 1, 5, 1, 1, 3, 3, 1, 1, 6]
def baseStart_177255 : Nat := 118140960795 + 177255 * 2 ^ 59
def prefixEnd_177255 : Nat := 4983230072969 + 3 ^ 40 * 177255 * 2
def baseEnd_177255 : Nat := 30339004470936407565775

theorem tailTrace_177255 : CollatzResearch.WordTrace tailWord_177255 prefixEnd_177255 30339004470936407565775 := by
  unfold tailWord_177255
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465020972842882588973219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4310013981895255059315479 6465020972842882588973219)
  ·
    refine ⟨9697531459264323883459829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6465020972842882588973219 9697531459264323883459829)
    ·
      refine ⟨909143574306030364074359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9697531459264323883459829 909143574306030364074359)
      ·
        refine ⟨1363715361459045546111539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 909143574306030364074359 1363715361459045546111539)
        ·
          refine ⟨2045573042188568319167309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1363715361459045546111539 2045573042188568319167309)
          ·
            refine ⟨767089890820713119687741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2045573042188568319167309 767089890820713119687741)
            ·
              refine ⟨287658709057767419882903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 767089890820713119687741 287658709057767419882903)
              ·
                refine ⟨431488063586651129824355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287658709057767419882903 431488063586651129824355)
                ·
                  refine ⟨647232095379976694736533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 431488063586651129824355 647232095379976694736533)
                  ·
                    refine ⟨30339004470936407565775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 647232095379976694736533 30339004470936407565775)
                    ·
                      rfl

theorem cell23_177255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_177255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177255 prefixEnd_177255 := by exact prefixLift 177255
  have htrace : WordTrace (prefixWord ++ tailWord_177255) baseStart_177255 baseEnd_177255 := by
    simpa [prefixWord, tailWord_177255, baseEnd_177255] using wordTrace_append hprefix tailTrace_177255
  have hstable : (prefixWord ++ tailWord_177255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177255).length < 2 ^ (prefixWord ++ tailWord_177255).sum := by decide
  have hdescent : baseEnd_177255 < baseStart_177255 := by decide
  rcases family_descends (prefixWord ++ tailWord_177255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177262 : List Nat := [4, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_177262 : Nat := 118140960795 + 177262 * 2 ^ 59
def prefixEnd_177262 : Nat := 4983230072969 + 3 ^ 40 * 177262 * 2
def baseEnd_177262 : Nat := 91020607777390695309793

theorem tailTrace_177262 : CollatzResearch.WordTrace tailWord_177262 prefixEnd_177262 91020607777390695309793 := by
  unfold tailWord_177262
  simp only [CollatzResearch.WordTrace]
  refine ⟨808159535477190348059755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4310184189211681856318693 808159535477190348059755)
  ·
    refine ⟨1212239303215785522089633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 808159535477190348059755 1212239303215785522089633)
    ·
      refine ⟨909179477411839141567225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1212239303215785522089633 909179477411839141567225)
      ·
        refine ⟨681884608058879356175419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 909179477411839141567225 681884608058879356175419)
        ·
          refine ⟨1022826912088319034263129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681884608058879356175419 1022826912088319034263129)
          ·
            refine ⟨767120184066239275697347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1022826912088319034263129 767120184066239275697347)
            ·
              refine ⟨1150680276099358913546021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 767120184066239275697347 1150680276099358913546021)
              ·
                refine ⟨215752551768629796289879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1150680276099358913546021 215752551768629796289879)
                ·
                  refine ⟨323628827652944694434819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 215752551768629796289879 323628827652944694434819)
                  ·
                    refine ⟨485443241479417041652229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 323628827652944694434819 485443241479417041652229)
                    ·
                      refine ⟨91020607777390695309793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 485443241479417041652229 91020607777390695309793)
                      ·
                        rfl

theorem cell23_177262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_177262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177262 prefixEnd_177262 := by exact prefixLift 177262
  have htrace : WordTrace (prefixWord ++ tailWord_177262) baseStart_177262 baseEnd_177262 := by
    simpa [prefixWord, tailWord_177262, baseEnd_177262] using wordTrace_append hprefix tailTrace_177262
  have hstable : (prefixWord ++ tailWord_177262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177262).length < 2 ^ (prefixWord ++ tailWord_177262).sum := by decide
  have hdescent : baseEnd_177262 < baseStart_177262 := by decide
  rcases family_descends (prefixWord ++ tailWord_177262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177273 : List Nat := [1, 2, 1, 3, 6, 1, 1, 3, 1, 1, 3]
def baseStart_177273 : Nat := 118140960795 + 177273 * 2 ^ 59
def prefixEnd_177273 : Nat := 4983230072969 + 3 ^ 40 * 177273 * 2
def baseEnd_177273 : Nat := 91026256064590152272243

theorem tailTrace_177273 : CollatzResearch.WordTrace tailWord_177273 prefixEnd_177273 91026256064590152272243 := by
  unfold tailWord_177273
  simp only [CollatzResearch.WordTrace]
  refine ⟨6465677486777671663128473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4310451657851781108752315 6465677486777671663128473)
  ·
    refine ⟨4849258115083253747346355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6465677486777671663128473 4849258115083253747346355)
    ·
      refine ⟨7273887172624880621019533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4849258115083253747346355 7273887172624880621019533)
      ·
        refine ⟨2727707689734330232882325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7273887172624880621019533 2727707689734330232882325)
        ·
          refine ⟨127861297956296729666359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2727707689734330232882325 127861297956296729666359)
          ·
            refine ⟨191791946934445094499539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127861297956296729666359 191791946934445094499539)
            ·
              refine ⟨287687920401667641749309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 191791946934445094499539 287687920401667641749309)
              ·
                refine ⟨107882970150625365655991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 287687920401667641749309 107882970150625365655991)
                ·
                  refine ⟨161824455225938048483987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 107882970150625365655991 161824455225938048483987)
                  ·
                    refine ⟨242736682838907072725981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 161824455225938048483987 242736682838907072725981)
                    ·
                      refine ⟨91026256064590152272243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242736682838907072725981 91026256064590152272243)
                      ·
                        rfl

theorem cell23_177273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_177273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177273 prefixEnd_177273 := by exact prefixLift 177273
  have htrace : WordTrace (prefixWord ++ tailWord_177273) baseStart_177273 baseEnd_177273 := by
    simpa [prefixWord, tailWord_177273, baseEnd_177273] using wordTrace_append hprefix tailTrace_177273
  have hstable : (prefixWord ++ tailWord_177273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177273).length < 2 ^ (prefixWord ++ tailWord_177273).sum := by decide
  have hdescent : baseEnd_177273 < baseStart_177273 := by decide
  rcases family_descends (prefixWord ++ tailWord_177273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177285 : List Nat := [1, 3, 1, 1, 6, 2, 9]
def baseStart_177285 : Nat := 118140960795 + 177285 * 2 ^ 59
def prefixEnd_177285 : Nat := 4983230072969 + 3 ^ 40 * 177285 * 2
def baseEnd_177285 : Nat := 1123857010277087720027

theorem tailTrace_177285 : CollatzResearch.WordTrace tailWord_177285 prefixEnd_177285 1123857010277087720027 := by
  unfold tailWord_177285
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466115162734197712565309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4310743441822798475043539 6466115162734197712565309)
  ·
    refine ⟨2424793186025324142211991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6466115162734197712565309 2424793186025324142211991)
    ·
      refine ⟨3637189779037986213317987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2424793186025324142211991 3637189779037986213317987)
      ·
        refine ⟨5455784668556979319976981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637189779037986213317987 5455784668556979319976981)
        ·
          refine ⟨255739906338608405623921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5455784668556979319976981 255739906338608405623921)
          ·
            refine ⟨191804929753956304217941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 255739906338608405623921 191804929753956304217941)
            ·
              refine ⟨1123857010277087720027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 191804929753956304217941 1123857010277087720027)
              ·
                rfl

theorem cell23_177285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 9].length) (baseStart_177285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177285 prefixEnd_177285 := by exact prefixLift 177285
  have htrace : WordTrace (prefixWord ++ tailWord_177285) baseStart_177285 baseEnd_177285 := by
    simpa [prefixWord, tailWord_177285, baseEnd_177285] using wordTrace_append hprefix tailTrace_177285
  have hstable : (prefixWord ++ tailWord_177285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177285).length < 2 ^ (prefixWord ++ tailWord_177285).sum := by decide
  have hdescent : baseEnd_177285 < baseStart_177285 := by decide
  rcases family_descends (prefixWord ++ tailWord_177285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177305 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 1, 9, 2]
def baseStart_177305 : Nat := 118140960795 + 177305 * 2 ^ 59
def prefixEnd_177305 : Nat := 4983230072969 + 3 ^ 40 * 177305 * 2
def baseEnd_177305 : Nat := 91042687445534027072095

theorem tailTrace_177305 : CollatzResearch.WordTrace tailWord_177305 prefixEnd_177305 91042687445534027072095 := by
  unfold tailWord_177305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6466844622661741128293369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4311229748441160752195579 6466844622661741128293369)
  ·
    refine ⟨4850133466996305846220027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6466844622661741128293369 4850133466996305846220027)
    ·
      refine ⟨7275200200494458769330041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4850133466996305846220027 7275200200494458769330041)
      ·
        refine ⟨5456400150370844076997531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7275200200494458769330041 5456400150370844076997531)
        ·
          refine ⟨8184600225556266115496297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456400150370844076997531 8184600225556266115496297)
          ·
            refine ⟨6138450169167199586622223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184600225556266115496297 6138450169167199586622223)
            ·
              refine ⟨9207675253750799379933335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6138450169167199586622223 9207675253750799379933335)
              ·
                refine ⟨13811512880626199069900003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9207675253750799379933335 13811512880626199069900003)
                ·
                  refine ⟨20717269320939298604850005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13811512880626199069900003 20717269320939298604850005)
                  ·
                    refine ⟨121390249927378702762793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 20717269320939298604850005 121390249927378702762793)
                    ·
                      refine ⟨91042687445534027072095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121390249927378702762793 91042687445534027072095)
                      ·
                        rfl

theorem cell23_177305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9, 2].length) (baseStart_177305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177305 prefixEnd_177305 := by exact prefixLift 177305
  have htrace : WordTrace (prefixWord ++ tailWord_177305) baseStart_177305 baseEnd_177305 := by
    simpa [prefixWord, tailWord_177305, baseEnd_177305] using wordTrace_append hprefix tailTrace_177305
  have hstable : (prefixWord ++ tailWord_177305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177305).length < 2 ^ (prefixWord ++ tailWord_177305).sum := by decide
  have hdescent : baseEnd_177305 < baseStart_177305 := by decide
  rcases family_descends (prefixWord ++ tailWord_177305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177306 : List Nat := [3, 1, 1, 5, 1, 3, 2, 1, 2, 4]
def baseStart_177306 : Nat := 118140960795 + 177306 * 2 ^ 59
def prefixEnd_177306 : Nat := 4983230072969 + 3 ^ 40 * 177306 * 2
def baseEnd_177306 : Nat := 30347733642062841053197

theorem tailTrace_177306 : CollatzResearch.WordTrace tailWord_177306 prefixEnd_177306 30347733642062841053197 := by
  unfold tailWord_177306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1616720273914529574769943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4311254063772078866053181 1616720273914529574769943)
  ·
    refine ⟨2425080410871794362154915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1616720273914529574769943 2425080410871794362154915)
    ·
      refine ⟨3637620616307691543232373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2425080410871794362154915 3637620616307691543232373)
      ·
        refine ⟨341026932778846082178035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3637620616307691543232373 341026932778846082178035)
        ·
          refine ⟨511540399168269123267053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341026932778846082178035 511540399168269123267053)
          ·
            refine ⟨191827649688100921225145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 511540399168269123267053 191827649688100921225145)
            ·
              refine ⟨143870737266075690918859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191827649688100921225145 143870737266075690918859)
              ·
                refine ⟨215806105899113536378289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143870737266075690918859 215806105899113536378289)
                ·
                  refine ⟨161854579424335152283717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 215806105899113536378289 161854579424335152283717)
                  ·
                    refine ⟨30347733642062841053197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 161854579424335152283717 30347733642062841053197)
                    ·
                      rfl

theorem cell23_177306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_177306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177306 prefixEnd_177306 := by exact prefixLift 177306
  have htrace : WordTrace (prefixWord ++ tailWord_177306) baseStart_177306 baseEnd_177306 := by
    simpa [prefixWord, tailWord_177306, baseEnd_177306] using wordTrace_append hprefix tailTrace_177306
  have hstable : (prefixWord ++ tailWord_177306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177306).length < 2 ^ (prefixWord ++ tailWord_177306).sum := by decide
  have hdescent : baseEnd_177306 < baseStart_177306 := by decide
  rcases family_descends (prefixWord ++ tailWord_177306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177328 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 8]
def baseStart_177328 : Nat := 118140960795 + 177328 * 2 ^ 59
def prefixEnd_177328 : Nat := 4983230072969 + 3 ^ 40 * 177328 * 2
def baseEnd_177328 : Nat := 30351499166862479028163

theorem tailTrace_177328 : CollatzResearch.WordTrace tailWord_177328 prefixEnd_177328 30351499166862479028163 := by
  unfold tailWord_177328
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233841750789208028190319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4311789001052277370920425 3233841750789208028190319)
  ·
    refine ⟨4850762626183812042285479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233841750789208028190319 4850762626183812042285479)
    ·
      refine ⟨7276143939275718063428219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4850762626183812042285479 7276143939275718063428219)
      ·
        refine ⟨10914215908913577095142329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7276143939275718063428219 10914215908913577095142329)
        ·
          refine ⟨8185661931685182821356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10914215908913577095142329 8185661931685182821356747)
          ·
            refine ⟨12278492897527774232035121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8185661931685182821356747 12278492897527774232035121)
            ·
              refine ⟨9208869673145830674026341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12278492897527774232035121 9208869673145830674026341)
              ·
                refine ⟨1726663063714843251379939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9208869673145830674026341 1726663063714843251379939)
                ·
                  refine ⟨2589994595572264877069909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1726663063714843251379939 2589994595572264877069909)
                  ·
                    refine ⟨30351499166862479028163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2589994595572264877069909 30351499166862479028163)
                    ·
                      rfl

theorem cell23_177328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_177328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177328 prefixEnd_177328 := by exact prefixLift 177328
  have htrace : WordTrace (prefixWord ++ tailWord_177328) baseStart_177328 baseEnd_177328 := by
    simpa [prefixWord, tailWord_177328, baseEnd_177328] using wordTrace_append hprefix tailTrace_177328
  have hstable : (prefixWord ++ tailWord_177328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177328).length < 2 ^ (prefixWord ++ tailWord_177328).sum := by decide
  have hdescent : baseEnd_177328 < baseStart_177328 := by decide
  rcases family_descends (prefixWord ++ tailWord_177328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177385 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 3]
def baseStart_177385 : Nat := 118140960795 + 177385 * 2 ^ 59
def prefixEnd_177385 : Nat := 4983230072969 + 3 ^ 40 * 177385 * 2
def baseEnd_177385 : Nat := 91083765897893714071727

theorem tailTrace_177385 : CollatzResearch.WordTrace tailWord_177385 prefixEnd_177385 91083765897893714071727 := by
  unfold tailWord_177385
  simp only [CollatzResearch.WordTrace]
  refine ⟨6469762462371914791205609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4313174974914609860803739 6469762462371914791205609)
  ·
    refine ⟨4852321846778936093404207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6469762462371914791205609 4852321846778936093404207)
    ·
      refine ⟨7278482770168404140106311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4852321846778936093404207 7278482770168404140106311)
      ·
        refine ⟨10917724155252606210159467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7278482770168404140106311 10917724155252606210159467)
        ·
          refine ⟨16376586232878909315239201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10917724155252606210159467 16376586232878909315239201)
          ·
            refine ⟨12282439674659181986429401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16376586232878909315239201 12282439674659181986429401)
            ·
              refine ⟨9211829755994386489822051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12282439674659181986429401 9211829755994386489822051)
              ·
                refine ⟨13817744633991579734733077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9211829755994386489822051 13817744633991579734733077)
                ·
                  refine ⟨647706779718355300065613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13817744633991579734733077 647706779718355300065613)
                  ·
                    refine ⟨242890042394383237524605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 647706779718355300065613 242890042394383237524605)
                    ·
                      refine ⟨91083765897893714071727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 242890042394383237524605 91083765897893714071727)
                      ·
                        rfl

theorem cell23_177385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 3, 3].length) (baseStart_177385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177385 prefixEnd_177385 := by exact prefixLift 177385
  have htrace : WordTrace (prefixWord ++ tailWord_177385) baseStart_177385 baseEnd_177385 := by
    simpa [prefixWord, tailWord_177385, baseEnd_177385] using wordTrace_append hprefix tailTrace_177385
  have hstable : (prefixWord ++ tailWord_177385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177385).length < 2 ^ (prefixWord ++ tailWord_177385).sum := by decide
  have hdescent : baseEnd_177385 < baseStart_177385 := by decide
  rcases family_descends (prefixWord ++ tailWord_177385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177425 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 4]
def baseStart_177425 : Nat := 118140960795 + 177425 * 2 ^ 59
def prefixEnd_177425 : Nat := 4983230072969 + 3 ^ 40 * 177425 * 2
def baseEnd_177425 : Nat := 91104305124073557571543

theorem tailTrace_177425 : CollatzResearch.WordTrace tailWord_177425 prefixEnd_177425 91104305124073557571543 := by
  unfold tailWord_177425
  simp only [CollatzResearch.WordTrace]
  refine ⟨6471221382227001622661729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4314147588151334415107819 6471221382227001622661729)
  ·
    refine ⟨4853416036670251216996297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6471221382227001622661729 4853416036670251216996297)
    ·
      refine ⟨3640062027502688412747223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4853416036670251216996297 3640062027502688412747223)
      ·
        refine ⟨5460093041254032619120835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3640062027502688412747223 5460093041254032619120835)
        ·
          refine ⟨8190139561881048928681253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5460093041254032619120835 8190139561881048928681253)
          ·
            refine ⟨1535651167852696674127735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8190139561881048928681253 1535651167852696674127735)
            ·
              refine ⟨2303476751779045011191603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1535651167852696674127735 2303476751779045011191603)
              ·
                refine ⟨3455215127668567516787405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2303476751779045011191603 3455215127668567516787405)
                ·
                  refine ⟨1295705672875712818795277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3455215127668567516787405 1295705672875712818795277)
                  ·
                    refine ⟨485889627328392307048229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1295705672875712818795277 485889627328392307048229)
                    ·
                      refine ⟨91104305124073557571543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 485889627328392307048229 91104305124073557571543)
                      ·
                        rfl

theorem cell23_177425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_177425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177425 prefixEnd_177425 := by exact prefixLift 177425
  have htrace : WordTrace (prefixWord ++ tailWord_177425) baseStart_177425 baseEnd_177425 := by
    simpa [prefixWord, tailWord_177425, baseEnd_177425] using wordTrace_append hprefix tailTrace_177425
  have hstable : (prefixWord ++ tailWord_177425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177425).length < 2 ^ (prefixWord ++ tailWord_177425).sum := by decide
  have hdescent : baseEnd_177425 < baseStart_177425 := by decide
  rcases family_descends (prefixWord ++ tailWord_177425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177505 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 7]
def baseStart_177505 : Nat := 118140960795 + 177505 * 2 ^ 59
def prefixEnd_177505 : Nat := 4983230072969 + 3 ^ 40 * 177505 * 2
def baseEnd_177505 : Nat := 91145383576433244571175

theorem tailTrace_177505 : CollatzResearch.WordTrace tailWord_177505 prefixEnd_177505 91145383576433244571175 := by
  unfold tailWord_177505
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474139221937175285573969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4316092814624783523715979 6474139221937175285573969)
  ·
    refine ⟨4855604416452881464180477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6474139221937175285573969 4855604416452881464180477)
    ·
      refine ⟨1820851656169830549067679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4855604416452881464180477 1820851656169830549067679)
      ·
        refine ⟨2731277484254745823601519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1820851656169830549067679 2731277484254745823601519)
        ·
          refine ⟨4096916226382118735402279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731277484254745823601519 4096916226382118735402279)
          ·
            refine ⟨6145374339573178103103419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4096916226382118735402279 6145374339573178103103419)
            ·
              refine ⟨9218061509359767154655129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6145374339573178103103419 9218061509359767154655129)
              ·
                refine ⟨6913546132019825365991347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9218061509359767154655129 6913546132019825365991347)
                ·
                  refine ⟨10370319198029738048987021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6913546132019825365991347 10370319198029738048987021)
                  ·
                    refine ⟨3888869699261151768370133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10370319198029738048987021 3888869699261151768370133)
                    ·
                      refine ⟨91145383576433244571175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3888869699261151768370133 91145383576433244571175)
                      ·
                        rfl

theorem cell23_177505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_177505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177505 prefixEnd_177505 := by exact prefixLift 177505
  have htrace : WordTrace (prefixWord ++ tailWord_177505) baseStart_177505 baseEnd_177505 := by
    simpa [prefixWord, tailWord_177505, baseEnd_177505] using wordTrace_append hprefix tailTrace_177505
  have hstable : (prefixWord ++ tailWord_177505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177505).length < 2 ^ (prefixWord ++ tailWord_177505).sum := by decide
  have hdescent : baseEnd_177505 < baseStart_177505 := by decide
  rcases family_descends (prefixWord ++ tailWord_177505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177519 : List Nat := [1, 1, 2, 1, 3, 1, 3, 4, 2, 3, 2]
def baseStart_177519 : Nat := 118140960795 + 177519 * 2 ^ 59
def prefixEnd_177519 : Nat := 4983230072969 + 3 ^ 40 * 177519 * 2
def baseEnd_177519 : Nat := 91152572305596189796111

theorem tailTrace_177519 : CollatzResearch.WordTrace tailWord_177519 prefixEnd_177519 91152572305596189796111 := by
  unfold tailWord_177519
  simp only [CollatzResearch.WordTrace]
  refine ⟨6474649843886455676583611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4316433229257637117722407 6474649843886455676583611)
  ·
    refine ⟨9711974765829683514875417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6474649843886455676583611 9711974765829683514875417)
    ·
      refine ⟨7283981074372262636156563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9711974765829683514875417 7283981074372262636156563)
      ·
        refine ⟨10925971611558393954234845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7283981074372262636156563 10925971611558393954234845)
        ·
          refine ⟨4097239354334397732838067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10925971611558393954234845 4097239354334397732838067)
          ·
            refine ⟨6145859031501596599257101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097239354334397732838067 6145859031501596599257101)
            ·
              refine ⟨2304697136813098724721413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6145859031501596599257101 2304697136813098724721413)
              ·
                refine ⟨432130713152456010885265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2304697136813098724721413 432130713152456010885265)
                ·
                  refine ⟨324098034864342008163949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432130713152456010885265 324098034864342008163949)
                  ·
                    refine ⟨121536763074128253061481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 324098034864342008163949 121536763074128253061481)
                    ·
                      refine ⟨91152572305596189796111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121536763074128253061481 91152572305596189796111)
                      ·
                        rfl

theorem cell23_177519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3, 2].length) (baseStart_177519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177519 prefixEnd_177519 := by exact prefixLift 177519
  have htrace : WordTrace (prefixWord ++ tailWord_177519) baseStart_177519 baseEnd_177519 := by
    simpa [prefixWord, tailWord_177519, baseEnd_177519] using wordTrace_append hprefix tailTrace_177519
  have hstable : (prefixWord ++ tailWord_177519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177519).length < 2 ^ (prefixWord ++ tailWord_177519).sum := by decide
  have hdescent : baseEnd_177519 < baseStart_177519 := by decide
  rcases family_descends (prefixWord ++ tailWord_177519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177532 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_177532 : Nat := 118140960795 + 177532 * 2 ^ 59
def prefixEnd_177532 : Nat := 4983230072969 + 3 ^ 40 * 177532 * 2
def baseEnd_177532 : Nat := 91159247554104638933551

theorem tailTrace_177532 : CollatzResearch.WordTrace tailWord_177532 prefixEnd_177532 91159247554104638933551 := by
  unfold tailWord_177532
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237561996419679448403425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4316749328559572597871233 3237561996419679448403425)
  ·
    refine ⟨2428171497314759586302569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3237561996419679448403425 2428171497314759586302569)
    ·
      refine ⟨1821128622986069689726927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2428171497314759586302569 1821128622986069689726927)
      ·
        refine ⟨2731692934479104534590391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1821128622986069689726927 2731692934479104534590391)
        ·
          refine ⟨4097539401718656801885587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2731692934479104534590391 4097539401718656801885587)
          ·
            refine ⟨6146309102577985202828381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4097539401718656801885587 6146309102577985202828381)
            ·
              refine ⟨2304865913466744451060643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6146309102577985202828381 2304865913466744451060643)
              ·
                refine ⟨3457298870200116676590965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2304865913466744451060643 3457298870200116676590965)
                ·
                  refine ⟨324121769081260938430403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3457298870200116676590965 324121769081260938430403)
                  ·
                    refine ⟨486182653621891407645605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 324121769081260938430403 486182653621891407645605)
                    ·
                      refine ⟨91159247554104638933551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 486182653621891407645605 91159247554104638933551)
                      ·
                        rfl

theorem cell23_177532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_177532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177532 prefixEnd_177532 := by exact prefixLift 177532
  have htrace : WordTrace (prefixWord ++ tailWord_177532) baseStart_177532 baseEnd_177532 := by
    simpa [prefixWord, tailWord_177532, baseEnd_177532] using wordTrace_append hprefix tailTrace_177532
  have hstable : (prefixWord ++ tailWord_177532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177532).length < 2 ^ (prefixWord ++ tailWord_177532).sum := by decide
  have hdescent : baseEnd_177532 < baseStart_177532 := by decide
  rcases family_descends (prefixWord ++ tailWord_177532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177560 : List Nat := [2, 1, 2, 5, 2, 1, 2, 3, 1, 1, 3]
def baseStart_177560 : Nat := 118140960795 + 177560 * 2 ^ 59
def prefixEnd_177560 : Nat := 4983230072969 + 3 ^ 40 * 177560 * 2
def baseEnd_177560 : Nat := 91173625012430529383423

theorem tailTrace_177560 : CollatzResearch.WordTrace tailWord_177560 prefixEnd_177560 91173625012430529383423 := by
  unfold tailWord_177560
  simp only [CollatzResearch.WordTrace]
  refine ⟨3238072618368959839413067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4317430157825279785884089 3238072618368959839413067)
  ·
    refine ⟨4857108927553439759119601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3238072618368959839413067 4857108927553439759119601)
    ·
      refine ⟨3642831695665079819339701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4857108927553439759119601 3642831695665079819339701)
      ·
        refine ⟨341515471468601233063097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3642831695665079819339701 341515471468601233063097)
        ·
          refine ⟨256136603601450924797323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341515471468601233063097 256136603601450924797323)
          ·
            refine ⟨384204905402176387195985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256136603601450924797323 384204905402176387195985)
            ·
              refine ⟨288153679051632290396989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 384204905402176387195985 288153679051632290396989)
              ·
                refine ⟨108057629644362108898871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288153679051632290396989 108057629644362108898871)
                ·
                  refine ⟨162086444466543163348307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108057629644362108898871 162086444466543163348307)
                  ·
                    refine ⟨243129666699814745022461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162086444466543163348307 243129666699814745022461)
                    ·
                      refine ⟨91173625012430529383423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243129666699814745022461 91173625012430529383423)
                      ·
                        rfl

theorem cell23_177560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_177560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177560 prefixEnd_177560 := by exact prefixLift 177560
  have htrace : WordTrace (prefixWord ++ tailWord_177560) baseStart_177560 baseEnd_177560 := by
    simpa [prefixWord, tailWord_177560, baseEnd_177560] using wordTrace_append hprefix tailTrace_177560
  have hstable : (prefixWord ++ tailWord_177560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177560).length < 2 ^ (prefixWord ++ tailWord_177560).sum := by decide
  have hdescent : baseEnd_177560 < baseStart_177560 := by decide
  rcases family_descends (prefixWord ++ tailWord_177560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177593 : List Nat := [1, 2, 1, 4, 4, 1, 3, 1, 2, 4]
def baseStart_177593 : Nat := 118140960795 + 177593 * 2 ^ 59
def prefixEnd_177593 : Nat := 4983230072969 + 3 ^ 40 * 177593 * 2
def baseEnd_177593 : Nat := 30396856624676300090257

theorem tailTrace_177593 : CollatzResearch.WordTrace tailWord_177593 prefixEnd_177593 30396856624676300090257 := by
  unfold tailWord_177593
  simp only [CollatzResearch.WordTrace]
  refine ⟨6477348845618366314777433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4318232563745577543184955 6477348845618366314777433)
  ·
    refine ⟨4858011634213774736083075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6477348845618366314777433 4858011634213774736083075)
    ·
      refine ⟨7287017451320662104124613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4858011634213774736083075 7287017451320662104124613)
      ·
        refine ⟨1366315772122624144523365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7287017451320662104124613 1366315772122624144523365)
        ·
          refine ⟨256184207272992027098131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1366315772122624144523365 256184207272992027098131)
          ·
            refine ⟨384276310909488040647197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256184207272992027098131 384276310909488040647197)
            ·
              refine ⟨144103616591058015242699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 384276310909488040647197 144103616591058015242699)
              ·
                refine ⟨216155424886587022864049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144103616591058015242699 216155424886587022864049)
                ·
                  refine ⟨162116568664940267148037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216155424886587022864049 162116568664940267148037)
                  ·
                    refine ⟨30396856624676300090257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162116568664940267148037 30396856624676300090257)
                    ·
                      rfl

theorem cell23_177593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 2, 4].length) (baseStart_177593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177593 prefixEnd_177593 := by exact prefixLift 177593
  have htrace : WordTrace (prefixWord ++ tailWord_177593) baseStart_177593 baseEnd_177593 := by
    simpa [prefixWord, tailWord_177593, baseEnd_177593] using wordTrace_append hprefix tailTrace_177593
  have hstable : (prefixWord ++ tailWord_177593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177593).length < 2 ^ (prefixWord ++ tailWord_177593).sum := by decide
  have hdescent : baseEnd_177593 < baseStart_177593 := by decide
  rcases family_descends (prefixWord ++ tailWord_177593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177632 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 2, 6]
def baseStart_177632 : Nat := 118140960795 + 177632 * 2 ^ 59
def prefixEnd_177632 : Nat := 4983230072969 + 3 ^ 40 * 177632 * 2
def baseEnd_177632 : Nat := 30403531873184749227697

theorem tailTrace_177632 : CollatzResearch.WordTrace tailWord_177632 prefixEnd_177632 30403531873184749227697 := by
  unfold tailWord_177632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3239385646238537987723575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4319180861651383983631433 3239385646238537987723575)
  ·
    refine ⟨4859078469357806981585363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3239385646238537987723575 4859078469357806981585363)
    ·
      refine ⟨7288617704036710472378045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4859078469357806981585363 7288617704036710472378045)
      ·
        refine ⟨2733231639013766427141767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7288617704036710472378045 2733231639013766427141767)
        ·
          refine ⟨4099847458520649640712651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2733231639013766427141767 4099847458520649640712651)
          ·
            refine ⟨6149771187780974461068977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099847458520649640712651 6149771187780974461068977)
            ·
              refine ⟨4612328390835730845801733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149771187780974461068977 4612328390835730845801733)
              ·
                refine ⟨864811573281699533587825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4612328390835730845801733 864811573281699533587825)
                ·
                  refine ⟨648608679961274650190869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 864811573281699533587825 648608679961274650190869)
                  ·
                    refine ⟨30403531873184749227697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 648608679961274650190869 30403531873184749227697)
                    ·
                      rfl

theorem cell23_177632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_177632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177632 prefixEnd_177632 := by exact prefixLift 177632
  have htrace : WordTrace (prefixWord ++ tailWord_177632) baseStart_177632 baseEnd_177632 := by
    simpa [prefixWord, tailWord_177632, baseEnd_177632] using wordTrace_append hprefix tailTrace_177632
  have hstable : (prefixWord ++ tailWord_177632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177632).length < 2 ^ (prefixWord ++ tailWord_177632).sum := by decide
  have hdescent : baseEnd_177632 < baseStart_177632 := by decide
  rcases family_descends (prefixWord ++ tailWord_177632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177650 : List Nat := [3, 2, 1, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_177650 : Nat := 118140960795 + 177650 * 2 ^ 59
def prefixEnd_177650 : Nat := 4983230072969 + 3 ^ 40 * 177650 * 2
def baseEnd_177650 : Nat := 91219838271335177258009

theorem tailTrace_177650 : CollatzResearch.WordTrace tailWord_177650 prefixEnd_177650 91219838271335177258009 := by
  unfold tailWord_177650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619856951602966262400601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4319618537607910033068269 1619856951602966262400601)
  ·
    refine ⟨1214892713702224696800451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1619856951602966262400601 1214892713702224696800451)
    ·
      refine ⟨1822339070553337045200677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1214892713702224696800451 1822339070553337045200677)
      ·
        refine ⟨341688575728750695975127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1822339070553337045200677 341688575728750695975127)
        ·
          refine ⟨512532863593126043962691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341688575728750695975127 512532863593126043962691)
          ·
            refine ⟨768799295389689065944037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512532863593126043962691 768799295389689065944037)
            ·
              refine ⟨144149867885566699864507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 768799295389689065944037 144149867885566699864507)
              ·
                refine ⟨216224801828350049796761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144149867885566699864507 216224801828350049796761)
                ·
                  refine ⟨162168601371262537347571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216224801828350049796761 162168601371262537347571)
                  ·
                    refine ⟨243252902056893806021357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162168601371262537347571 243252902056893806021357)
                    ·
                      refine ⟨91219838271335177258009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243252902056893806021357 91219838271335177258009)
                      ·
                        rfl

theorem cell23_177650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_177650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177650 prefixEnd_177650 := by exact prefixLift 177650
  have htrace : WordTrace (prefixWord ++ tailWord_177650) baseStart_177650 baseEnd_177650 := by
    simpa [prefixWord, tailWord_177650, baseEnd_177650] using wordTrace_append hprefix tailTrace_177650
  have hstable : (prefixWord ++ tailWord_177650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177650).length < 2 ^ (prefixWord ++ tailWord_177650).sum := by decide
  have hdescent : baseEnd_177650 < baseStart_177650 := by decide
  rcases family_descends (prefixWord ++ tailWord_177650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177706 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_177706 : Nat := 118140960795 + 177706 * 2 ^ 59
def prefixEnd_177706 : Nat := 4983230072969 + 3 ^ 40 * 177706 * 2
def baseEnd_177706 : Nat := 91248593187986958157751

theorem tailTrace_177706 : CollatzResearch.WordTrace tailWord_177706 prefixEnd_177706 91248593187986958157751 := by
  unfold tailWord_177706
  simp only [CollatzResearch.WordTrace]
  refine ⟨1620367573552246653410243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4320980196139324409093981 1620367573552246653410243)
  ·
    refine ⟨2430551360328369980115365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1620367573552246653410243 2430551360328369980115365)
    ·
      refine ⟨455728380061569371271631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2430551360328369980115365 455728380061569371271631)
      ·
        refine ⟨683592570092354056907447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 455728380061569371271631 683592570092354056907447)
        ·
          refine ⟨1025388855138531085361171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 683592570092354056907447 1025388855138531085361171)
          ·
            refine ⟨1538083282707796628041757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1025388855138531085361171 1538083282707796628041757)
            ·
              refine ⟨576781231015423735515659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1538083282707796628041757 576781231015423735515659)
              ·
                refine ⟨865171846523135603273489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 576781231015423735515659 865171846523135603273489)
                ·
                  refine ⟨648878884892351702455117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 865171846523135603273489 648878884892351702455117)
                  ·
                    refine ⟨243329581834631888420669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 648878884892351702455117 243329581834631888420669)
                    ·
                      refine ⟨91248593187986958157751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243329581834631888420669 91248593187986958157751)
                      ·
                        rfl

theorem cell23_177706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_177706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177706 prefixEnd_177706 := by exact prefixLift 177706
  have htrace : WordTrace (prefixWord ++ tailWord_177706) baseStart_177706 baseEnd_177706 := by
    simpa [prefixWord, tailWord_177706, baseEnd_177706] using wordTrace_append hprefix tailTrace_177706
  have hstable : (prefixWord ++ tailWord_177706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177706).length < 2 ^ (prefixWord ++ tailWord_177706).sum := by decide
  have hdescent : baseEnd_177706 < baseStart_177706 := by decide
  rcases family_descends (prefixWord ++ tailWord_177706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177739 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 7, 4]
def baseStart_177739 : Nat := 118140960795 + 177739 * 2 ^ 59
def prefixEnd_177739 : Nat := 4983230072969 + 3 ^ 40 * 177739 * 2
def baseEnd_177739 : Nat := 30421846016528443015033

theorem tailTrace_177739 : CollatzResearch.WordTrace tailWord_177739 prefixEnd_177739 30421846016528443015033 := by
  unfold tailWord_177739
  simp only [CollatzResearch.WordTrace]
  refine ⟨6482673903089433249592271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4321782602059622166394847 6482673903089433249592271)
  ·
    refine ⟨9724010854634149874388407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6482673903089433249592271 9724010854634149874388407)
    ·
      refine ⟨14586016281951224811582611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9724010854634149874388407 14586016281951224811582611)
      ·
        refine ⟨21879024422926837217373917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14586016281951224811582611 21879024422926837217373917)
        ·
          refine ⟨8204634158597563956515219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21879024422926837217373917 8204634158597563956515219)
          ·
            refine ⟨12306951237896345934772829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8204634158597563956515219 12306951237896345934772829)
            ·
              refine ⟨4615106714211129725539811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12306951237896345934772829 4615106714211129725539811)
              ·
                refine ⟨6922660071316694588309717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615106714211129725539811 6922660071316694588309717)
                ·
                  refine ⟨162249845421485029413509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6922660071316694588309717 162249845421485029413509)
                  ·
                    refine ⟨30421846016528443015033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162249845421485029413509 30421846016528443015033)
                    ·
                      rfl

theorem cell23_177739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 4].length) (baseStart_177739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177739 prefixEnd_177739 := by exact prefixLift 177739
  have htrace : WordTrace (prefixWord ++ tailWord_177739) baseStart_177739 baseEnd_177739 := by
    simpa [prefixWord, tailWord_177739, baseEnd_177739] using wordTrace_append hprefix tailTrace_177739
  have hstable : (prefixWord ++ tailWord_177739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177739).length < 2 ^ (prefixWord ++ tailWord_177739).sum := by decide
  have hdescent : baseEnd_177739 < baseStart_177739 := by decide
  rcases family_descends (prefixWord ++ tailWord_177739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177769 : List Nat := [1, 2, 1, 1, 1, 4, 2, 5, 6]
def baseStart_177769 : Nat := 118140960795 + 177769 * 2 ^ 59
def prefixEnd_177769 : Nat := 4983230072969 + 3 ^ 40 * 177769 * 2
def baseEnd_177769 : Nat := 10142326941024467963329

theorem tailTrace_177769 : CollatzResearch.WordTrace tailWord_177769 prefixEnd_177769 10142326941024467963329 := by
  unfold tailWord_177769
  simp only [CollatzResearch.WordTrace]
  refine ⟨6483768092980748373184361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4322512061987165582122907 6483768092980748373184361)
  ·
    refine ⟨4862826069735561279888271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6483768092980748373184361 4862826069735561279888271)
    ·
      refine ⟨7294239104603341919832407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862826069735561279888271 7294239104603341919832407)
      ·
        refine ⟨10941358656905012879748611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7294239104603341919832407 10941358656905012879748611)
        ·
          refine ⟨16412037985357519319622917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941358656905012879748611 16412037985357519319622917)
          ·
            refine ⟨3077257122254534872429297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16412037985357519319622917 3077257122254534872429297)
            ·
              refine ⟨2307942841690901154321973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3077257122254534872429297 2307942841690901154321973)
              ·
                refine ⟨216369641408521983217685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2307942841690901154321973 216369641408521983217685)
                ·
                  refine ⟨10142326941024467963329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216369641408521983217685 10142326941024467963329)
                  ·
                    rfl

theorem cell23_177769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 5, 6].length) (baseStart_177769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177769 prefixEnd_177769 := by exact prefixLift 177769
  have htrace : WordTrace (prefixWord ++ tailWord_177769) baseStart_177769 baseEnd_177769 := by
    simpa [prefixWord, tailWord_177769, baseEnd_177769] using wordTrace_append hprefix tailTrace_177769
  have hstable : (prefixWord ++ tailWord_177769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177769).length < 2 ^ (prefixWord ++ tailWord_177769).sum := by decide
  have hdescent : baseEnd_177769 < baseStart_177769 := by decide
  rcases family_descends (prefixWord ++ tailWord_177769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177800 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_177800 : Nat := 118140960795 + 177800 * 2 ^ 59
def prefixEnd_177800 : Nat := 4983230072969 + 3 ^ 40 * 177800 * 2
def baseEnd_177800 : Nat := 91296860369509590382319

theorem tailTrace_177800 : CollatzResearch.WordTrace tailWord_177800 prefixEnd_177800 91296860369509590382319 := by
  unfold tailWord_177800
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242449377934220333781427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4323265837245627111708569 3242449377934220333781427)
  ·
    refine ⟨4863674066901330500672141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3242449377934220333781427 4863674066901330500672141)
    ·
      refine ⟨1823877775087998937752053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4863674066901330500672141 1823877775087998937752053)
      ·
        refine ⟨170988541414499900414255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1823877775087998937752053 170988541414499900414255)
        ·
          refine ⟨256482812121749850621383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170988541414499900414255 256482812121749850621383)
          ·
            refine ⟨384724218182624775932075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256482812121749850621383 384724218182624775932075)
            ·
              refine ⟨577086327273937163898113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 384724218182624775932075 577086327273937163898113)
              ·
                refine ⟨432814745455452872923585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577086327273937163898113 432814745455452872923585)
                ·
                  refine ⟨324611059091589654692689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 432814745455452872923585 324611059091589654692689)
                  ·
                    refine ⟨243458294318692241019517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 324611059091589654692689 243458294318692241019517)
                    ·
                      refine ⟨91296860369509590382319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243458294318692241019517 91296860369509590382319)
                      ·
                        rfl

theorem cell23_177800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_177800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177800 prefixEnd_177800 := by exact prefixLift 177800
  have htrace : WordTrace (prefixWord ++ tailWord_177800) baseStart_177800 baseEnd_177800 := by
    simpa [prefixWord, tailWord_177800, baseEnd_177800] using wordTrace_append hprefix tailTrace_177800
  have hstable : (prefixWord ++ tailWord_177800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177800).length < 2 ^ (prefixWord ++ tailWord_177800).sum := by decide
  have hdescent : baseEnd_177800 < baseStart_177800 := by decide
  rcases family_descends (prefixWord ++ tailWord_177800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177820 : List Nat := [2, 2, 3, 2, 3, 2, 2, 1, 6]
def baseStart_177820 : Nat := 118140960795 + 177820 * 2 ^ 59
def prefixEnd_177820 : Nat := 4983230072969 + 3 ^ 40 * 177820 * 2
def baseEnd_177820 : Nat := 10145236664733279125803

theorem tailTrace_177820 : CollatzResearch.WordTrace tailWord_177820 prefixEnd_177820 10145236664733279125803 := by
  unfold tailWord_177820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3242814107897992041645457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4323752143863989388860609 3242814107897992041645457)
  ·
    refine ⟨2432110580923494031234093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3242814107897992041645457 2432110580923494031234093)
    ·
      refine ⟨912041467846310261712785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2432110580923494031234093 912041467846310261712785)
      ·
        refine ⟨684031100884732696284589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 912041467846310261712785 684031100884732696284589)
        ·
          refine ⟨256511662831774761106721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 684031100884732696284589 256511662831774761106721)
          ·
            refine ⟨192383747123831070830041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256511662831774761106721 192383747123831070830041)
            ·
              refine ⟨144287810342873303122531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192383747123831070830041 144287810342873303122531)
              ·
                refine ⟨216431715514309954683797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144287810342873303122531 216431715514309954683797)
                ·
                  refine ⟨10145236664733279125803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 216431715514309954683797 10145236664733279125803)
                  ·
                    rfl

theorem cell23_177820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_177820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177820 prefixEnd_177820 := by exact prefixLift 177820
  have htrace : WordTrace (prefixWord ++ tailWord_177820) baseStart_177820 baseEnd_177820 := by
    simpa [prefixWord, tailWord_177820, baseEnd_177820] using wordTrace_append hprefix tailTrace_177820
  have hstable : (prefixWord ++ tailWord_177820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177820).length < 2 ^ (prefixWord ++ tailWord_177820).sum := by decide
  have hdescent : baseEnd_177820 < baseStart_177820 := by decide
  rcases family_descends (prefixWord ++ tailWord_177820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177858 : List Nat := [3, 5, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_177858 : Nat := 118140960795 + 177858 * 2 ^ 59
def prefixEnd_177858 : Nat := 4983230072969 + 3 ^ 40 * 177858 * 2
def baseEnd_177858 : Nat := 30442214082490121152351

theorem tailTrace_177858 : CollatzResearch.WordTrace tailWord_177858 prefixEnd_177858 30442214082490121152351 := by
  unfold tailWord_177858
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621753547414579143293557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4324676126438877715449485 1621753547414579143293557)
  ·
    refine ⟨152039395070116794683771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1621753547414579143293557 152039395070116794683771)
    ·
      refine ⟨228059092605175192025657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152039395070116794683771 228059092605175192025657)
      ·
        refine ⟨171044319453881394019243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228059092605175192025657 171044319453881394019243)
        ·
          refine ⟨256566479180822091028865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171044319453881394019243 256566479180822091028865)
          ·
            refine ⟨192424859385616568271649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256566479180822091028865 192424859385616568271649)
            ·
              refine ⟨144318644539212426203737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192424859385616568271649 144318644539212426203737)
              ·
                refine ⟨108238983404409319652803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144318644539212426203737 108238983404409319652803)
                ·
                  refine ⟨162358475106613979479205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108238983404409319652803 162358475106613979479205)
                  ·
                    refine ⟨30442214082490121152351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162358475106613979479205 30442214082490121152351)
                    ·
                      rfl

theorem cell23_177858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_177858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177858 prefixEnd_177858 := by exact prefixLift 177858
  have htrace : WordTrace (prefixWord ++ tailWord_177858) baseStart_177858 baseEnd_177858 := by
    simpa [prefixWord, tailWord_177858, baseEnd_177858] using wordTrace_append hprefix tailTrace_177858
  have hstable : (prefixWord ++ tailWord_177858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177858).length < 2 ^ (prefixWord ++ tailWord_177858).sum := by decide
  have hdescent : baseEnd_177858 < baseStart_177858 := by decide
  rcases family_descends (prefixWord ++ tailWord_177858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177863 : List Nat := [1, 1, 4, 1, 1, 1, 6, 2, 2, 4]
def baseStart_177863 : Nat := 118140960795 + 177863 * 2 ^ 59
def prefixEnd_177863 : Nat := 4983230072969 + 3 ^ 40 * 177863 * 2
def baseEnd_177863 : Nat := 30443069883580947964843

theorem tailTrace_177863 : CollatzResearch.WordTrace tailWord_177863 prefixEnd_177863 30443069883580947964843 := by
  unfold tailWord_177863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6487196554640202427106243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4324797703093468284737495 6487196554640202427106243)
  ·
    refine ⟨9730794831960303640659365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6487196554640202427106243 9730794831960303640659365)
    ·
      refine ⟨1824524030992556932623631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9730794831960303640659365 1824524030992556932623631)
      ·
        refine ⟨2736786046488835398935447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824524030992556932623631 2736786046488835398935447)
        ·
          refine ⟨4105179069733253098403171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2736786046488835398935447 4105179069733253098403171)
          ·
            refine ⟨6157768604599879647604757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4105179069733253098403171 6157768604599879647604757)
            ·
              refine ⟨288645403340619358481473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6157768604599879647604757 288645403340619358481473)
              ·
                refine ⟨216484052505464518861105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288645403340619358481473 216484052505464518861105)
                ·
                  refine ⟨162363039379098389145829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216484052505464518861105 162363039379098389145829)
                  ·
                    refine ⟨30443069883580947964843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162363039379098389145829 30443069883580947964843)
                    ·
                      rfl

theorem cell23_177863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_177863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177863 prefixEnd_177863 := by exact prefixLift 177863
  have htrace : WordTrace (prefixWord ++ tailWord_177863) baseStart_177863 baseEnd_177863 := by
    simpa [prefixWord, tailWord_177863, baseEnd_177863] using wordTrace_append hprefix tailTrace_177863
  have hstable : (prefixWord ++ tailWord_177863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177863).length < 2 ^ (prefixWord ++ tailWord_177863).sum := by decide
  have hdescent : baseEnd_177863 < baseStart_177863 := by decide
  rcases family_descends (prefixWord ++ tailWord_177863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177870 : List Nat := [4, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_177870 : Nat := 118140960795 + 177870 * 2 ^ 59
def prefixEnd_177870 : Nat := 4983230072969 + 3 ^ 40 * 177870 * 2
def baseEnd_177870 : Nat := 91332804015324316506997

theorem tailTrace_177870 : CollatzResearch.WordTrace tailWord_177870 prefixEnd_177870 91332804015324316506997 := by
  unfold tailWord_177870
  simp only [CollatzResearch.WordTrace]
  refine ⟨810931483201855327826383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4324967910409895081740709 810931483201855327826383)
  ·
    refine ⟨1216397224802782991739575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 810931483201855327826383 1216397224802782991739575)
    ·
      refine ⟨1824595837204174487609363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1216397224802782991739575 1824595837204174487609363)
      ·
        refine ⟨2736893755806261731414045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1824595837204174487609363 2736893755806261731414045)
        ·
          refine ⟨1026335158427348149280267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2736893755806261731414045 1026335158427348149280267)
          ·
            refine ⟨1539502737641022223920401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026335158427348149280267 1539502737641022223920401)
            ·
              refine ⟨1154627053230766667940301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539502737641022223920401 1154627053230766667940301)
              ·
                refine ⟨432985144961537500477613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1154627053230766667940301 432985144961537500477613)
                ·
                  refine ⟨162369429360576562679105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 432985144961537500477613 162369429360576562679105)
                  ·
                    refine ⟨121777072020432422009329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 162369429360576562679105 121777072020432422009329)
                    ·
                      refine ⟨91332804015324316506997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 121777072020432422009329 91332804015324316506997)
                      ·
                        rfl

theorem cell23_177870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_177870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177870 prefixEnd_177870 := by exact prefixLift 177870
  have htrace : WordTrace (prefixWord ++ tailWord_177870) baseStart_177870 baseEnd_177870 := by
    simpa [prefixWord, tailWord_177870, baseEnd_177870] using wordTrace_append hprefix tailTrace_177870
  have hstable : (prefixWord ++ tailWord_177870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177870).length < 2 ^ (prefixWord ++ tailWord_177870).sum := by decide
  have hdescent : baseEnd_177870 < baseStart_177870 := by decide
  rcases family_descends (prefixWord ++ tailWord_177870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_177903 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 3]
def baseStart_177903 : Nat := 118140960795 + 177903 * 2 ^ 59
def prefixEnd_177903 : Nat := 4983230072969 + 3 ^ 40 * 177903 * 2
def baseEnd_177903 : Nat := 91349748876922687394345

theorem tailTrace_177903 : CollatzResearch.WordTrace tailWord_177903 prefixEnd_177903 91349748876922687394345 := by
  unfold tailWord_177903
  simp only [CollatzResearch.WordTrace]
  refine ⟨6488655474495289258562363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4325770316330192839041575 6488655474495289258562363)
  ·
    refine ⟨9732983211742933887843545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6488655474495289258562363 9732983211742933887843545)
    ·
      refine ⟨7299737408807200415882659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9732983211742933887843545 7299737408807200415882659)
      ·
        refine ⟨10949606113210800623823989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7299737408807200415882659 10949606113210800623823989)
        ·
          refine ⟨1026525573113512558483499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10949606113210800623823989 1026525573113512558483499)
          ·
            refine ⟨1539788359670268837725249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1026525573113512558483499 1539788359670268837725249)
            ·
              refine ⟨1154841269752701628293937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1539788359670268837725249 1154841269752701628293937)
              ·
                refine ⟨866130952314526221220453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154841269752701628293937 866130952314526221220453)
                ·
                  refine ⟨162399553558973666478835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 866130952314526221220453 162399553558973666478835)
                  ·
                    refine ⟨243599330338460499718253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162399553558973666478835 243599330338460499718253)
                    ·
                      refine ⟨91349748876922687394345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243599330338460499718253 91349748876922687394345)
                      ·
                        rfl

theorem cell23_177903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 1, 3].length) (baseStart_177903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_177903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_177903 prefixEnd_177903 := by exact prefixLift 177903
  have htrace : WordTrace (prefixWord ++ tailWord_177903) baseStart_177903 baseEnd_177903 := by
    simpa [prefixWord, tailWord_177903, baseEnd_177903] using wordTrace_append hprefix tailTrace_177903
  have hstable : (prefixWord ++ tailWord_177903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_177903).length < 2 ^ (prefixWord ++ tailWord_177903).sum := by decide
  have hdescent : baseEnd_177903 < baseStart_177903 := by decide
  rcases family_descends (prefixWord ++ tailWord_177903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178030 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 2, 5]
def baseStart_178030 : Nat := 118140960795 + 178030 * 2 ^ 59
def prefixEnd_178030 : Nat := 4983230072969 + 3 ^ 40 * 178030 * 2
def baseEnd_178030 : Nat := 30471653640014563502087

theorem tailTrace_178030 : CollatzResearch.WordTrace tailWord_178030 prefixEnd_178030 30471653640014563502087 := by
  unfold tailWord_178030
  simp only [CollatzResearch.WordTrace]
  refine ⟨811660943129398743554443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4328858363356793298957029 811660943129398743554443)
  ·
    refine ⟨1217491414694098115331665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 811660943129398743554443 1217491414694098115331665)
    ·
      refine ⟨913118561020573586498749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1217491414694098115331665 913118561020573586498749)
      ·
        refine ⟨342419460382715094937031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 913118561020573586498749 342419460382715094937031)
        ·
          refine ⟨513629190574072642405547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 342419460382715094937031 513629190574072642405547)
          ·
            refine ⟨770443785861108963608321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513629190574072642405547 770443785861108963608321)
            ·
              refine ⟨577832839395831722706241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 770443785861108963608321 577832839395831722706241)
              ·
                refine ⟨433374629546873792029681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 577832839395831722706241 433374629546873792029681)
                ·
                  refine ⟨325030972160155344022261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433374629546873792029681 325030972160155344022261)
                  ·
                    refine ⟨30471653640014563502087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 325030972160155344022261 30471653640014563502087)
                    ·
                      rfl

theorem cell23_178030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_178030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178030 prefixEnd_178030 := by exact prefixLift 178030
  have htrace : WordTrace (prefixWord ++ tailWord_178030) baseStart_178030 baseEnd_178030 := by
    simpa [prefixWord, tailWord_178030, baseEnd_178030] using wordTrace_append hprefix tailTrace_178030
  have hstable : (prefixWord ++ tailWord_178030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178030).length < 2 ^ (prefixWord ++ tailWord_178030).sum := by decide
  have hdescent : baseEnd_178030 < baseStart_178030 := by decide
  rcases family_descends (prefixWord ++ tailWord_178030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178033 : List Nat := [1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 4]
def baseStart_178033 : Nat := 118140960795 + 178033 * 2 ^ 59
def prefixEnd_178033 : Nat := 4983230072969 + 3 ^ 40 * 178033 * 2
def baseEnd_178033 : Nat := 91416501362007178768747

theorem tailTrace_178033 : CollatzResearch.WordTrace tailWord_178033 prefixEnd_178033 91416501362007178768747 := by
  unfold tailWord_178033
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493396964024321460794753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4328931309349547640529835 6493396964024321460794753)
  ·
    refine ⟨4870047723018241095596065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6493396964024321460794753 4870047723018241095596065)
    ·
      refine ⟨3652535792263680821697049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4870047723018241095596065 3652535792263680821697049)
      ·
        refine ⟨2739401844197760616272787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3652535792263680821697049 2739401844197760616272787)
        ·
          refine ⟨4109102766296640924409181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2739401844197760616272787 4109102766296640924409181)
          ·
            refine ⟨1540913537361240346653443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4109102766296640924409181 1540913537361240346653443)
            ·
              refine ⟨2311370306041860519980165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1540913537361240346653443 2311370306041860519980165)
              ·
                refine ⟨433381932382848847496281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2311370306041860519980165 433381932382848847496281)
                ·
                  refine ⟨325036449287136635622211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 433381932382848847496281 325036449287136635622211)
                  ·
                    refine ⟨487554673930704953433317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 325036449287136635622211 487554673930704953433317)
                    ·
                      refine ⟨91416501362007178768747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 487554673930704953433317 91416501362007178768747)
                      ·
                        rfl

theorem cell23_178033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_178033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178033 prefixEnd_178033 := by exact prefixLift 178033
  have htrace : WordTrace (prefixWord ++ tailWord_178033) baseStart_178033 baseEnd_178033 := by
    simpa [prefixWord, tailWord_178033, baseEnd_178033] using wordTrace_append hprefix tailTrace_178033
  have hstable : (prefixWord ++ tailWord_178033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178033).length < 2 ^ (prefixWord ++ tailWord_178033).sum := by decide
  have hdescent : baseEnd_178033 < baseStart_178033 := by decide
  rcases family_descends (prefixWord ++ tailWord_178033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178043 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 3, 4]
def baseStart_178043 : Nat := 118140960795 + 178043 * 2 ^ 59
def prefixEnd_178043 : Nat := 4983230072969 + 3 ^ 40 * 178043 * 2
def baseEnd_178043 : Nat := 30473878722850713214567

theorem tailTrace_178043 : CollatzResearch.WordTrace tailWord_178043 prefixEnd_178043 30473878722850713214567 := by
  unfold tailWord_178043
  simp only [CollatzResearch.WordTrace]
  refine ⟨6493761693988093168658783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4329174462658728779105855 6493761693988093168658783)
  ·
    refine ⟨9740642540982139752988175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6493761693988093168658783 9740642540982139752988175)
    ·
      refine ⟨14610963811473209629482263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9740642540982139752988175 14610963811473209629482263)
      ·
        refine ⟨21916445717209814444223395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14610963811473209629482263 21916445717209814444223395)
        ·
          refine ⟨32874668575814721666335093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21916445717209814444223395 32874668575814721666335093)
          ·
            refine ⟨3082000178982630156218915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32874668575814721666335093 3082000178982630156218915)
            ·
              refine ⟨4623000268473945234328373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3082000178982630156218915 4623000268473945234328373)
              ·
                refine ⟨433406275169432365718285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4623000268473945234328373 433406275169432365718285)
                ·
                  refine ⟨162527353188537137144357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433406275169432365718285 162527353188537137144357)
                  ·
                    refine ⟨30473878722850713214567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162527353188537137144357 30473878722850713214567)
                    ·
                      rfl

theorem cell23_178043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 4].length) (baseStart_178043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178043 prefixEnd_178043 := by exact prefixLift 178043
  have htrace : WordTrace (prefixWord ++ tailWord_178043) baseStart_178043 baseEnd_178043 := by
    simpa [prefixWord, tailWord_178043, baseEnd_178043] using wordTrace_append hprefix tailTrace_178043
  have hstable : (prefixWord ++ tailWord_178043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178043).length < 2 ^ (prefixWord ++ tailWord_178043).sum := by decide
  have hdescent : baseEnd_178043 < baseStart_178043 := by decide
  rcases family_descends (prefixWord ++ tailWord_178043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178053 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 3]
def baseStart_178053 : Nat := 118140960795 + 178053 * 2 ^ 59
def prefixEnd_178053 : Nat := 4983230072969 + 3 ^ 40 * 178053 * 2
def baseEnd_178053 : Nat := 91426770975097100518655

theorem tailTrace_178053 : CollatzResearch.WordTrace tailWord_178053 prefixEnd_178053 91426770975097100518655 := by
  unfold tailWord_178053
  simp only [CollatzResearch.WordTrace]
  refine ⟨6494126423951864876522813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4329417615967909917681875 6494126423951864876522813)
  ·
    refine ⟨2435297408981949328696055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6494126423951864876522813 2435297408981949328696055)
    ·
      refine ⟨3652946113472923993044083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435297408981949328696055 3652946113472923993044083)
      ·
        refine ⟨5479419170209385989566125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3652946113472923993044083 5479419170209385989566125)
        ·
          refine ⟨2054782188828519746087297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5479419170209385989566125 2054782188828519746087297)
          ·
            refine ⟨1541086641621389809565473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2054782188828519746087297 1541086641621389809565473)
            ·
              refine ⟨1155814981216042357174105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1541086641621389809565473 1155814981216042357174105)
              ·
                refine ⟨866861235912031767880579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1155814981216042357174105 866861235912031767880579)
                ·
                  refine ⟨1300291853868047651820869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 866861235912031767880579 1300291853868047651820869)
                  ·
                    refine ⟨243804722600258934716413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1300291853868047651820869 243804722600258934716413)
                    ·
                      refine ⟨91426770975097100518655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243804722600258934716413 91426770975097100518655)
                      ·
                        rfl

theorem cell23_178053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_178053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178053 prefixEnd_178053 := by exact prefixLift 178053
  have htrace : WordTrace (prefixWord ++ tailWord_178053) baseStart_178053 baseEnd_178053 := by
    simpa [prefixWord, tailWord_178053, baseEnd_178053] using wordTrace_append hprefix tailTrace_178053
  have hstable : (prefixWord ++ tailWord_178053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178053).length < 2 ^ (prefixWord ++ tailWord_178053).sum := by decide
  have hdescent : baseEnd_178053 < baseStart_178053 := by decide
  rcases family_descends (prefixWord ++ tailWord_178053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178077 : List Nat := [1, 4, 2, 1, 2, 2, 1, 5, 1, 4]
def baseStart_178077 : Nat := 118140960795 + 178077 * 2 ^ 59
def prefixEnd_178077 : Nat := 4983230072969 + 3 ^ 40 * 178077 * 2
def baseEnd_178077 : Nat := 30479698170268335539515

theorem tailTrace_178077 : CollatzResearch.WordTrace tailWord_178077 prefixEnd_178077 30479698170268335539515 := by
  unfold tailWord_178077
  simp only [CollatzResearch.WordTrace]
  refine ⟨6495001775864916975396485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4330001183909944650264323 6495001775864916975396485)
  ·
    refine ⟨1217812832974671932886841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6495001775864916975396485 1217812832974671932886841)
    ·
      refine ⟨913359624731003949665131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1217812832974671932886841 913359624731003949665131)
      ·
        refine ⟨1370039437096505924497697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 913359624731003949665131 1370039437096505924497697)
        ·
          refine ⟨1027529577822379443373273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1370039437096505924497697 1027529577822379443373273)
          ·
            refine ⟨770647183366784582529955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1027529577822379443373273 770647183366784582529955)
            ·
              refine ⟨1155970775050176873794933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770647183366784582529955 1155970775050176873794933)
              ·
                refine ⟨108372260160954081918275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1155970775050176873794933 108372260160954081918275)
                ·
                  refine ⟨162558390241431122877413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108372260160954081918275 162558390241431122877413)
                  ·
                    refine ⟨30479698170268335539515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 162558390241431122877413 30479698170268335539515)
                    ·
                      rfl

theorem cell23_178077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_178077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178077 prefixEnd_178077 := by exact prefixLift 178077
  have htrace : WordTrace (prefixWord ++ tailWord_178077) baseStart_178077 baseEnd_178077 := by
    simpa [prefixWord, tailWord_178077, baseEnd_178077] using wordTrace_append hprefix tailTrace_178077
  have hstable : (prefixWord ++ tailWord_178077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178077).length < 2 ^ (prefixWord ++ tailWord_178077).sum := by decide
  have hdescent : baseEnd_178077 < baseStart_178077 := by decide
  rcases family_descends (prefixWord ++ tailWord_178077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178120 : List Nat := [2, 1, 3, 1, 4, 1, 1, 4, 1, 5]
def baseStart_178120 : Nat := 118140960795 + 178120 * 2 ^ 59
def prefixEnd_178120 : Nat := 4983230072969 + 3 ^ 40 * 178120 * 2
def baseEnd_178120 : Nat := 30487058059649446126949

theorem tailTrace_178120 : CollatzResearch.WordTrace tailWord_178120 prefixEnd_178120 30487058059649446126949 := by
  unfold tailWord_178120
  simp only [CollatzResearch.WordTrace]
  refine ⟨3248285057354567659605907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4331046743139423546141209 3248285057354567659605907)
  ·
    refine ⟨4872427586031851489408861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3248285057354567659605907 4872427586031851489408861)
    ·
      refine ⟨1827160344761944308528323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4872427586031851489408861 1827160344761944308528323)
      ·
        refine ⟨2740740517142916462792485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1827160344761944308528323 2740740517142916462792485)
        ·
          refine ⟨513888846964296836773591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2740740517142916462792485 513888846964296836773591)
          ·
            refine ⟨770833270446445255160387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513888846964296836773591 770833270446445255160387)
            ·
              refine ⟨1156249905669667882740581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 770833270446445255160387 1156249905669667882740581)
              ·
                refine ⟨216796857313062728013859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1156249905669667882740581 216796857313062728013859)
                ·
                  refine ⟨325195285969594092020789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 216796857313062728013859 325195285969594092020789)
                  ·
                    refine ⟨30487058059649446126949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 325195285969594092020789 30487058059649446126949)
                    ·
                      rfl

theorem cell23_178120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_178120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178120 prefixEnd_178120 := by exact prefixLift 178120
  have htrace : WordTrace (prefixWord ++ tailWord_178120) baseStart_178120 baseEnd_178120 := by
    simpa [prefixWord, tailWord_178120, baseEnd_178120] using wordTrace_append hprefix tailTrace_178120
  have hstable : (prefixWord ++ tailWord_178120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178120).length < 2 ^ (prefixWord ++ tailWord_178120).sum := by decide
  have hdescent : baseEnd_178120 < baseStart_178120 := by decide
  rcases family_descends (prefixWord ++ tailWord_178120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_178151 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 3, 1, 3]
def baseStart_178151 : Nat := 118140960795 + 178151 * 2 ^ 59
def prefixEnd_178151 : Nat := 4983230072969 + 3 ^ 40 * 178151 * 2
def baseEnd_178151 : Nat := 91477092079237717093205

theorem tailTrace_178151 : CollatzResearch.WordTrace tailWord_178151 prefixEnd_178151 91477092079237717093205 := by
  unfold tailWord_178151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6497700777596827613590307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4331800518397885075726871 6497700777596827613590307)
  ·
    refine ⟨9746551166395241420385461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6497700777596827613590307 9746551166395241420385461)
    ·
      refine ⟨913739171849553883161137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9746551166395241420385461 913739171849553883161137)
      ·
        refine ⟨685304378887165412370853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 913739171849553883161137 685304378887165412370853)
        ·
          refine ⟨128494571041343514819535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 685304378887165412370853 128494571041343514819535)
          ·
            refine ⟨192741856562015272229303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128494571041343514819535 192741856562015272229303)
            ·
              refine ⟨289112784843022908343955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192741856562015272229303 289112784843022908343955)
              ·
                refine ⟨433669177264534362515933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 289112784843022908343955 433669177264534362515933)
                ·
                  refine ⟨162625941474200385943475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433669177264534362515933 162625941474200385943475)
                  ·
                    refine ⟨243938912211300578915213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162625941474200385943475 243938912211300578915213)
                    ·
                      refine ⟨91477092079237717093205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 243938912211300578915213 91477092079237717093205)
                      ·
                        rfl

theorem cell23_178151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_178151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_178151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_178151 prefixEnd_178151 := by exact prefixLift 178151
  have htrace : WordTrace (prefixWord ++ tailWord_178151) baseStart_178151 baseEnd_178151 := by
    simpa [prefixWord, tailWord_178151, baseEnd_178151] using wordTrace_append hprefix tailTrace_178151
  have hstable : (prefixWord ++ tailWord_178151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_178151).length < 2 ^ (prefixWord ++ tailWord_178151).sum := by decide
  have hdescent : baseEnd_178151 < baseStart_178151 := by decide
  rcases family_descends (prefixWord ++ tailWord_178151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
