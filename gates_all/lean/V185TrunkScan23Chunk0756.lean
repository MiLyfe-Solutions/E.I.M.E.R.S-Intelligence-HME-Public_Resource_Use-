import V185TrunkScan23Chunk0755

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4470189 : List Nat := [1, 5, 2, 2, 1, 2, 2, 8]
def baseStart_4470189 : Nat := 118140960795 + 4470189 * 2 ^ 59
def prefixEnd_4470189 : Nat := 4983230072969 + 3 ^ 40 * 4470189 * 2
def baseEnd_4470189 : Nat := 85013169386715411062203

theorem tailTrace_4470189 : CollatzResearch.WordTrace tailWord_4470189 prefixEnd_4470189 85013169386715411062203 := by
  unfold tailWord_4470189
  simp only [CollatzResearch.WordTrace]
  refine ⟨163041187202276175345149621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108694124801517450230099747 163041187202276175345149621)
  ·
    refine ⟨15285111300213391438607777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163041187202276175345149621 15285111300213391438607777)
    ·
      refine ⟨11463833475160043578955833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15285111300213391438607777 11463833475160043578955833)
      ·
        refine ⟨8597875106370032684216875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11463833475160043578955833 8597875106370032684216875)
        ·
          refine ⟨12896812659555049026325313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8597875106370032684216875 12896812659555049026325313)
          ·
            refine ⟨9672609494666286769743985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12896812659555049026325313 9672609494666286769743985)
            ·
              refine ⟨7254457120999715077307989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9672609494666286769743985 7254457120999715077307989)
              ·
                refine ⟨85013169386715411062203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7254457120999715077307989 85013169386715411062203)
                ·
                  rfl

theorem cell23_4470189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 8].length) (baseStart_4470189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470189 prefixEnd_4470189 := by exact prefixLift 4470189
  have htrace : WordTrace (prefixWord ++ tailWord_4470189) baseStart_4470189 baseEnd_4470189 := by
    simpa [prefixWord, tailWord_4470189, baseEnd_4470189] using wordTrace_append hprefix tailTrace_4470189
  have hstable : (prefixWord ++ tailWord_4470189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470189).length < 2 ^ (prefixWord ++ tailWord_4470189).sum := by decide
  have hdescent : baseEnd_4470189 < baseStart_4470189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470210 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_4470210 : Nat := 118140960795 + 4470210 * 2 ^ 59
def prefixEnd_4470210 : Nat := 4983230072969 + 3 ^ 40 * 4470210 * 2
def baseEnd_4470210 : Nat := 765122118845020172172295

theorem tailTrace_4470210 : CollatzResearch.WordTrace tailWord_4470210 prefixEnd_4470210 765122118845020172172295 := by
  unfold tailWord_4470210
  simp only [CollatzResearch.WordTrace]
  refine ⟨40760488283800023982916021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108694635423466730621109389 40760488283800023982916021)
  ·
    refine ⟨3821295776606252248398377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40760488283800023982916021 3821295776606252248398377)
    ·
      refine ⟨2865971832454689186298783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3821295776606252248398377 2865971832454689186298783)
      ·
        refine ⟨4298957748682033779448175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2865971832454689186298783 4298957748682033779448175)
        ·
          refine ⟨6448436623023050669172263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4298957748682033779448175 6448436623023050669172263)
          ·
            refine ⟨9672654934534576003758395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6448436623023050669172263 9672654934534576003758395)
            ·
              refine ⟨14508982401801864005637593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9672654934534576003758395 14508982401801864005637593)
              ·
                refine ⟨10881736801351398004228195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14508982401801864005637593 10881736801351398004228195)
                ·
                  refine ⟨16322605202027097006342293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10881736801351398004228195 16322605202027097006342293)
                  ·
                    refine ⟨765122118845020172172295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16322605202027097006342293 765122118845020172172295)
                    ·
                      rfl

theorem cell23_4470210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_4470210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470210 prefixEnd_4470210 := by exact prefixLift 4470210
  have htrace : WordTrace (prefixWord ++ tailWord_4470210) baseStart_4470210 baseEnd_4470210 := by
    simpa [prefixWord, tailWord_4470210, baseEnd_4470210] using wordTrace_append hprefix tailTrace_4470210
  have hstable : (prefixWord ++ tailWord_4470210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470210).length < 2 ^ (prefixWord ++ tailWord_4470210).sum := by decide
  have hdescent : baseEnd_4470210 < baseStart_4470210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470239 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 3, 4, 2]
def baseStart_4470239 : Nat := 118140960795 + 4470239 * 2 ^ 59
def prefixEnd_4470239 : Nat := 4983230072969 + 3 ^ 40 * 4470239 * 2
def baseEnd_4470239 : Nat := 2295381247474040903054251

theorem tailTrace_4470239 : CollatzResearch.WordTrace tailWord_4470239 prefixEnd_4470239 2295381247474040903054251 := by
  unfold tailWord_4470239
  simp only [CollatzResearch.WordTrace]
  refine ⟨163043010852095033884469771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108695340568063355922979847 163043010852095033884469771)
  ·
    refine ⟨244564516278142550826704657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163043010852095033884469771 244564516278142550826704657)
    ·
      refine ⟨183423387208606913120028493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244564516278142550826704657 183423387208606913120028493)
      ·
        refine ⟨68783770203227592420010685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183423387208606913120028493 68783770203227592420010685)
        ·
          refine ⟨25793913826210347157504007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68783770203227592420010685 25793913826210347157504007)
          ·
            refine ⟨38690870739315520736256011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25793913826210347157504007 38690870739315520736256011)
            ·
              refine ⟨58036306108973281104384017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38690870739315520736256011 58036306108973281104384017)
              ·
                refine ⟨43527229581729960828288013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58036306108973281104384017 43527229581729960828288013)
                ·
                  refine ⟨16322711093148735310608005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43527229581729960828288013 16322711093148735310608005)
                  ·
                    refine ⟨3060508329965387870739001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16322711093148735310608005 3060508329965387870739001)
                    ·
                      refine ⟨2295381247474040903054251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060508329965387870739001 2295381247474040903054251)
                      ·
                        rfl

theorem cell23_4470239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_4470239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470239 prefixEnd_4470239 := by exact prefixLift 4470239
  have htrace : WordTrace (prefixWord ++ tailWord_4470239) baseStart_4470239 baseEnd_4470239 := by
    simpa [prefixWord, tailWord_4470239, baseEnd_4470239] using wordTrace_append hprefix tailTrace_4470239
  have hstable : (prefixWord ++ tailWord_4470239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470239).length < 2 ^ (prefixWord ++ tailWord_4470239).sum := by decide
  have hdescent : baseEnd_4470239 < baseStart_4470239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470256 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2]
def baseStart_4470256 : Nat := 118140960795 + 4470256 * 2 ^ 59
def prefixEnd_4470256 : Nat := 4983230072969 + 3 ^ 40 * 4470256 * 2
def baseEnd_4470256 : Nat := 2295389976645167336541673

theorem tailTrace_4470256 : CollatzResearch.WordTrace tailWord_4470256 prefixEnd_4470256 2295389976645167336541673 := by
  unfold tailWord_4470256
  simp only [CollatzResearch.WordTrace]
  refine ⟨81521815446516722893919311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108695753928688963858559081 81521815446516722893919311)
  ·
    refine ⟨122282723169775084340878967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81521815446516722893919311 122282723169775084340878967)
    ·
      refine ⟨183424084754662626511318451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122282723169775084340878967 183424084754662626511318451)
      ·
        refine ⟨275136127131993939766977677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183424084754662626511318451 275136127131993939766977677)
        ·
          refine ⟨103176047674497727412616629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275136127131993939766977677 103176047674497727412616629)
          ·
            refine ⟨9672754469484161944932809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103176047674497727412616629 9672754469484161944932809)
            ·
              refine ⟨7254565852113121458699607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9672754469484161944932809 7254565852113121458699607)
              ·
                refine ⟨10881848778169682188049411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7254565852113121458699607 10881848778169682188049411)
                ·
                  refine ⟨16322773167254523282074117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10881848778169682188049411 16322773167254523282074117)
                  ·
                    refine ⟨3060519968860223115388897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16322773167254523282074117 3060519968860223115388897)
                    ·
                      refine ⟨2295389976645167336541673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060519968860223115388897 2295389976645167336541673)
                      ·
                        rfl

theorem cell23_4470256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 4, 2].length) (baseStart_4470256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470256 prefixEnd_4470256 := by exact prefixLift 4470256
  have htrace : WordTrace (prefixWord ++ tailWord_4470256) baseStart_4470256 baseEnd_4470256 := by
    simpa [prefixWord, tailWord_4470256, baseEnd_4470256] using wordTrace_append hprefix tailTrace_4470256
  have hstable : (prefixWord ++ tailWord_4470256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470256).length < 2 ^ (prefixWord ++ tailWord_4470256).sum := by decide
  have hdescent : baseEnd_4470256 < baseStart_4470256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470322 : List Nat := [3, 2, 1, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4470322 : Nat := 118140960795 + 4470322 * 2 ^ 59
def prefixEnd_4470322 : Nat := 4983230072969 + 3 ^ 40 * 4470322 * 2
def baseEnd_4470322 : Nat := 765141288789454692772123

theorem tailTrace_4470322 : CollatzResearch.WordTrace tailWord_4470322 prefixEnd_4470322 765141288789454692772123 := by
  unfold tailWord_4470322
  simp only [CollatzResearch.WordTrace]
  refine ⟨40761509527698584764935305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108697358740529559373160813 40761509527698584764935305)
  ·
    refine ⟨30571132145773938573701479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40761509527698584764935305 30571132145773938573701479)
    ·
      refine ⟨45856698218660907860552219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30571132145773938573701479 45856698218660907860552219)
      ·
        refine ⟨68785047327991361790828329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45856698218660907860552219 68785047327991361790828329)
        ·
          refine ⟨51588785495993521343121247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68785047327991361790828329 51588785495993521343121247)
          ·
            refine ⟨77383178243990282014681871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51588785495993521343121247 77383178243990282014681871)
            ·
              refine ⟨116074767365985423022022807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77383178243990282014681871 116074767365985423022022807)
              ·
                refine ⟨174112151048978134533034211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116074767365985423022022807 174112151048978134533034211)
                ·
                  refine ⟨261168226573467201799551317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174112151048978134533034211 261168226573467201799551317)
                  ·
                    refine ⟨765141288789454692772123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 261168226573467201799551317 765141288789454692772123)
                    ·
                      rfl

theorem cell23_4470322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4470322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470322 prefixEnd_4470322 := by exact prefixLift 4470322
  have htrace : WordTrace (prefixWord ++ tailWord_4470322) baseStart_4470322 baseEnd_4470322 := by
    simpa [prefixWord, tailWord_4470322, baseEnd_4470322] using wordTrace_append hprefix tailTrace_4470322
  have hstable : (prefixWord ++ tailWord_4470322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470322).length < 2 ^ (prefixWord ++ tailWord_4470322).sum := by decide
  have hdescent : baseEnd_4470322 < baseStart_4470322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470329 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4470329 : Nat := 118140960795 + 4470329 * 2 ^ 59
def prefixEnd_4470329 : Nat := 4983230072969 + 3 ^ 40 * 4470329 * 2
def baseEnd_4470329 : Nat := 2295427460732945550928837

theorem tailTrace_4470329 : CollatzResearch.WordTrace tailWord_4470329 prefixEnd_4470329 2295427460732945550928837 := by
  unfold tailWord_4470329
  simp only [CollatzResearch.WordTrace]
  refine ⟨163046293421768979255246041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108697528947845986170164027 163046293421768979255246041)
  ·
    refine ⟨122284720066326734441434531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163046293421768979255246041 122284720066326734441434531)
    ·
      refine ⟨183427080099490101662151797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122284720066326734441434531 183427080099490101662151797)
      ·
        refine ⟨17196288759327197030826731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 183427080099490101662151797 17196288759327197030826731)
        ·
          refine ⟨25794433138990795546240097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17196288759327197030826731 25794433138990795546240097)
          ·
            refine ⟨19345824854243096659680073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25794433138990795546240097 19345824854243096659680073)
            ·
              refine ⟨14509368640682322494760055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19345824854243096659680073 14509368640682322494760055)
              ·
                refine ⟨21764052961023483742140083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14509368640682322494760055 21764052961023483742140083)
                ·
                  refine ⟨32646079441535225613210125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21764052961023483742140083 32646079441535225613210125)
                  ·
                    refine ⟨12242279790575709604953797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32646079441535225613210125 12242279790575709604953797)
                    ·
                      refine ⟨2295427460732945550928837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12242279790575709604953797 2295427460732945550928837)
                      ·
                        rfl

theorem cell23_4470329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4470329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470329 prefixEnd_4470329 := by exact prefixLift 4470329
  have htrace : WordTrace (prefixWord ++ tailWord_4470329) baseStart_4470329 baseEnd_4470329 := by
    simpa [prefixWord, tailWord_4470329, baseEnd_4470329] using wordTrace_append hprefix tailTrace_4470329
  have hstable : (prefixWord ++ tailWord_4470329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470329).length < 2 ^ (prefixWord ++ tailWord_4470329).sum := by decide
  have hdescent : baseEnd_4470329 < baseStart_4470329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470352 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 8]
def baseStart_4470352 : Nat := 118140960795 + 4470352 * 2 ^ 59
def prefixEnd_4470352 : Nat := 4983230072969 + 3 ^ 40 * 4470352 * 2
def baseEnd_4470352 : Nat := 255048807865333217882359

theorem tailTrace_4470352 : CollatzResearch.WordTrace tailWord_4470352 prefixEnd_4470352 255048807865333217882359 := by
  unfold tailWord_4470352
  simp only [CollatzResearch.WordTrace]
  refine ⟨81523566150342827091666655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108698088200457102788888873 81523566150342827091666655)
  ·
    refine ⟨122285349225514240637499983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81523566150342827091666655 122285349225514240637499983)
    ·
      refine ⟨183428023838271360956249975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122285349225514240637499983 183428023838271360956249975)
      ·
        refine ⟨275142035757407041434374963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183428023838271360956249975 275142035757407041434374963)
        ·
          refine ⟨412713053636110562151562445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275142035757407041434374963 412713053636110562151562445)
          ·
            refine ⟨154767395113541460806835917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412713053636110562151562445 154767395113541460806835917)
            ·
              refine ⟨58037773167578047802563469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154767395113541460806835917 58037773167578047802563469)
              ·
                refine ⟨21764164937841767925961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58037773167578047802563469 21764164937841767925961301)
                ·
                  refine ⟨255048807865333217882359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21764164937841767925961301 255048807865333217882359)
                  ·
                    rfl

theorem cell23_4470352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 8].length) (baseStart_4470352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470352 prefixEnd_4470352 := by exact prefixLift 4470352
  have htrace : WordTrace (prefixWord ++ tailWord_4470352) baseStart_4470352 baseEnd_4470352 := by
    simpa [prefixWord, tailWord_4470352, baseEnd_4470352] using wordTrace_append hprefix tailTrace_4470352
  have hstable : (prefixWord ++ tailWord_4470352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470352).length < 2 ^ (prefixWord ++ tailWord_4470352).sum := by decide
  have hdescent : baseEnd_4470352 < baseStart_4470352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470358 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2]
def baseStart_4470358 : Nat := 118140960795 + 4470358 * 2 ^ 59
def prefixEnd_4470358 : Nat := 4983230072969 + 3 ^ 40 * 4470358 * 2
def baseEnd_4470358 : Nat := 2295442351671925937466205

theorem tailTrace_4470358 : CollatzResearch.WordTrace tailWord_4470358 prefixEnd_4470358 2295442351671925937466205 := by
  unfold tailWord_4470358
  simp only [CollatzResearch.WordTrace]
  refine ⟨10190459446166494825503233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108698234092442611472034485 10190459446166494825503233)
  ·
    refine ⟨7642844584624871119127425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10190459446166494825503233 7642844584624871119127425)
    ·
      refine ⟨5732133438468653339345569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7642844584624871119127425 5732133438468653339345569)
      ·
        refine ⟨4299100078851490004509177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5732133438468653339345569 4299100078851490004509177)
        ·
          refine ⟨3224325059138617503381883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299100078851490004509177 3224325059138617503381883)
          ·
            refine ⟨4836487588707926255072825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224325059138617503381883 4836487588707926255072825)
            ·
              refine ⟨3627365691530944691304619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4836487588707926255072825 3627365691530944691304619)
              ·
                refine ⟨5441048537296417036956929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627365691530944691304619 5441048537296417036956929)
                ·
                  refine ⟨4080786402972312777717697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5441048537296417036956929 4080786402972312777717697)
                  ·
                    refine ⟨3060589802229234583288273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4080786402972312777717697 3060589802229234583288273)
                    ·
                      refine ⟨2295442351671925937466205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060589802229234583288273 2295442351671925937466205)
                      ·
                        rfl

theorem cell23_4470358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_4470358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470358 prefixEnd_4470358 := by exact prefixLift 4470358
  have htrace : WordTrace (prefixWord ++ tailWord_4470358) baseStart_4470358 baseEnd_4470358 := by
    simpa [prefixWord, tailWord_4470358, baseEnd_4470358] using wordTrace_append hprefix tailTrace_4470358
  have hstable : (prefixWord ++ tailWord_4470358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470358).length < 2 ^ (prefixWord ++ tailWord_4470358).sum := by decide
  have hdescent : baseEnd_4470358 < baseStart_4470358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470369 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 6]
def baseStart_4470369 : Nat := 118140960795 + 4470369 * 2 ^ 59
def prefixEnd_4470369 : Nat := 4983230072969 + 3 ^ 40 * 4470369 * 2
def baseEnd_4470369 : Nat := 255049777773236154936517

theorem tailTrace_4470369 : CollatzResearch.WordTrace tailWord_4470369 prefixEnd_4470369 255049777773236154936517 := by
  unfold tailWord_4470369
  simp only [CollatzResearch.WordTrace]
  refine ⟨163047752341624066086702161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108698501561082710724468107 163047752341624066086702161)
  ·
    refine ⟨122285814256218049565026621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163047752341624066086702161 122285814256218049565026621)
    ·
      refine ⟨45857180346081768586884983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122285814256218049565026621 45857180346081768586884983)
      ·
        refine ⟨68785770519122652880327475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45857180346081768586884983 68785770519122652880327475)
        ·
          refine ⟨103178655778683979320491213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68785770519122652880327475 103178655778683979320491213)
          ·
            refine ⟨38691995917006492245184205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103178655778683979320491213 38691995917006492245184205)
            ·
              refine ⟨14509498468877434591944077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38691995917006492245184205 14509498468877434591944077)
              ·
                refine ⟨5441061925829037971979029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14509498468877434591944077 5441061925829037971979029)
                ·
                  refine ⟨255049777773236154936517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5441061925829037971979029 255049777773236154936517)
                  ·
                    rfl

theorem cell23_4470369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 6].length) (baseStart_4470369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470369 prefixEnd_4470369 := by exact prefixLift 4470369
  have htrace : WordTrace (prefixWord ++ tailWord_4470369) baseStart_4470369 baseEnd_4470369 := by
    simpa [prefixWord, tailWord_4470369, baseEnd_4470369] using wordTrace_append hprefix tailTrace_4470369
  have hstable : (prefixWord ++ tailWord_4470369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470369).length < 2 ^ (prefixWord ++ tailWord_4470369).sum := by decide
  have hdescent : baseEnd_4470369 < baseStart_4470369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470430 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4470430 : Nat := 118140960795 + 4470430 * 2 ^ 59
def prefixEnd_4470430 : Nat := 4983230072969 + 3 ^ 40 * 4470430 * 2
def baseEnd_4470430 : Nat := 2295479322279049655765873

theorem tailTrace_4470430 : CollatzResearch.WordTrace tailWord_4470430 prefixEnd_4470430 2295479322279049655765873 := by
  unfold tailWord_4470430
  simp only [CollatzResearch.WordTrace]
  refine ⟨20381247149300384188084093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108699984796268715669781829 20381247149300384188084093)
  ·
    refine ⟨7642967680987644070531535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20381247149300384188084093 7642967680987644070531535)
    ·
      refine ⟨11464451521481466105797303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7642967680987644070531535 11464451521481466105797303)
      ·
        refine ⟨17196677282222199158695955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11464451521481466105797303 17196677282222199158695955)
        ·
          refine ⟨25795015923333298738043933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17196677282222199158695955 25795015923333298738043933)
          ·
            refine ⟨9673130971249987026766475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25795015923333298738043933 9673130971249987026766475)
            ·
              refine ⟨14509696456874980540149713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9673130971249987026766475 14509696456874980540149713)
              ·
                refine ⟨10882272342656235405112285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14509696456874980540149713 10882272342656235405112285)
                ·
                  refine ⟨4080852128496088276917107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10882272342656235405112285 4080852128496088276917107)
                  ·
                    refine ⟨6121278192744132415375661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4080852128496088276917107 6121278192744132415375661)
                    ·
                      refine ⟨2295479322279049655765873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6121278192744132415375661 2295479322279049655765873)
                      ·
                        rfl

theorem cell23_4470430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4470430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470430 prefixEnd_4470430 := by exact prefixLift 4470430
  have htrace : WordTrace (prefixWord ++ tailWord_4470430) baseStart_4470430 baseEnd_4470430 := by
    simpa [prefixWord, tailWord_4470430, baseEnd_4470430] using wordTrace_append hprefix tailTrace_4470430
  have hstable : (prefixWord ++ tailWord_4470430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470430).length < 2 ^ (prefixWord ++ tailWord_4470430).sum := by decide
  have hdescent : baseEnd_4470430 < baseStart_4470430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470436 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_4470436 : Nat := 118140960795 + 4470436 * 2 ^ 59
def prefixEnd_4470436 : Nat := 4983230072969 + 3 ^ 40 * 4470436 * 2
def baseEnd_4470436 : Nat := 2295482403162976632290845

theorem tailTrace_4470436 : CollatzResearch.WordTrace tailWord_4470436 prefixEnd_4470436 2295482403162976632290845 := by
  unfold tailWord_4470436
  simp only [CollatzResearch.WordTrace]
  refine ⟨81525098016190668264695581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108700130688254224352927441 81525098016190668264695581)
  ·
    refine ⟨30571911756071500599260843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81525098016190668264695581 30571911756071500599260843)
    ·
      refine ⟨45857867634107250898891265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30571911756071500599260843 45857867634107250898891265)
      ·
        refine ⟨34393400725580438174168449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45857867634107250898891265 34393400725580438174168449)
        ·
          refine ⟨25795050544185328630626337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34393400725580438174168449 25795050544185328630626337)
          ·
            refine ⟨19346287908138996472969753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25795050544185328630626337 19346287908138996472969753)
            ·
              refine ⟨14509715931104247354727315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19346287908138996472969753 14509715931104247354727315)
              ·
                refine ⟨21764573896656371032090973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14509715931104247354727315 21764573896656371032090973)
                ·
                  refine ⟨8161715211246139137034115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21764573896656371032090973 8161715211246139137034115)
                  ·
                    refine ⟨12242572816869208705551173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8161715211246139137034115 12242572816869208705551173)
                    ·
                      refine ⟨2295482403162976632290845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12242572816869208705551173 2295482403162976632290845)
                      ·
                        rfl

theorem cell23_4470436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_4470436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470436 prefixEnd_4470436 := by exact prefixLift 4470436
  have htrace : WordTrace (prefixWord ++ tailWord_4470436) baseStart_4470436 baseEnd_4470436 := by
    simpa [prefixWord, tailWord_4470436, baseEnd_4470436] using wordTrace_append hprefix tailTrace_4470436
  have hstable : (prefixWord ++ tailWord_4470436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470436).length < 2 ^ (prefixWord ++ tailWord_4470436).sum := by decide
  have hdescent : baseEnd_4470436 < baseStart_4470436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470493 : List Nat := [1, 4, 3, 3, 1, 1, 1, 9]
def baseStart_4470493 : Nat := 118140960795 + 4470493 * 2 ^ 59
def prefixEnd_4470493 : Nat := 4983230072969 + 3 ^ 40 * 4470493 * 2
def baseEnd_4470493 : Nat := 85018950798528996639929

theorem tailTrace_4470493 : CollatzResearch.WordTrace tailWord_4470493 prefixEnd_4470493 85018950798528996639929 := by
  unfold tailWord_4470493
  simp only [CollatzResearch.WordTrace]
  refine ⟨163052274993174835264216133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108701516662116556842810755 163052274993174835264216133)
  ·
    refine ⟨30572301561220281612040525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163052274993174835264216133 30572301561220281612040525)
    ·
      refine ⟨11464613085457605604515197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30572301561220281612040525 11464613085457605604515197)
      ·
        refine ⟨4299229907046602101693199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11464613085457605604515197 4299229907046602101693199)
        ·
          refine ⟨6448844860569903152539799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4299229907046602101693199 6448844860569903152539799)
          ·
            refine ⟨9673267290854854728809699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6448844860569903152539799 9673267290854854728809699)
            ·
              refine ⟨14509900936282282093214549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9673267290854854728809699 14509900936282282093214549)
              ·
                refine ⟨85018950798528996639929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14509900936282282093214549 85018950798528996639929)
                ·
                  rfl

theorem cell23_4470493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 9].length) (baseStart_4470493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470493 prefixEnd_4470493 := by exact prefixLift 4470493
  have htrace : WordTrace (prefixWord ++ tailWord_4470493) baseStart_4470493 baseEnd_4470493 := by
    simpa [prefixWord, tailWord_4470493, baseEnd_4470493] using wordTrace_append hprefix tailTrace_4470493
  have hstable : (prefixWord ++ tailWord_4470493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470493).length < 2 ^ (prefixWord ++ tailWord_4470493).sum := by decide
  have hdescent : baseEnd_4470493 < baseStart_4470493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470504 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_4470504 : Nat := 118140960795 + 4470504 * 2 ^ 59
def prefixEnd_4470504 : Nat := 4983230072969 + 3 ^ 40 * 4470504 * 2
def baseEnd_4470504 : Nat := 2295517319847482366240533

theorem tailTrace_4470504 : CollatzResearch.WordTrace tailWord_4470504 prefixEnd_4470504 2295517319847482366240533 := by
  unfold tailWord_4470504
  simp only [CollatzResearch.WordTrace]
  refine ⟨81526338098067492071433283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108701784130756656095244377 81526338098067492071433283)
  ·
    refine ⟨122289507147101238107149925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81526338098067492071433283 122289507147101238107149925)
    ·
      refine ⟨22929282590081482145090611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122289507147101238107149925 22929282590081482145090611)
      ·
        refine ⟨34393923885122223217635917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22929282590081482145090611 34393923885122223217635917)
        ·
          refine ⟨12897721456920833706613469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34393923885122223217635917 12897721456920833706613469)
          ·
            refine ⟨4836645546345312639980051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12897721456920833706613469 4836645546345312639980051)
            ·
              refine ⟨7254968319517968959970077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4836645546345312639980051 7254968319517968959970077)
              ·
                refine ⟨2720613119819238359988779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7254968319517968959970077 2720613119819238359988779)
                ·
                  refine ⟨4080919679728857539983169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720613119819238359988779 4080919679728857539983169)
                  ·
                    refine ⟨3060689759796643154987377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4080919679728857539983169 3060689759796643154987377)
                    ·
                      refine ⟨2295517319847482366240533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060689759796643154987377 2295517319847482366240533)
                      ·
                        rfl

theorem cell23_4470504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_4470504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470504 prefixEnd_4470504 := by exact prefixLift 4470504
  have htrace : WordTrace (prefixWord ++ tailWord_4470504) baseStart_4470504 baseEnd_4470504 := by
    simpa [prefixWord, tailWord_4470504, baseEnd_4470504] using wordTrace_append hprefix tailTrace_4470504
  have hstable : (prefixWord ++ tailWord_4470504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470504).length < 2 ^ (prefixWord ++ tailWord_4470504).sum := by decide
  have hdescent : baseEnd_4470504 < baseStart_4470504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470519 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 4, 6]
def baseStart_4470519 : Nat := 118140960795 + 4470519 * 2 ^ 59
def prefixEnd_4470519 : Nat := 4983230072969 + 3 ^ 40 * 4470519 * 2
def baseEnd_4470519 : Nat := 765175007352433269184321

theorem tailTrace_4470519 : CollatzResearch.WordTrace tailWord_4470519 prefixEnd_4470519 765175007352433269184321 := by
  unfold tailWord_4470519
  simp only [CollatzResearch.WordTrace]
  refine ⟨163053223291080641704662611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108702148860720427803108407 163053223291080641704662611)
  ·
    refine ⟨244579834936620962556993917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163053223291080641704662611 244579834936620962556993917)
    ·
      refine ⟨91717438101232860958872719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244579834936620962556993917 91717438101232860958872719)
      ·
        refine ⟨137576157151849291438309079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91717438101232860958872719 137576157151849291438309079)
        ·
          refine ⟨206364235727773937157463619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137576157151849291438309079 206364235727773937157463619)
          ·
            refine ⟨309546353591660905736195429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206364235727773937157463619 309546353591660905736195429)
            ·
              refine ⟨58039941298436419825536643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 309546353591660905736195429 58039941298436419825536643)
              ·
                refine ⟨87059911947654629738304965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58039941298436419825536643 87059911947654629738304965)
                ·
                  refine ⟨16323733490185243075932181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87059911947654629738304965 16323733490185243075932181)
                  ·
                    refine ⟨765175007352433269184321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16323733490185243075932181 765175007352433269184321)
                    ·
                      rfl

theorem cell23_4470519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_4470519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470519 prefixEnd_4470519 := by exact prefixLift 4470519
  have htrace : WordTrace (prefixWord ++ tailWord_4470519) baseStart_4470519 baseEnd_4470519 := by
    simpa [prefixWord, tailWord_4470519, baseEnd_4470519] using wordTrace_append hprefix tailTrace_4470519
  have hstable : (prefixWord ++ tailWord_4470519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470519).length < 2 ^ (prefixWord ++ tailWord_4470519).sum := by decide
  have hdescent : baseEnd_4470519 < baseStart_4470519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470530 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 3, 3, 2]
def baseStart_4470530 : Nat := 118140960795 + 4470530 * 2 ^ 59
def prefixEnd_4470530 : Nat := 4983230072969 + 3 ^ 40 * 4470530 * 2
def baseEnd_4470530 : Nat := 2295530670344499264515413

theorem tailTrace_4470530 : CollatzResearch.WordTrace tailWord_4470530 prefixEnd_4470530 2295530670344499264515413 := by
  unfold tailWord_4470530
  simp only [CollatzResearch.WordTrace]
  refine ⟨40763406123510197645828261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108702416329360527055542029 40763406123510197645828261)
  ·
    refine ⟨7643138648158162058592799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40763406123510197645828261 7643138648158162058592799)
    ·
      refine ⟨11464707972237243087889199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7643138648158162058592799 11464707972237243087889199)
      ·
        refine ⟨17197061958355864631833799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11464707972237243087889199 17197061958355864631833799)
        ·
          refine ⟨25795592937533796947750699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17197061958355864631833799 25795592937533796947750699)
          ·
            refine ⟨38693389406300695421626049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25795592937533796947750699 38693389406300695421626049)
            ·
              refine ⟨29020042054725521566219537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38693389406300695421626049 29020042054725521566219537)
              ·
                refine ⟨21765031541044141174664653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29020042054725521566219537 21765031541044141174664653)
                ·
                  refine ⟨8161886827891552940499245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21765031541044141174664653 8161886827891552940499245)
                  ·
                    refine ⟨3060707560459332352687217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8161886827891552940499245 3060707560459332352687217)
                    ·
                      refine ⟨2295530670344499264515413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060707560459332352687217 2295530670344499264515413)
                      ·
                        rfl

theorem cell23_4470530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_4470530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470530 prefixEnd_4470530 := by exact prefixLift 4470530
  have htrace : WordTrace (prefixWord ++ tailWord_4470530) baseStart_4470530 baseEnd_4470530 := by
    simpa [prefixWord, tailWord_4470530, baseEnd_4470530] using wordTrace_append hprefix tailTrace_4470530
  have hstable : (prefixWord ++ tailWord_4470530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470530).length < 2 ^ (prefixWord ++ tailWord_4470530).sum := by decide
  have hdescent : baseEnd_4470530 < baseStart_4470530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470543 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 6, 2, 2]
def baseStart_4470543 : Nat := 118140960795 + 4470543 * 2 ^ 59
def prefixEnd_4470543 : Nat := 4983230072969 + 3 ^ 40 * 4470543 * 2
def baseEnd_4470543 : Nat := 2295537345593007713652853

theorem tailTrace_4470543 : CollatzResearch.WordTrace tailWord_4470543 prefixEnd_4470543 2295537345593007713652853 := by
  unfold tailWord_4470543
  simp only [CollatzResearch.WordTrace]
  refine ⟨163054098642993693803536283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108702732428662462535690855 163054098642993693803536283)
  ·
    refine ⟨244581147964490540705304425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163054098642993693803536283 244581147964490540705304425)
    ·
      refine ⟨183435860973367905528978319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244581147964490540705304425 183435860973367905528978319)
      ·
        refine ⟨275153791460051858293467479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183435860973367905528978319 275153791460051858293467479)
        ·
          refine ⟨412730687190077787440201219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275153791460051858293467479 412730687190077787440201219)
          ·
            refine ⟨619096030785116681160301829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412730687190077787440201219 619096030785116681160301829)
            ·
              refine ⟨116080505772209377717556593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 619096030785116681160301829 116080505772209377717556593)
              ·
                refine ⟨87060379329157033288167445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116080505772209377717556593 87060379329157033288167445)
                ·
                  refine ⟨4080955281054235935382849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87060379329157033288167445 4080955281054235935382849)
                  ·
                    refine ⟨3060716460790676951537137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4080955281054235935382849 3060716460790676951537137)
                    ·
                      refine ⟨2295537345593007713652853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060716460790676951537137 2295537345593007713652853)
                      ·
                        rfl

theorem cell23_4470543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 2, 2].length) (baseStart_4470543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470543 prefixEnd_4470543 := by exact prefixLift 4470543
  have htrace : WordTrace (prefixWord ++ tailWord_4470543) baseStart_4470543 baseEnd_4470543 := by
    simpa [prefixWord, tailWord_4470543, baseEnd_4470543] using wordTrace_append hprefix tailTrace_4470543
  have hstable : (prefixWord ++ tailWord_4470543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470543).length < 2 ^ (prefixWord ++ tailWord_4470543).sum := by decide
  have hdescent : baseEnd_4470543 < baseStart_4470543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470569 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 6]
def baseStart_4470569 : Nat := 118140960795 + 4470569 * 2 ^ 59
def prefixEnd_4470569 : Nat := 4983230072969 + 3 ^ 40 * 4470569 * 2
def baseEnd_4470569 : Nat := 2295550696090024611927733

theorem tailTrace_4470569 : CollatzResearch.WordTrace tailWord_4470569 prefixEnd_4470569 2295550696090024611927733 := by
  unfold tailWord_4470569
  simp only [CollatzResearch.WordTrace]
  refine ⟨163055046940899500243982761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108703364627266333495988507 163055046940899500243982761)
  ·
    refine ⟨122291285205674625182987071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163055046940899500243982761 122291285205674625182987071)
    ·
      refine ⟨183436927808511937774480607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122291285205674625182987071 183436927808511937774480607)
      ·
        refine ⟨275155391712767906661720911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183436927808511937774480607 275155391712767906661720911)
        ·
          refine ⟨412733087569151859992581367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275155391712767906661720911 412733087569151859992581367)
          ·
            refine ⟨619099631353727789988872051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412733087569151859992581367 619099631353727789988872051)
            ·
              refine ⟨928649447030591684983308077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619099631353727789988872051 928649447030591684983308077)
              ·
                refine ⟨348243542636471881868740529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 928649447030591684983308077 348243542636471881868740529)
                ·
                  refine ⟨261182656977353911401555397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 348243542636471881868740529 261182656977353911401555397)
                  ·
                    refine ⟨48971748183253858387791637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 261182656977353911401555397 48971748183253858387791637)
                    ·
                      refine ⟨2295550696090024611927733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48971748183253858387791637 2295550696090024611927733)
                      ·
                        rfl

theorem cell23_4470569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_4470569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470569 prefixEnd_4470569 := by exact prefixLift 4470569
  have htrace : WordTrace (prefixWord ++ tailWord_4470569) baseStart_4470569 baseEnd_4470569 := by
    simpa [prefixWord, tailWord_4470569, baseEnd_4470569] using wordTrace_append hprefix tailTrace_4470569
  have hstable : (prefixWord ++ tailWord_4470569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470569).length < 2 ^ (prefixWord ++ tailWord_4470569).sum := by decide
  have hdescent : baseEnd_4470569 < baseStart_4470569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470577 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_4470577 : Nat := 118140960795 + 4470577 * 2 ^ 59
def prefixEnd_4470577 : Nat := 4983230072969 + 3 ^ 40 * 4470577 * 2
def baseEnd_4470577 : Nat := 2295554803935260580627697

theorem tailTrace_4470577 : CollatzResearch.WordTrace tailWord_4470577 prefixEnd_4470577 2295554803935260580627697 := by
  unfold tailWord_4470577
  simp only [CollatzResearch.WordTrace]
  refine ⟨163055338724870517610273985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108703559149913678406849323 163055338724870517610273985)
  ·
    refine ⟨122291504043652888207705489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163055338724870517610273985 122291504043652888207705489)
    ·
      refine ⟨91718628032739666155779117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122291504043652888207705489 91718628032739666155779117)
      ·
        refine ⟨34394485512277374808417169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91718628032739666155779117 34394485512277374808417169)
        ·
          refine ⟨25795864134208031106312877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34394485512277374808417169 25795864134208031106312877)
          ·
            refine ⟨9673449050328011664867329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25795864134208031106312877 9673449050328011664867329)
            ·
              refine ⟨7255086787746008748650497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9673449050328011664867329 7255086787746008748650497)
              ·
                refine ⟨5441315090809506561487873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7255086787746008748650497 5441315090809506561487873)
                ·
                  refine ⟨4080986318107129921115905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5441315090809506561487873 4080986318107129921115905)
                  ·
                    refine ⟨3060739738580347440836929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4080986318107129921115905 3060739738580347440836929)
                    ·
                      refine ⟨2295554803935260580627697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060739738580347440836929 2295554803935260580627697)
                      ·
                        rfl

theorem cell23_4470577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_4470577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470577 prefixEnd_4470577 := by exact prefixLift 4470577
  have htrace : WordTrace (prefixWord ++ tailWord_4470577) baseStart_4470577 baseEnd_4470577 := by
    simpa [prefixWord, tailWord_4470577, baseEnd_4470577] using wordTrace_append hprefix tailTrace_4470577
  have hstable : (prefixWord ++ tailWord_4470577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470577).length < 2 ^ (prefixWord ++ tailWord_4470577).sum := by decide
  have hdescent : baseEnd_4470577 < baseStart_4470577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470613 : List Nat := [1, 3, 2, 2, 2, 2, 3, 1, 2, 5]
def baseStart_4470613 : Nat := 118140960795 + 4470613 * 2 ^ 59
def prefixEnd_4470613 : Nat := 4983230072969 + 3 ^ 40 * 4470613 * 2
def baseEnd_4470613 : Nat := 765191096412940813259177

theorem tailTrace_4470613 : CollatzResearch.WordTrace tailWord_4470613 prefixEnd_4470613 765191096412940813259177 := by
  unfold tailWord_4470613
  simp only [CollatzResearch.WordTrace]
  refine ⟨163056651752740095758584493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108704434501826730505722995 163056651752740095758584493)
  ·
    refine ⟨61146244407277535909469185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163056651752740095758584493 61146244407277535909469185)
    ·
      refine ⟨45859683305458151932101889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61146244407277535909469185 45859683305458151932101889)
      ·
        refine ⟨34394762479093613949076417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45859683305458151932101889 34394762479093613949076417)
        ·
          refine ⟨25796071859320210461807313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34394762479093613949076417 25796071859320210461807313)
          ·
            refine ⟨19347053894490157846355485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25796071859320210461807313 19347053894490157846355485)
            ·
              refine ⟨7255145210433809192383307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19347053894490157846355485 7255145210433809192383307)
              ·
                refine ⟨10882717815650713788574961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7255145210433809192383307 10882717815650713788574961)
                ·
                  refine ⟨8162038361738035341431221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10882717815650713788574961 8162038361738035341431221)
                  ·
                    refine ⟨765191096412940813259177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8162038361738035341431221 765191096412940813259177)
                    ·
                      rfl

theorem cell23_4470613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_4470613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470613 prefixEnd_4470613 := by exact prefixLift 4470613
  have htrace : WordTrace (prefixWord ++ tailWord_4470613) baseStart_4470613 baseEnd_4470613 := by
    simpa [prefixWord, tailWord_4470613, baseEnd_4470613] using wordTrace_append hprefix tailTrace_4470613
  have hstable : (prefixWord ++ tailWord_4470613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470613).length < 2 ^ (prefixWord ++ tailWord_4470613).sum := by decide
  have hdescent : baseEnd_4470613 < baseStart_4470613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470746 : List Nat := [3, 1, 1, 2, 16]
def baseStart_4470746 : Nat := 118140960795 + 4470746 * 2 ^ 59
def prefixEnd_4470746 : Nat := 4983230072969 + 3 ^ 40 * 4470746 * 2
def baseEnd_4470746 : Nat := 3149028233423690561611

theorem tailTrace_4470746 : CollatzResearch.WordTrace tailWord_4470746 prefixEnd_4470746 3149028233423690561611 := by
  unfold tailWord_4470746
  simp only [CollatzResearch.WordTrace]
  refine ⟨40765375665314564868294023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108707668440838839648784061 40765375665314564868294023)
  ·
    refine ⟨61148063497971847302441035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40765375665314564868294023 61148063497971847302441035)
    ·
      refine ⟨91722095246957770953661553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61148063497971847302441035 91722095246957770953661553)
      ·
        refine ⟨68791571435218328215246165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91722095246957770953661553 68791571435218328215246165)
        ·
          refine ⟨3149028233423690561611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 68791571435218328215246165 3149028233423690561611)
          ·
            rfl

theorem cell23_4470746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 16].length) (baseStart_4470746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470746 prefixEnd_4470746 := by exact prefixLift 4470746
  have htrace : WordTrace (prefixWord ++ tailWord_4470746) baseStart_4470746 baseEnd_4470746 := by
    simpa [prefixWord, tailWord_4470746, baseEnd_4470746] using wordTrace_append hprefix tailTrace_4470746
  have hstable : (prefixWord ++ tailWord_4470746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470746).length < 2 ^ (prefixWord ++ tailWord_4470746).sum := by decide
  have hdescent : baseEnd_4470746 < baseStart_4470746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470751 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 1, 1, 3]
def baseStart_4470751 : Nat := 118140960795 + 4470751 * 2 ^ 59
def prefixEnd_4470751 : Nat := 4983230072969 + 3 ^ 40 * 4470751 * 2
def baseEnd_4470751 : Nat := 2295644149569142899851897

theorem tailTrace_4470751 : CollatzResearch.WordTrace tailWord_4470751 prefixEnd_4470751 2295644149569142899851897 := by
  unfold tailWord_4470751
  simp only [CollatzResearch.WordTrace]
  refine ⟨163061685026240145327108107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108707790017493430218072071 163061685026240145327108107)
  ·
    refine ⟨244592527539360217990662161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163061685026240145327108107 244592527539360217990662161)
    ·
      refine ⟨183444395654520163492996621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244592527539360217990662161 183444395654520163492996621)
      ·
        refine ⟨68791648370445061309873733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183444395654520163492996621 68791648370445061309873733)
        ·
          refine ⟨12898434069458448995601325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68791648370445061309873733 12898434069458448995601325)
          ·
            refine ⟨4836912776046918373350497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12898434069458448995601325 4836912776046918373350497)
            ·
              refine ⟨3627684582035188780012873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4836912776046918373350497 3627684582035188780012873)
              ·
                refine ⟨2720763436526391585009655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3627684582035188780012873 2720763436526391585009655)
                ·
                  refine ⟨4081145154789587377514483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720763436526391585009655 4081145154789587377514483)
                  ·
                    refine ⟨6121717732184381066271725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4081145154789587377514483 6121717732184381066271725)
                    ·
                      refine ⟨2295644149569142899851897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6121717732184381066271725 2295644149569142899851897)
                      ·
                        rfl

theorem cell23_4470751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_4470751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470751 prefixEnd_4470751 := by exact prefixLift 4470751
  have htrace : WordTrace (prefixWord ++ tailWord_4470751) baseStart_4470751 baseEnd_4470751 := by
    simpa [prefixWord, tailWord_4470751, baseEnd_4470751] using wordTrace_append hprefix tailTrace_4470751
  have hstable : (prefixWord ++ tailWord_4470751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470751).length < 2 ^ (prefixWord ++ tailWord_4470751).sum := by decide
  have hdescent : baseEnd_4470751 < baseStart_4470751 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470791 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 1, 2, 2]
def baseStart_4470791 : Nat := 118140960795 + 4470791 * 2 ^ 59
def prefixEnd_4470791 : Nat := 4983230072969 + 3 ^ 40 * 4470791 * 2
def baseEnd_4470791 : Nat := 2295664688795322743351713

theorem tailTrace_4470791 : CollatzResearch.WordTrace tailWord_4470791 prefixEnd_4470791 2295664688795322743351713 := by
  unfold tailWord_4470791
  simp only [CollatzResearch.WordTrace]
  refine ⟨163063143946095232158564227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108708762630730154772376151 163063143946095232158564227)
  ·
    refine ⟨244594715919142848237846341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163063143946095232158564227 244594715919142848237846341)
    ·
      refine ⟨45861509234839284044596189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244594715919142848237846341 45861509234839284044596189)
      ·
        refine ⟨17198065963064731516723571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45861509234839284044596189 17198065963064731516723571)
        ·
          refine ⟨25797098944597097275085357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17198065963064731516723571 25797098944597097275085357)
          ·
            refine ⟨9673912104223911478157009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25797098944597097275085357 9673912104223911478157009)
            ·
              refine ⟨7255434078167933608617757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9673912104223911478157009 7255434078167933608617757)
              ·
                refine ⟨2720787779312975103231659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7255434078167933608617757 2720787779312975103231659)
                ·
                  refine ⟨4081181668969462654847489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2720787779312975103231659 4081181668969462654847489)
                  ·
                    refine ⟨3060886251727096991135617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081181668969462654847489 3060886251727096991135617)
                    ·
                      refine ⟨2295664688795322743351713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060886251727096991135617 2295664688795322743351713)
                      ·
                        rfl

theorem cell23_4470791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_4470791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470791 prefixEnd_4470791 := by exact prefixLift 4470791
  have htrace : WordTrace (prefixWord ++ tailWord_4470791) baseStart_4470791 baseEnd_4470791 := by
    simpa [prefixWord, tailWord_4470791, baseEnd_4470791] using wordTrace_append hprefix tailTrace_4470791
  have hstable : (prefixWord ++ tailWord_4470791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470791).length < 2 ^ (prefixWord ++ tailWord_4470791).sum := by decide
  have hdescent : baseEnd_4470791 < baseStart_4470791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470834 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_4470834 : Nat := 118140960795 + 4470834 * 2 ^ 59
def prefixEnd_4470834 : Nat := 4983230072969 + 3 ^ 40 * 4470834 * 2
def baseEnd_4470834 : Nat := 2295686768463466075114015

theorem tailTrace_4470834 : CollatzResearch.WordTrace tailWord_4470834 prefixEnd_4470834 2295686768463466075114015 := by
  unfold tailWord_4470834
  simp only [CollatzResearch.WordTrace]
  refine ⟨40766178071234862625594889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108709808189959633668253037 40766178071234862625594889)
  ·
    refine ⟨30574633553426146969196167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40766178071234862625594889 30574633553426146969196167)
    ·
      refine ⟨45861950330139220453794251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30574633553426146969196167 45861950330139220453794251)
      ·
        refine ⟨68792925495208830680691377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45861950330139220453794251 68792925495208830680691377)
        ·
          refine ⟨51594694121406623010518533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68792925495208830680691377 51594694121406623010518533)
          ·
            refine ⟨9674005147763741814472225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51594694121406623010518533 9674005147763741814472225)
            ·
              refine ⟨7255503860822806360854169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9674005147763741814472225 7255503860822806360854169)
              ·
                refine ⟨5441627895617104770640627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7255503860822806360854169 5441627895617104770640627)
                ·
                  refine ⟨8162441843425657155960941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441627895617104770640627 8162441843425657155960941)
                  ·
                    refine ⟨3060915691284621433485353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8162441843425657155960941 3060915691284621433485353)
                    ·
                      refine ⟨2295686768463466075114015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060915691284621433485353 2295686768463466075114015)
                      ·
                        rfl

theorem cell23_4470834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_4470834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470834 prefixEnd_4470834 := by exact prefixLift 4470834
  have htrace : WordTrace (prefixWord ++ tailWord_4470834) baseStart_4470834 baseEnd_4470834 := by
    simpa [prefixWord, tailWord_4470834, baseEnd_4470834] using wordTrace_append hprefix tailTrace_4470834
  have hstable : (prefixWord ++ tailWord_4470834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470834).length < 2 ^ (prefixWord ++ tailWord_4470834).sum := by decide
  have hdescent : baseEnd_4470834 < baseStart_4470834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470847 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 4, 2, 2]
def baseStart_4470847 : Nat := 118140960795 + 4470847 * 2 ^ 59
def prefixEnd_4470847 : Nat := 4983230072969 + 3 ^ 40 * 4470847 * 2
def baseEnd_4470847 : Nat := 2295693443711974524251455

theorem tailTrace_4470847 : CollatzResearch.WordTrace tailWord_4470847 prefixEnd_4470847 2295693443711974524251455 := by
  unfold tailWord_4470847
  simp only [CollatzResearch.WordTrace]
  refine ⟨163065186433892353722602795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108710124289261569148401863 163065186433892353722602795)
  ·
    refine ⟨244597779650838530583904193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163065186433892353722602795 244597779650838530583904193)
    ·
      refine ⟨183448334738128897937928145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244597779650838530583904193 183448334738128897937928145)
      ·
        refine ⟨137586251053596673453446109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183448334738128897937928145 137586251053596673453446109)
        ·
          refine ⟨51594844145098752545042291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137586251053596673453446109 51594844145098752545042291)
          ·
            refine ⟨77392266217648128817563437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51594844145098752545042291 77392266217648128817563437)
            ·
              refine ⟨29022099831618048306586289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77392266217648128817563437 29022099831618048306586289)
              ·
                refine ⟨21766574873713536229939717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29022099831618048306586289 21766574873713536229939717)
                ·
                  refine ⟨4081232788821288043113697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21766574873713536229939717 4081232788821288043113697)
                  ·
                    refine ⟨3060924591615966032335273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081232788821288043113697 3060924591615966032335273)
                    ·
                      refine ⟨2295693443711974524251455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3060924591615966032335273 2295693443711974524251455)
                      ·
                        rfl

theorem cell23_4470847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_4470847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470847 prefixEnd_4470847 := by exact prefixLift 4470847
  have htrace : WordTrace (prefixWord ++ tailWord_4470847) baseStart_4470847 baseEnd_4470847 := by
    simpa [prefixWord, tailWord_4470847, baseEnd_4470847] using wordTrace_append hprefix tailTrace_4470847
  have hstable : (prefixWord ++ tailWord_4470847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470847).length < 2 ^ (prefixWord ++ tailWord_4470847).sum := by decide
  have hdescent : baseEnd_4470847 < baseStart_4470847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470883 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 3, 7]
def baseStart_4470883 : Nat := 118140960795 + 4470883 * 2 ^ 59
def prefixEnd_4470883 : Nat := 4983230072969 + 3 ^ 40 * 4470883 * 2
def baseEnd_4470883 : Nat := 765237309671845461133763

theorem tailTrace_4470883 : CollatzResearch.WordTrace tailWord_4470883 prefixEnd_4470883 765237309671845461133763 := by
  unfold tailWord_4470883
  simp only [CollatzResearch.WordTrace]
  refine ⟨163066499461761931870913303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108710999641174621247275535 163066499461761931870913303)
  ·
    refine ⟨244599749192642897806369955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163066499461761931870913303 244599749192642897806369955)
    ·
      refine ⟨366899623788964346709554933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244599749192642897806369955 366899623788964346709554933)
      ·
        refine ⟨34396839730215407504020775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 366899623788964346709554933 34396839730215407504020775)
        ·
          refine ⟨51595259595323111256031163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34396839730215407504020775 51595259595323111256031163)
          ·
            refine ⟨77392889392984666884046745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51595259595323111256031163 77392889392984666884046745)
            ·
              refine ⟨58044667044738500163035059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77392889392984666884046745 58044667044738500163035059)
              ·
                refine ⟨87067000567107750244552589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58044667044738500163035059 87067000567107750244552589)
                ·
                  refine ⟨32650125212665406341707221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87067000567107750244552589 32650125212665406341707221)
                  ·
                    refine ⟨765237309671845461133763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32650125212665406341707221 765237309671845461133763)
                    ·
                      rfl

theorem cell23_4470883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 7].length) (baseStart_4470883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470883 prefixEnd_4470883 := by exact prefixLift 4470883
  have htrace : WordTrace (prefixWord ++ tailWord_4470883) baseStart_4470883 baseEnd_4470883 := by
    simpa [prefixWord, tailWord_4470883, baseEnd_4470883] using wordTrace_append hprefix tailTrace_4470883
  have hstable : (prefixWord ++ tailWord_4470883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470883).length < 2 ^ (prefixWord ++ tailWord_4470883).sum := by decide
  have hdescent : baseEnd_4470883 < baseStart_4470883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470951 : List Nat := [1, 1, 6, 2, 3, 1, 1, 1, 2, 5]
def baseStart_4470951 : Nat := 118140960795 + 4470951 * 2 ^ 59
def prefixEnd_4470951 : Nat := 4983230072969 + 3 ^ 40 * 4470951 * 2
def baseEnd_4470951 : Nat := 765248948566680705783659

theorem tailTrace_4470951 : CollatzResearch.WordTrace tailWord_4470951 prefixEnd_4470951 765248948566680705783659 := by
  unfold tailWord_4470951
  simp only [CollatzResearch.WordTrace]
  refine ⟨163068979625515579484388707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108712653083677052989592471 163068979625515579484388707)
  ·
    refine ⟨244603469438273369226583061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163068979625515579484388707 244603469438273369226583061)
    ·
      refine ⟨11465787629919064182496081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 244603469438273369226583061 11465787629919064182496081)
      ·
        refine ⟨8599340722439298136872061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11465787629919064182496081 8599340722439298136872061)
        ·
          refine ⟨3224752770914736801327023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8599340722439298136872061 3224752770914736801327023)
          ·
            refine ⟨4837129156372105201990535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224752770914736801327023 4837129156372105201990535)
            ·
              refine ⟨7255693734558157802985803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4837129156372105201990535 7255693734558157802985803)
              ·
                refine ⟨10883540601837236704478705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7255693734558157802985803 10883540601837236704478705)
                ·
                  refine ⟨8162655451377927528359029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10883540601837236704478705 8162655451377927528359029)
                  ·
                    refine ⟨765248948566680705783659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8162655451377927528359029 765248948566680705783659)
                    ·
                      rfl

theorem cell23_4470951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_4470951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470951 prefixEnd_4470951 := by exact prefixLift 4470951
  have htrace : WordTrace (prefixWord ++ tailWord_4470951) baseStart_4470951 baseEnd_4470951 := by
    simpa [prefixWord, tailWord_4470951, baseEnd_4470951] using wordTrace_append hprefix tailTrace_4470951
  have hstable : (prefixWord ++ tailWord_4470951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470951).length < 2 ^ (prefixWord ++ tailWord_4470951).sum := by decide
  have hdescent : baseEnd_4470951 < baseStart_4470951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470953 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 9]
def baseStart_4470953 : Nat := 118140960795 + 4470953 * 2 ^ 59
def prefixEnd_4470953 : Nat := 4983230072969 + 3 ^ 40 * 4470953 * 2
def baseEnd_4470953 : Nat := 2295747872661351109525967

theorem tailTrace_4470953 : CollatzResearch.WordTrace tailWord_4470953 prefixEnd_4470953 2295747872661351109525967 := by
  unfold tailWord_4470953
  simp only [CollatzResearch.WordTrace]
  refine ⟨163069052571508333825961513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108712701714338889217307675 163069052571508333825961513)
  ·
    refine ⟨122301789428631250369471135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163069052571508333825961513 122301789428631250369471135)
    ·
      refine ⟨183452684142946875554206703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122301789428631250369471135 183452684142946875554206703)
      ·
        refine ⟨275179026214420313331310055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183452684142946875554206703 275179026214420313331310055)
        ·
          refine ⟨412768539321630469996965083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275179026214420313331310055 412768539321630469996965083)
          ·
            refine ⟨619152808982445704995447625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 412768539321630469996965083 619152808982445704995447625)
            ·
              refine ⟨464364606736834278746585719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 619152808982445704995447625 464364606736834278746585719)
              ·
                refine ⟨696546910105251418119878579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 464364606736834278746585719 696546910105251418119878579)
                ·
                  refine ⟨1044820365157877127179817869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 696546910105251418119878579 1044820365157877127179817869)
                  ·
                    refine ⟨391807636934203922692431701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1044820365157877127179817869 391807636934203922692431701)
                    ·
                      refine ⟨2295747872661351109525967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 391807636934203922692431701 2295747872661351109525967)
                      ·
                        rfl

theorem cell23_4470953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_4470953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470953 prefixEnd_4470953 := by exact prefixLift 4470953
  have htrace : WordTrace (prefixWord ++ tailWord_4470953) baseStart_4470953 baseEnd_4470953 := by
    simpa [prefixWord, tailWord_4470953, baseEnd_4470953] using wordTrace_append hprefix tailTrace_4470953
  have hstable : (prefixWord ++ tailWord_4470953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470953).length < 2 ^ (prefixWord ++ tailWord_4470953).sum := by decide
  have hdescent : baseEnd_4470953 < baseStart_4470953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470954 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4470954 : Nat := 118140960795 + 4470954 * 2 ^ 59
def prefixEnd_4470954 : Nat := 4983230072969 + 3 ^ 40 * 4470954 * 2
def baseEnd_4470954 : Nat := 2295748386142005605613463

theorem tailTrace_4470954 : CollatzResearch.WordTrace tailWord_4470954 prefixEnd_4470954 2295748386142005605613463 := by
  unfold tailWord_4470954
  simp only [CollatzResearch.WordTrace]
  refine ⟨40767272261126177749186979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108712726029669807331165277 40767272261126177749186979)
  ·
    refine ⟨61150908391689266623780469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40767272261126177749186979 61150908391689266623780469)
    ·
      refine ⟨5732897661720868745979419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61150908391689266623780469 5732897661720868745979419)
      ·
        refine ⟨8599346492581303118969129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5732897661720868745979419 8599346492581303118969129)
        ·
          refine ⟨6449509869435977339226847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8599346492581303118969129 6449509869435977339226847)
          ·
            refine ⟨9674264804153966008840271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6449509869435977339226847 9674264804153966008840271)
            ·
              refine ⟨14511397206230949013260407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674264804153966008840271 14511397206230949013260407)
              ·
                refine ⟨21767095809346423519890611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14511397206230949013260407 21767095809346423519890611)
                ·
                  refine ⟨32650643714019635279835917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21767095809346423519890611 32650643714019635279835917)
                  ·
                    refine ⟨12243991392757363229938469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32650643714019635279835917 12243991392757363229938469)
                    ·
                      refine ⟨2295748386142005605613463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12243991392757363229938469 2295748386142005605613463)
                      ·
                        rfl

theorem cell23_4470954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4470954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470954 prefixEnd_4470954 := by exact prefixLift 4470954
  have htrace : WordTrace (prefixWord ++ tailWord_4470954) baseStart_4470954 baseEnd_4470954 := by
    simpa [prefixWord, tailWord_4470954, baseEnd_4470954] using wordTrace_append hprefix tailTrace_4470954
  have hstable : (prefixWord ++ tailWord_4470954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470954).length < 2 ^ (prefixWord ++ tailWord_4470954).sum := by decide
  have hdescent : baseEnd_4470954 < baseStart_4470954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4470994 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 6]
def baseStart_4470994 : Nat := 118140960795 + 4470994 * 2 ^ 59
def prefixEnd_4470994 : Nat := 4983230072969 + 3 ^ 40 * 4470994 * 2
def baseEnd_4470994 : Nat := 255085436152020605457031

theorem tailTrace_4470994 : CollatzResearch.WordTrace tailWord_4470994 prefixEnd_4470994 255085436152020605457031 := by
  unfold tailWord_4470994
  simp only [CollatzResearch.WordTrace]
  refine ⟨40767636991089949457051009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108713698642906531885469357 40767636991089949457051009)
  ·
    refine ⟨30575727743317462092788257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40767636991089949457051009 30575727743317462092788257)
    ·
      refine ⟨22931795807488096569591193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30575727743317462092788257 22931795807488096569591193)
      ·
        refine ⟨17198846855616072427193395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22931795807488096569591193 17198846855616072427193395)
        ·
          refine ⟨25798270283424108640790093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17198846855616072427193395 25798270283424108640790093)
          ·
            refine ⟨9674351356284040740296285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25798270283424108640790093 9674351356284040740296285)
            ·
              refine ⟨3627881758606515277611107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9674351356284040740296285 3627881758606515277611107)
              ·
                refine ⟨5441822637909772916416661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627881758606515277611107 5441822637909772916416661)
                ·
                  refine ⟨255085436152020605457031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5441822637909772916416661 255085436152020605457031)
                  ·
                    rfl

theorem cell23_4470994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_4470994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4470994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4470994 prefixEnd_4470994 := by exact prefixLift 4470994
  have htrace : WordTrace (prefixWord ++ tailWord_4470994) baseStart_4470994 baseEnd_4470994 := by
    simpa [prefixWord, tailWord_4470994, baseEnd_4470994] using wordTrace_append hprefix tailTrace_4470994
  have hstable : (prefixWord ++ tailWord_4470994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4470994).length < 2 ^ (prefixWord ++ tailWord_4470994).sum := by decide
  have hdescent : baseEnd_4470994 < baseStart_4470994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4470994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471020 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 3, 6]
def baseStart_4471020 : Nat := 118140960795 + 4471020 * 2 ^ 59
def prefixEnd_4471020 : Nat := 4983230072969 + 3 ^ 40 * 4471020 * 2
def baseEnd_4471020 : Nat := 765260758621734115796053

theorem tailTrace_4471020 : CollatzResearch.WordTrace tailWord_4471020 prefixEnd_4471020 765260758621734115796053 := by
  unfold tailWord_4471020
  simp only [CollatzResearch.WordTrace]
  refine ⟨81535748131132802134325257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108714330841510402845767009 81535748131132802134325257)
  ·
    refine ⟨61151811098349601600743943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81535748131132802134325257 61151811098349601600743943)
    ·
      refine ⟨91727716647524402401115915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61151811098349601600743943 91727716647524402401115915)
      ·
        refine ⟨137591574971286603601673873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91727716647524402401115915 137591574971286603601673873)
        ·
          refine ⟨103193681228464952701255405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137591574971286603601673873 103193681228464952701255405)
          ·
            refine ⟨38697630460674357262970777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103193681228464952701255405 38697630460674357262970777)
            ·
              refine ⟨29023222845505767947228083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38697630460674357262970777 29023222845505767947228083)
              ·
                refine ⟨43534834268258651920842125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29023222845505767947228083 43534834268258651920842125)
                ·
                  refine ⟨16325562850596994470315797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43534834268258651920842125 16325562850596994470315797)
                  ·
                    refine ⟨765260758621734115796053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16325562850596994470315797 765260758621734115796053)
                    ·
                      rfl

theorem cell23_4471020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_4471020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471020 prefixEnd_4471020 := by exact prefixLift 4471020
  have htrace : WordTrace (prefixWord ++ tailWord_4471020) baseStart_4471020 baseEnd_4471020 := by
    simpa [prefixWord, tailWord_4471020, baseEnd_4471020] using wordTrace_append hprefix tailTrace_4471020
  have hstable : (prefixWord ++ tailWord_4471020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471020).length < 2 ^ (prefixWord ++ tailWord_4471020).sum := by decide
  have hdescent : baseEnd_4471020 < baseStart_4471020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471027 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 4]
def baseStart_4471027 : Nat := 118140960795 + 4471027 * 2 ^ 59
def prefixEnd_4471027 : Nat := 4983230072969 + 3 ^ 40 * 4471027 * 2
def baseEnd_4471027 : Nat := 2295785870229783820000627

theorem tailTrace_4471027 : CollatzResearch.WordTrace tailWord_4471027 prefixEnd_4471027 2295785870229783820000627 := by
  unfold tailWord_4471027
  simp only [CollatzResearch.WordTrace]
  refine ⟨163071751573240244464155335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108714501048826829642770223 163071751573240244464155335)
  ·
    refine ⟨244607627359860366696233003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163071751573240244464155335 244607627359860366696233003)
    ·
      refine ⟨366911441039790550044349505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244607627359860366696233003 366911441039790550044349505)
      ·
        refine ⟨275183580779842912533262129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 366911441039790550044349505 275183580779842912533262129)
        ·
          refine ⟨206387685584882184399946597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275183580779842912533262129 206387685584882184399946597)
          ·
            refine ⟨38697691047165409574989987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206387685584882184399946597 38697691047165409574989987)
            ·
              refine ⟨58046536570748114362484981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38697691047165409574989987 58046536570748114362484981)
              ·
                refine ⟨5441862803507635721482967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58046536570748114362484981 5441862803507635721482967)
                ·
                  refine ⟨8162794205261453582224451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441862803507635721482967 8162794205261453582224451)
                  ·
                    refine ⟨12244191307892180373336677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8162794205261453582224451 12244191307892180373336677)
                    ·
                      refine ⟨2295785870229783820000627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12244191307892180373336677 2295785870229783820000627)
                      ·
                        rfl

theorem cell23_4471027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_4471027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471027 prefixEnd_4471027 := by exact prefixLift 4471027
  have htrace : WordTrace (prefixWord ++ tailWord_4471027) baseStart_4471027 baseEnd_4471027 := by
    simpa [prefixWord, tailWord_4471027, baseEnd_4471027] using wordTrace_append hprefix tailTrace_4471027
  have hstable : (prefixWord ++ tailWord_4471027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471027).length < 2 ^ (prefixWord ++ tailWord_4471027).sum := by decide
  have hdescent : baseEnd_4471027 < baseStart_4471027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471040 : List Nat := [2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6]
def baseStart_4471040 : Nat := 118140960795 + 4471040 * 2 ^ 59
def prefixEnd_4471040 : Nat := 4983230072969 + 3 ^ 40 * 4471040 * 2
def baseEnd_4471040 : Nat := 2295792545478292269138067

theorem tailTrace_4471040 : CollatzResearch.WordTrace tailWord_4471040 prefixEnd_4471040 2295792545478292269138067 := by
  unfold tailWord_4471040
  simp only [CollatzResearch.WordTrace]
  refine ⟨81536112861096573842189287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108714817148128765122919049 81536112861096573842189287)
  ·
    refine ⟨122304169291644860763283931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81536112861096573842189287 122304169291644860763283931)
    ·
      refine ⟨183456253937467291144925897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122304169291644860763283931 183456253937467291144925897)
      ·
        refine ⟨137592190453100468358694423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183456253937467291144925897 137592190453100468358694423)
        ·
          refine ⟨206388285679650702538041635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137592190453100468358694423 206388285679650702538041635)
          ·
            refine ⟨309582428519476053807062453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206388285679650702538041635 309582428519476053807062453)
            ·
              refine ⟨29023352673700880044412105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 309582428519476053807062453 29023352673700880044412105)
              ·
                refine ⟨21767514505275660033309079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29023352673700880044412105 21767514505275660033309079)
                ·
                  refine ⟨32651271757913490049963619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21767514505275660033309079 32651271757913490049963619)
                  ·
                    refine ⟨48976907636870235074945429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32651271757913490049963619 48976907636870235074945429)
                    ·
                      refine ⟨2295792545478292269138067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48976907636870235074945429 2295792545478292269138067)
                      ·
                        rfl

theorem cell23_4471040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_4471040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471040 prefixEnd_4471040 := by exact prefixLift 4471040
  have htrace : WordTrace (prefixWord ++ tailWord_4471040) baseStart_4471040 baseEnd_4471040 := by
    simpa [prefixWord, tailWord_4471040, baseEnd_4471040] using wordTrace_append hprefix tailTrace_4471040
  have hstable : (prefixWord ++ tailWord_4471040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471040).length < 2 ^ (prefixWord ++ tailWord_4471040).sum := by decide
  have hdescent : baseEnd_4471040 < baseStart_4471040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471050 : List Nat := [3, 1, 2, 2, 1, 1, 3, 10]
def baseStart_4471050 : Nat := 118140960795 + 4471050 * 2 ^ 59
def prefixEnd_4471050 : Nat := 4983230072969 + 3 ^ 40 * 4471050 * 2
def baseEnd_4471050 : Nat := 85029543714253230741223

theorem tailTrace_4471050 : CollatzResearch.WordTrace tailWord_4471050 prefixEnd_4471050 85029543714253230741223 := by
  unfold tailWord_4471050
  simp only [CollatzResearch.WordTrace]
  refine ⟨40768147613039229848060651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108715060301437946261495069 40768147613039229848060651)
  ·
    refine ⟨61152221419558844772090977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40768147613039229848060651 61152221419558844772090977)
    ·
      refine ⟨45864166064669133579068233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61152221419558844772090977 45864166064669133579068233)
      ·
        refine ⟨34398124548501850184301175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45864166064669133579068233 34398124548501850184301175)
        ·
          refine ⟨51597186822752775276451763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34398124548501850184301175 51597186822752775276451763)
          ·
            refine ⟨77395780234129162914677645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51597186822752775276451763 77395780234129162914677645)
            ·
              refine ⟨29023417587798436093004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77395780234129162914677645 29023417587798436093004117)
              ·
                refine ⟨85029543714253230741223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29023417587798436093004117 85029543714253230741223)
                ·
                  rfl

theorem cell23_4471050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 10].length) (baseStart_4471050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471050 prefixEnd_4471050 := by exact prefixLift 4471050
  have htrace : WordTrace (prefixWord ++ tailWord_4471050) baseStart_4471050 baseEnd_4471050 := by
    simpa [prefixWord, tailWord_4471050, baseEnd_4471050] using wordTrace_append hprefix tailTrace_4471050
  have hstable : (prefixWord ++ tailWord_4471050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471050).length < 2 ^ (prefixWord ++ tailWord_4471050).sum := by decide
  have hdescent : baseEnd_4471050 < baseStart_4471050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471054 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_4471054 : Nat := 118140960795 + 4471054 * 2 ^ 59
def prefixEnd_4471054 : Nat := 4983230072969 + 3 ^ 40 * 4471054 * 2
def baseEnd_4471054 : Nat := 765266578069151738121001

theorem tailTrace_4471054 : CollatzResearch.WordTrace tailWord_4471054 prefixEnd_4471054 765266578069151738121001 := by
  unfold tailWord_4471054
  simp only [CollatzResearch.WordTrace]
  refine ⟨20384092043017803509423527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108715157562761618716925477 20384092043017803509423527)
  ·
    refine ⟨30576138064526705264135291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20384092043017803509423527 30576138064526705264135291)
    ·
      refine ⟨45864207096790057896202937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30576138064526705264135291 45864207096790057896202937)
      ·
        refine ⟨34398155322592543422152203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45864207096790057896202937 34398155322592543422152203)
        ·
          refine ⟨51597232983888815133228305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34398155322592543422152203 51597232983888815133228305)
          ·
            refine ⟨38697924737916611349921229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51597232983888815133228305 38697924737916611349921229)
            ·
              refine ⟨14511721776718729256220461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38697924737916611349921229 14511721776718729256220461)
              ·
                refine ⟨5441895666269523471082673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14511721776718729256220461 5441895666269523471082673)
                ·
                  refine ⟨4081421749702142603312005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5441895666269523471082673 4081421749702142603312005)
                  ·
                    refine ⟨765266578069151738121001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081421749702142603312005 765266578069151738121001)
                    ·
                      rfl

theorem cell23_4471054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_4471054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471054 prefixEnd_4471054 := by exact prefixLift 4471054
  have htrace : WordTrace (prefixWord ++ tailWord_4471054) baseStart_4471054 baseEnd_4471054 := by
    simpa [prefixWord, tailWord_4471054, baseEnd_4471054] using wordTrace_append hprefix tailTrace_4471054
  have hstable : (prefixWord ++ tailWord_4471054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471054).length < 2 ^ (prefixWord ++ tailWord_4471054).sum := by decide
  have hdescent : baseEnd_4471054 < baseStart_4471054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471074 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_4471074 : Nat := 118140960795 + 4471074 * 2 ^ 59
def prefixEnd_4471074 : Nat := 4983230072969 + 3 ^ 40 * 4471074 * 2
def baseEnd_4471074 : Nat := 2295810003820545136112911

theorem tailTrace_4471074 : CollatzResearch.WordTrace tailWord_4471074 prefixEnd_4471074 2295810003820545136112911 := by
  unfold tailWord_4471074
  simp only [CollatzResearch.WordTrace]
  refine ⟨40768366451017492872779069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108715643869379980994077517 40768366451017492872779069)
  ·
    refine ⟨15288137419131559827292151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40768366451017492872779069 15288137419131559827292151)
    ·
      refine ⟨22932206128697339740938227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15288137419131559827292151 22932206128697339740938227)
      ·
        refine ⟨34398309193046009611407341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22932206128697339740938227 34398309193046009611407341)
        ·
          refine ⟨12899365947392253604277753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34398309193046009611407341 12899365947392253604277753)
          ·
            refine ⟨9674524460544190203208315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12899365947392253604277753 9674524460544190203208315)
            ·
              refine ⟨14511786690816285304812473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674524460544190203208315 14511786690816285304812473)
              ·
                refine ⟨10883840018112213978609355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14511786690816285304812473 10883840018112213978609355)
                ·
                  refine ⟨16325760027168320967914033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10883840018112213978609355 16325760027168320967914033)
                  ·
                    refine ⟨12244320020376240725935525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16325760027168320967914033 12244320020376240725935525)
                    ·
                      refine ⟨2295810003820545136112911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12244320020376240725935525 2295810003820545136112911)
                      ·
                        rfl

theorem cell23_4471074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_4471074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471074 prefixEnd_4471074 := by exact prefixLift 4471074
  have htrace : WordTrace (prefixWord ++ tailWord_4471074) baseStart_4471074 baseEnd_4471074 := by
    simpa [prefixWord, tailWord_4471074, baseEnd_4471074] using wordTrace_append hprefix tailTrace_4471074
  have hstable : (prefixWord ++ tailWord_4471074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471074).length < 2 ^ (prefixWord ++ tailWord_4471074).sum := by decide
  have hdescent : baseEnd_4471074 < baseStart_4471074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471097 : List Nat := [1, 2, 1, 6, 1, 1, 1, 1, 2, 7]
def baseStart_4471097 : Nat := 118140960795 + 4471097 * 2 ^ 59
def prefixEnd_4471097 : Nat := 4983230072969 + 3 ^ 40 * 4471097 * 2
def baseEnd_4471097 : Nat := 765273937958532848708435

theorem tailTrace_4471097 : CollatzResearch.WordTrace tailWord_4471097 prefixEnd_4471097 765273937958532848708435 := by
  unfold tailWord_4471097
  simp only [CollatzResearch.WordTrace]
  refine ⟨163074304682986646419203545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108716203121991097612802363 163074304682986646419203545)
  ·
    refine ⟨122305728512239984814402659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163074304682986646419203545 122305728512239984814402659)
    ·
      refine ⟨183458592768359977221603989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122305728512239984814402659 183458592768359977221603989)
      ·
        refine ⟨8599621536016873932262687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 183458592768359977221603989 8599621536016873932262687)
        ·
          refine ⟨12899432304025310898394031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8599621536016873932262687 12899432304025310898394031)
          ·
            refine ⟨19349148456037966347591047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12899432304025310898394031 19349148456037966347591047)
            ·
              refine ⟨29023722684056949521386571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19349148456037966347591047 29023722684056949521386571)
              ·
                refine ⟨43535584026085424282079857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29023722684056949521386571 43535584026085424282079857)
                ·
                  refine ⟨32651688019564068211559893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43535584026085424282079857 32651688019564068211559893)
                  ·
                    refine ⟨765273937958532848708435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32651688019564068211559893 765273937958532848708435)
                    ·
                      rfl

theorem cell23_4471097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 7].length) (baseStart_4471097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471097 prefixEnd_4471097 := by exact prefixLift 4471097
  have htrace : WordTrace (prefixWord ++ tailWord_4471097) baseStart_4471097 baseEnd_4471097 := by
    simpa [prefixWord, tailWord_4471097, baseEnd_4471097] using wordTrace_append hprefix tailTrace_4471097
  have hstable : (prefixWord ++ tailWord_4471097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471097).length < 2 ^ (prefixWord ++ tailWord_4471097).sum := by decide
  have hdescent : baseEnd_4471097 < baseStart_4471097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471132 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4471132 : Nat := 118140960795 + 4471132 * 2 ^ 59
def prefixEnd_4471132 : Nat := 4983230072969 + 3 ^ 40 * 4471132 * 2
def baseEnd_4471132 : Nat := 2295839785698505909187645

theorem tailTrace_4471132 : CollatzResearch.WordTrace tailWord_4471132 prefixEnd_4471132 2295839785698505909187645 := by
  unfold tailWord_4471132
  simp only [CollatzResearch.WordTrace]
  refine ⟨81537790618929923698363825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108717054158573231597818433 81537790618929923698363825)
  ·
    refine ⟨61153342964197442773772869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81537790618929923698363825 61153342964197442773772869)
    ·
      refine ⟨11466251805787020520082413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61153342964197442773772869 11466251805787020520082413)
      ·
        refine ⟨4299844427170132695030905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11466251805787020520082413 4299844427170132695030905)
        ·
          refine ⟨3224883320377599521273179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4299844427170132695030905 3224883320377599521273179)
          ·
            refine ⟨4837324980566399281909769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3224883320377599521273179 4837324980566399281909769)
            ·
              refine ⟨3627993735424799461432327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4837324980566399281909769 3627993735424799461432327)
              ·
                refine ⟨5441990603137199192148491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3627993735424799461432327 5441990603137199192148491)
                ·
                  refine ⟨8162985904705798788222737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441990603137199192148491 8162985904705798788222737)
                  ·
                    refine ⟨6122239428529349091167053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8162985904705798788222737 6122239428529349091167053)
                    ·
                      refine ⟨2295839785698505909187645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6122239428529349091167053 2295839785698505909187645)
                      ·
                        rfl

theorem cell23_4471132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4471132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471132 prefixEnd_4471132 := by exact prefixLift 4471132
  have htrace : WordTrace (prefixWord ++ tailWord_4471132) baseStart_4471132 baseEnd_4471132 := by
    simpa [prefixWord, tailWord_4471132, baseEnd_4471132] using wordTrace_append hprefix tailTrace_4471132
  have hstable : (prefixWord ++ tailWord_4471132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471132).length < 2 ^ (prefixWord ++ tailWord_4471132).sum := by decide
  have hdescent : baseEnd_4471132 < baseStart_4471132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471138 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4471138 : Nat := 118140960795 + 4471138 * 2 ^ 59
def prefixEnd_4471138 : Nat := 4983230072969 + 3 ^ 40 * 4471138 * 2
def baseEnd_4471138 : Nat := 2295842866582432885712617

theorem tailTrace_4471138 : CollatzResearch.WordTrace tailWord_4471138 prefixEnd_4471138 2295842866582432885712617 := by
  unfold tailWord_4471138
  simp only [CollatzResearch.WordTrace]
  refine ⟨40768950018959527605361517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108717200050558740280964045 40768950018959527605361517)
  ·
    refine ⟨15288356257109822852010569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40768950018959527605361517 15288356257109822852010569)
    ·
      refine ⟨11466267192832367139007927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15288356257109822852010569 11466267192832367139007927)
      ·
        refine ⟨17199400789248550708511891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11466267192832367139007927 17199400789248550708511891)
        ·
          refine ⟨25799101183872826062767837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17199400789248550708511891 25799101183872826062767837)
          ·
            refine ⟨9674662943952309773537939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25799101183872826062767837 9674662943952309773537939)
            ·
              refine ⟨14511994415928464660306909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9674662943952309773537939 14511994415928464660306909)
              ·
                refine ⟨5441997905973174247615091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14511994415928464660306909 5441997905973174247615091)
                ·
                  refine ⟨8162996858959761371422637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5441997905973174247615091 8162996858959761371422637)
                  ·
                    refine ⟨3061123822109910514283489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8162996858959761371422637 3061123822109910514283489)
                    ·
                      refine ⟨2295842866582432885712617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061123822109910514283489 2295842866582432885712617)
                      ·
                        rfl

theorem cell23_4471138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4471138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471138 prefixEnd_4471138 := by exact prefixLift 4471138
  have htrace : WordTrace (prefixWord ++ tailWord_4471138) baseStart_4471138 baseEnd_4471138 := by
    simpa [prefixWord, tailWord_4471138, baseEnd_4471138] using wordTrace_append hprefix tailTrace_4471138
  have hstable : (prefixWord ++ tailWord_4471138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471138).length < 2 ^ (prefixWord ++ tailWord_4471138).sum := by decide
  have hdescent : baseEnd_4471138 < baseStart_4471138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471151 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 2, 2, 2]
def baseStart_4471151 : Nat := 118140960795 + 4471151 * 2 ^ 59
def prefixEnd_4471151 : Nat := 4983230072969 + 3 ^ 40 * 4471151 * 2
def baseEnd_4471151 : Nat := 2295849541830941334850057

theorem tailTrace_4471151 : CollatzResearch.WordTrace tailWord_4471151 prefixEnd_4471151 2295849541830941334850057 := by
  unfold tailWord_4471151
  simp only [CollatzResearch.WordTrace]
  refine ⟨163076274224791013641669307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108717516149860675761112871 163076274224791013641669307)
  ·
    refine ⟨244614411337186520462503961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163076274224791013641669307 244614411337186520462503961)
    ·
      refine ⟨183460808502889890346877971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244614411337186520462503961 183460808502889890346877971)
      ·
        refine ⟨275191212754334835520316957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183460808502889890346877971 275191212754334835520316957)
        ·
          refine ⟨103196704782875563320118859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275191212754334835520316957 103196704782875563320118859)
          ·
            refine ⟨154795057174313344980178289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103196704782875563320118859 154795057174313344980178289)
            ·
              refine ⟨116096292880735008735133717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154795057174313344980178289 116096292880735008735133717)
              ·
                refine ⟨5442013728784453534459393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116096292880735008735133717 5442013728784453534459393)
                ·
                  refine ⟨4081510296588340150844545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5442013728784453534459393 4081510296588340150844545)
                  ·
                    refine ⟨3061132722441255113133409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081510296588340150844545 3061132722441255113133409)
                    ·
                      refine ⟨2295849541830941334850057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061132722441255113133409 2295849541830941334850057)
                      ·
                        rfl

theorem cell23_4471151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 2, 2].length) (baseStart_4471151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471151 prefixEnd_4471151 := by exact prefixLift 4471151
  have htrace : WordTrace (prefixWord ++ tailWord_4471151) baseStart_4471151 baseEnd_4471151 := by
    simpa [prefixWord, tailWord_4471151, baseEnd_4471151] using wordTrace_append hprefix tailTrace_4471151
  have hstable : (prefixWord ++ tailWord_4471151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471151).length < 2 ^ (prefixWord ++ tailWord_4471151).sum := by decide
  have hdescent : baseEnd_4471151 < baseStart_4471151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471224 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2]
def baseStart_4471224 : Nat := 118140960795 + 4471224 * 2 ^ 59
def prefixEnd_4471224 : Nat := 4983230072969 + 3 ^ 40 * 4471224 * 2
def baseEnd_4471224 : Nat := 2295887025918719549237221

theorem tailTrace_4471224 : CollatzResearch.WordTrace tailWord_4471224 prefixEnd_4471224 2295887025918719549237221 := by
  unfold tailWord_4471224
  simp only [CollatzResearch.WordTrace]
  refine ⟨81539468376763273554538363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108719291169017698072717817 81539468376763273554538363)
  ·
    refine ⟨122309202565144910331807545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81539468376763273554538363 122309202565144910331807545)
    ·
      refine ⟨91731901923858682748855659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122309202565144910331807545 91731901923858682748855659)
      ·
        refine ⟨137597852885788024123283489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91731901923858682748855659 137597852885788024123283489)
        ·
          refine ⟨103198389664341018092462617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137597852885788024123283489 103198389664341018092462617)
          ·
            refine ⟨77398792248255763569346963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103198389664341018092462617 77398792248255763569346963)
            ·
              refine ⟨116098188372383645354020445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77398792248255763569346963 116098188372383645354020445)
              ·
                refine ⟨43536820639643867007757667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116098188372383645354020445 43536820639643867007757667)
                ·
                  refine ⟨65305230959465800511636501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43536820639643867007757667 65305230959465800511636501)
                  ·
                    refine ⟨3061182701224959398982961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 65305230959465800511636501 3061182701224959398982961)
                    ·
                      refine ⟨2295887025918719549237221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061182701224959398982961 2295887025918719549237221)
                      ·
                        rfl

theorem cell23_4471224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 6, 2].length) (baseStart_4471224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471224 prefixEnd_4471224 := by exact prefixLift 4471224
  have htrace : WordTrace (prefixWord ++ tailWord_4471224) baseStart_4471224 baseEnd_4471224 := by
    simpa [prefixWord, tailWord_4471224, baseEnd_4471224] using wordTrace_append hprefix tailTrace_4471224
  have hstable : (prefixWord ++ tailWord_4471224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471224).length < 2 ^ (prefixWord ++ tailWord_4471224).sum := by decide
  have hdescent : baseEnd_4471224 < baseStart_4471224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471261 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4471261 : Nat := 118140960795 + 4471261 * 2 ^ 59
def prefixEnd_4471261 : Nat := 4983230072969 + 3 ^ 40 * 4471261 * 2
def baseEnd_4471261 : Nat := 2295906024702935904474551

theorem tailTrace_4471261 : CollatzResearch.WordTrace tailWord_4471261 prefixEnd_4471261 2295906024702935904474551 := by
  unfold tailWord_4471261
  simp only [CollatzResearch.WordTrace]
  refine ⟨163080286254392502428173637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108720190836261668285449091 163080286254392502428173637)
  ·
    refine ⟨30577553672698594205282557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163080286254392502428173637 30577553672698594205282557)
    ·
      refine ⟨11466582627261972826980959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30577553672698594205282557 11466582627261972826980959)
      ·
        refine ⟨17199873940892959240471439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11466582627261972826980959 17199873940892959240471439)
        ·
          refine ⟨25799810911339438860707159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17199873940892959240471439 25799810911339438860707159)
          ·
            refine ⟨38699716367009158291060739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25799810911339438860707159 38699716367009158291060739)
            ·
              refine ⟨58049574550513737436591109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38699716367009158291060739 58049574550513737436591109)
              ·
                refine ⟨10884295228221325769360833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58049574550513737436591109 10884295228221325769360833)
                ·
                  refine ⟨8163221421165994327020625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10884295228221325769360833 8163221421165994327020625)
                  ·
                    refine ⟨6122416065874495745265469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8163221421165994327020625 6122416065874495745265469)
                    ·
                      refine ⟨2295906024702935904474551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6122416065874495745265469 2295906024702935904474551)
                      ·
                        rfl

theorem cell23_4471261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4471261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471261 prefixEnd_4471261 := by exact prefixLift 4471261
  have htrace : WordTrace (prefixWord ++ tailWord_4471261) baseStart_4471261 baseEnd_4471261 := by
    simpa [prefixWord, tailWord_4471261, baseEnd_4471261] using wordTrace_append hprefix tailTrace_4471261
  have hstable : (prefixWord ++ tailWord_4471261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471261).length < 2 ^ (prefixWord ++ tailWord_4471261).sum := by decide
  have hdescent : baseEnd_4471261 < baseStart_4471261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471264 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 6]
def baseStart_4471264 : Nat := 118140960795 + 4471264 * 2 ^ 59
def prefixEnd_4471264 : Nat := 4983230072969 + 3 ^ 40 * 4471264 * 2
def baseEnd_4471264 : Nat := 255100840571655488081893

theorem tailTrace_4471264 : CollatzResearch.WordTrace tailWord_4471264 prefixEnd_4471264 255100840571655488081893 := by
  unfold tailWord_4471264
  simp only [CollatzResearch.WordTrace]
  refine ⟨81540197836690816970266423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108720263782254422627021897 81540197836690816970266423)
  ·
    refine ⟨122310296755036225455399635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81540197836690816970266423 122310296755036225455399635)
    ·
      refine ⟨183465445132554338183099453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122310296755036225455399635 183465445132554338183099453)
      ·
        refine ⟨68799541924707876818662295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183465445132554338183099453 68799541924707876818662295)
        ·
          refine ⟨103199312887061815227993443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68799541924707876818662295 103199312887061815227993443)
          ·
            refine ⟨154798969330592722841990165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103199312887061815227993443 154798969330592722841990165)
            ·
              refine ⟨7256201687371533883218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154798969330592722841990165 7256201687371533883218289)
              ·
                refine ⟨5442151265528650412413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7256201687371533883218289 5442151265528650412413717)
                ·
                  refine ⟨255100840571655488081893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5442151265528650412413717 255100840571655488081893)
                  ·
                    rfl

theorem cell23_4471264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 6].length) (baseStart_4471264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471264 prefixEnd_4471264 := by exact prefixLift 4471264
  have htrace : WordTrace (prefixWord ++ tailWord_4471264) baseStart_4471264 baseEnd_4471264 := by
    simpa [prefixWord, tailWord_4471264, baseEnd_4471264] using wordTrace_append hprefix tailTrace_4471264
  have hstable : (prefixWord ++ tailWord_4471264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471264).length < 2 ^ (prefixWord ++ tailWord_4471264).sum := by decide
  have hdescent : baseEnd_4471264 < baseStart_4471264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471287 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5]
def baseStart_4471287 : Nat := 118140960795 + 4471287 * 2 ^ 59
def prefixEnd_4471287 : Nat := 4983230072969 + 3 ^ 40 * 4471287 * 2
def baseEnd_4471287 : Nat := 2295919375199952802749431

theorem tailTrace_4471287 : CollatzResearch.WordTrace tailWord_4471287 prefixEnd_4471287 2295919375199952802749431 := by
  unfold tailWord_4471287
  simp only [CollatzResearch.WordTrace]
  refine ⟨163081234552298308868620115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108720823034865539245746743 163081234552298308868620115)
  ·
    refine ⟨244621851828447463302930173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163081234552298308868620115 244621851828447463302930173)
    ·
      refine ⟨91733194435667798738598815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244621851828447463302930173 91733194435667798738598815)
      ·
        refine ⟨137599791653501698107898223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91733194435667798738598815 137599791653501698107898223)
        ·
          refine ⟨206399687480252547161847335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137599791653501698107898223 206399687480252547161847335)
          ·
            refine ⟨309599531220378820742771003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206399687480252547161847335 309599531220378820742771003)
            ·
              refine ⟨464399296830568231114156505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309599531220378820742771003 464399296830568231114156505)
              ·
                refine ⟨348299472622926173335617379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 464399296830568231114156505 348299472622926173335617379)
                ·
                  refine ⟨522449208934389260003426069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 348299472622926173335617379 522449208934389260003426069)
                  ·
                    refine ⟨24489806668799496562660597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 522449208934389260003426069 24489806668799496562660597)
                    ·
                      refine ⟨2295919375199952802749431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24489806668799496562660597 2295919375199952802749431)
                      ·
                        rfl

theorem cell23_4471287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_4471287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471287 prefixEnd_4471287 := by exact prefixLift 4471287
  have htrace : WordTrace (prefixWord ++ tailWord_4471287) baseStart_4471287 baseEnd_4471287 := by
    simpa [prefixWord, tailWord_4471287, baseEnd_4471287] using wordTrace_append hprefix tailTrace_4471287
  have hstable : (prefixWord ++ tailWord_4471287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471287).length < 2 ^ (prefixWord ++ tailWord_4471287).sum := by decide
  have hdescent : baseEnd_4471287 < baseStart_4471287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471325 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_4471325 : Nat := 118140960795 + 4471325 * 2 ^ 59
def prefixEnd_4471325 : Nat := 4983230072969 + 3 ^ 40 * 4471325 * 2
def baseEnd_4471325 : Nat := 2295938887464823654074257

theorem tailTrace_4471325 : CollatzResearch.WordTrace tailWord_4471325 prefixEnd_4471325 2295938887464823654074257 := by
  unfold tailWord_4471325
  simp only [CollatzResearch.WordTrace]
  refine ⟨163082620526160641358503429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108721747017440427572335619 163082620526160641358503429)
  ·
    refine ⟨30577991348655120254719393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163082620526160641358503429 30577991348655120254719393)
    ·
      refine ⟨22933493511491340191039545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30577991348655120254719393 22933493511491340191039545)
      ·
        refine ⟨17200120133618505143279659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22933493511491340191039545 17200120133618505143279659)
        ·
          refine ⟨25800180200427757714919489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200120133618505143279659 25800180200427757714919489)
          ·
            refine ⟨19350135150320818286189617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25800180200427757714919489 19350135150320818286189617)
            ·
              refine ⟨14512601362740613714642213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19350135150320818286189617 14512601362740613714642213)
              ·
                refine ⟨2721112755513865071495415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14512601362740613714642213 2721112755513865071495415)
                ·
                  refine ⟨4081669133270797607243123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721112755513865071495415 4081669133270797607243123)
                  ·
                    refine ⟨6122503699906196410864685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4081669133270797607243123 6122503699906196410864685)
                    ·
                      refine ⟨2295938887464823654074257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6122503699906196410864685 2295938887464823654074257)
                      ·
                        rfl

theorem cell23_4471325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_4471325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471325 prefixEnd_4471325 := by exact prefixLift 4471325
  have htrace : WordTrace (prefixWord ++ tailWord_4471325) baseStart_4471325 baseEnd_4471325 := by
    simpa [prefixWord, tailWord_4471325, baseEnd_4471325] using wordTrace_append hprefix tailTrace_4471325
  have hstable : (prefixWord ++ tailWord_4471325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471325).length < 2 ^ (prefixWord ++ tailWord_4471325).sum := by decide
  have hdescent : baseEnd_4471325 < baseStart_4471325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471354 : List Nat := [3, 1, 1, 1, 3, 4, 1, 9]
def baseStart_4471354 : Nat := 118140960795 + 4471354 * 2 ^ 59
def prefixEnd_4471354 : Nat := 4983230072969 + 3 ^ 40 * 4471354 * 2
def baseEnd_4471354 : Nat := 85035325126066816318949

theorem tailTrace_4471354 : CollatzResearch.WordTrace tailWord_4471354 prefixEnd_4471354 85035325126066816318949 := by
  unfold tailWord_4471354
  simp only [CollatzResearch.WordTrace]
  refine ⟨40770919560763894827827279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108722452162037052874206077 40770919560763894827827279)
  ·
    refine ⟨61156379341145842241740919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40770919560763894827827279 61156379341145842241740919)
    ·
      refine ⟨91734569011718763362611379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61156379341145842241740919 91734569011718763362611379)
      ·
        refine ⟨137601853517578145043917069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91734569011718763362611379 137601853517578145043917069)
        ·
          refine ⟨51600695069091804391468901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137601853517578145043917069 51600695069091804391468901)
          ·
            refine ⟨9675130325454713323400419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51600695069091804391468901 9675130325454713323400419)
            ·
              refine ⟨14512695488182069985100629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675130325454713323400419 14512695488182069985100629)
              ·
                refine ⟨85035325126066816318949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14512695488182069985100629 85035325126066816318949)
                ·
                  rfl

theorem cell23_4471354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 9].length) (baseStart_4471354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471354 prefixEnd_4471354 := by exact prefixLift 4471354
  have htrace : WordTrace (prefixWord ++ tailWord_4471354) baseStart_4471354 baseEnd_4471354 := by
    simpa [prefixWord, tailWord_4471354, baseEnd_4471354] using wordTrace_append hprefix tailTrace_4471354
  have hstable : (prefixWord ++ tailWord_4471354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471354).length < 2 ^ (prefixWord ++ tailWord_4471354).sum := by decide
  have hdescent : baseEnd_4471354 < baseStart_4471354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471438 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4471438 : Nat := 118140960795 + 4471438 * 2 ^ 59
def prefixEnd_4471438 : Nat := 4983230072969 + 3 ^ 40 * 4471438 * 2
def baseEnd_4471438 : Nat := 2295996910778781711961237

theorem tailTrace_4471438 : CollatzResearch.WordTrace tailWord_4471438 prefixEnd_4471438 2295996910778781711961237 := by
  unfold tailWord_4471438
  simp only [CollatzResearch.WordTrace]
  refine ⟨20385842746843907707170871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108724494649834174438244645 20385842746843907707170871)
  ·
    refine ⟨30578764120265861560756307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20385842746843907707170871 30578764120265861560756307)
    ·
      refine ⟨45868146180398792341134461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30578764120265861560756307 45868146180398792341134461)
      ·
        refine ⟨17200554817649547127925423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45868146180398792341134461 17200554817649547127925423)
        ·
          refine ⟨25800832226474320691888135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17200554817649547127925423 25800832226474320691888135)
          ·
            refine ⟨38701248339711481037832203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25800832226474320691888135 38701248339711481037832203)
            ·
              refine ⟨58051872509567221556748305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38701248339711481037832203 58051872509567221556748305)
              ·
                refine ⟨43538904382175416167561229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58051872509567221556748305 43538904382175416167561229)
                ·
                  refine ⟨16327089143315781062835461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43538904382175416167561229 16327089143315781062835461)
                  ·
                    refine ⟨3061329214371708949281649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16327089143315781062835461 3061329214371708949281649)
                    ·
                      refine ⟨2295996910778781711961237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061329214371708949281649 2295996910778781711961237)
                      ·
                        rfl

theorem cell23_4471438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4471438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471438 prefixEnd_4471438 := by exact prefixLift 4471438
  have htrace : WordTrace (prefixWord ++ tailWord_4471438) baseStart_4471438 baseEnd_4471438 := by
    simpa [prefixWord, tailWord_4471438, baseEnd_4471438] using wordTrace_append hprefix tailTrace_4471438
  have hstable : (prefixWord ++ tailWord_4471438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471438).length < 2 ^ (prefixWord ++ tailWord_4471438).sum := by decide
  have hdescent : baseEnd_4471438 < baseStart_4471438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471489 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4471489 : Nat := 118140960795 + 4471489 * 2 ^ 59
def prefixEnd_4471489 : Nat := 4983230072969 + 3 ^ 40 * 4471489 * 2
def baseEnd_4471489 : Nat := 2296023098292161012423503

theorem tailTrace_4471489 : CollatzResearch.WordTrace tailWord_4471489 prefixEnd_4471489 2296023098292161012423503 := by
  unfold tailWord_4471489
  simp only [CollatzResearch.WordTrace]
  refine ⟨163088602097566497367473521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108725734731710998244982347 163088602097566497367473521)
  ·
    refine ⟨122316451573174873025605141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163088602097566497367473521 122316451573174873025605141)
    ·
      refine ⟨5733583667492572173075241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122316451573174873025605141 5733583667492572173075241)
      ·
        refine ⟨4300187750619429129806431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5733583667492572173075241 4300187750619429129806431)
        ·
          refine ⟨6450281625929143694709647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300187750619429129806431 6450281625929143694709647)
          ·
            refine ⟨9675422438893715542064471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450281625929143694709647 9675422438893715542064471)
            ·
              refine ⟨14513133658340573313096707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675422438893715542064471 14513133658340573313096707)
              ·
                refine ⟨21769700487510859969645061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14513133658340573313096707 21769700487510859969645061)
                ·
                  refine ⟨4081818841408286244308449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21769700487510859969645061 4081818841408286244308449)
                  ·
                    refine ⟨3061364131056214683231337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081818841408286244308449 3061364131056214683231337)
                    ·
                      refine ⟨2296023098292161012423503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061364131056214683231337 2296023098292161012423503)
                      ·
                        rfl

theorem cell23_4471489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4471489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471489 prefixEnd_4471489 := by exact prefixLift 4471489
  have htrace : WordTrace (prefixWord ++ tailWord_4471489) baseStart_4471489 baseEnd_4471489 := by
    simpa [prefixWord, tailWord_4471489, baseEnd_4471489] using wordTrace_append hprefix tailTrace_4471489
  have hstable : (prefixWord ++ tailWord_4471489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471489).length < 2 ^ (prefixWord ++ tailWord_4471489).sum := by decide
  have hdescent : baseEnd_4471489 < baseStart_4471489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471511 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4]
def baseStart_4471511 : Nat := 118140960795 + 4471511 * 2 ^ 59
def prefixEnd_4471511 : Nat := 4983230072969 + 3 ^ 40 * 4471511 * 2
def baseEnd_4471511 : Nat := 2296034394866559926348401

theorem tailTrace_4471511 : CollatzResearch.WordTrace tailWord_4471511 prefixEnd_4471511 2296034394866559926348401 := by
  unfold tailWord_4471511
  simp only [CollatzResearch.WordTrace]
  refine ⟨163089404503486795124774387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108726269668991196749849591 163089404503486795124774387)
  ·
    refine ⟨244634106755230192687161581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163089404503486795124774387 244634106755230192687161581)
    ·
      refine ⟨91737790033211322257685593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244634106755230192687161581 91737790033211322257685593)
      ·
        refine ⟨68803342524908491693264195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91737790033211322257685593 68803342524908491693264195)
        ·
          refine ⟨103205013787362737539896293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68803342524908491693264195 103205013787362737539896293)
          ·
            refine ⟨19350940085130513288730555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103205013787362737539896293 19350940085130513288730555)
            ·
              refine ⟨29026410127695769933095833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19350940085130513288730555 29026410127695769933095833)
              ·
                refine ⟨21769807595771827449821875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29026410127695769933095833 21769807595771827449821875)
                ·
                  refine ⟨32654711393657741174732813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21769807595771827449821875 32654711393657741174732813)
                  ·
                    refine ⟨12245516772621652940524805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32654711393657741174732813 12245516772621652940524805)
                    ·
                      refine ⟨2296034394866559926348401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12245516772621652940524805 2296034394866559926348401)
                      ·
                        rfl

theorem cell23_4471511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 4].length) (baseStart_4471511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471511 prefixEnd_4471511 := by exact prefixLift 4471511
  have htrace : WordTrace (prefixWord ++ tailWord_4471511) baseStart_4471511 baseEnd_4471511 := by
    simpa [prefixWord, tailWord_4471511, baseEnd_4471511] using wordTrace_append hprefix tailTrace_4471511
  have hstable : (prefixWord ++ tailWord_4471511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471511).length < 2 ^ (prefixWord ++ tailWord_4471511).sum := by decide
  have hdescent : baseEnd_4471511 < baseStart_4471511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471548 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_4471548 : Nat := 118140960795 + 4471548 * 2 ^ 59
def prefixEnd_4471548 : Nat := 4983230072969 + 3 ^ 40 * 4471548 * 2
def baseEnd_4471548 : Nat := 2296053393650776281585731

theorem tailTrace_4471548 : CollatzResearch.WordTrace tailWord_4471548 prefixEnd_4471548 2296053393650776281585731 := by
  unfold tailWord_4471548
  simp only [CollatzResearch.WordTrace]
  refine ⟨81545377002176375221935649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108727169336235166962580865 81545377002176375221935649)
  ·
    refine ⟨61159032751632281416451737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81545377002176375221935649 61159032751632281416451737)
    ·
      refine ⟨45869274563724211062338803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61159032751632281416451737 45869274563724211062338803)
      ·
        refine ⟨68803911845586316593508205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45869274563724211062338803 68803911845586316593508205)
        ·
          refine ⟨25801466942094868722565577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68803911845586316593508205 25801466942094868722565577)
          ·
            refine ⟨19351100206571151541924183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25801466942094868722565577 19351100206571151541924183)
            ·
              refine ⟨29026650309856727312886275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19351100206571151541924183 29026650309856727312886275)
              ·
                refine ⟨43539975464785090969329413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29026650309856727312886275 43539975464785090969329413)
                ·
                  refine ⟨8163745399647204556749265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43539975464785090969329413 8163745399647204556749265)
                  ·
                    refine ⟨6122809049735403417561949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8163745399647204556749265 6122809049735403417561949)
                    ·
                      refine ⟨2296053393650776281585731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6122809049735403417561949 2296053393650776281585731)
                      ·
                        rfl

theorem cell23_4471548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_4471548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471548 prefixEnd_4471548 := by exact prefixLift 4471548
  have htrace : WordTrace (prefixWord ++ tailWord_4471548) baseStart_4471548 baseEnd_4471548 := by
    simpa [prefixWord, tailWord_4471548, baseEnd_4471548] using wordTrace_append hprefix tailTrace_4471548
  have hstable : (prefixWord ++ tailWord_4471548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471548).length < 2 ^ (prefixWord ++ tailWord_4471548).sum := by decide
  have hdescent : baseEnd_4471548 < baseStart_4471548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471551 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 6]
def baseStart_4471551 : Nat := 118140960795 + 4471551 * 2 ^ 59
def prefixEnd_4471551 : Nat := 4983230072969 + 3 ^ 40 * 4471551 * 2
def baseEnd_4471551 : Nat := 255117214899193307760913

theorem tailTrace_4471551 : CollatzResearch.WordTrace tailWord_4471551 prefixEnd_4471551 255117214899193307760913 := by
  unfold tailWord_4471551
  simp only [CollatzResearch.WordTrace]
  refine ⟨163090863423341881956230507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108727242282227921304153671 163090863423341881956230507)
  ·
    refine ⟨244636295135012822934345761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163090863423341881956230507 244636295135012822934345761)
    ·
      refine ⟨183477221351259617200759321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244636295135012822934345761 183477221351259617200759321)
      ·
        refine ⟨137607916013444712900569491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183477221351259617200759321 137607916013444712900569491)
        ·
          refine ⟨206411874020167069350854237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137607916013444712900569491 206411874020167069350854237)
          ·
            refine ⟨77404452757562651006570339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206411874020167069350854237 77404452757562651006570339)
            ·
              refine ⟨116106679136343976509855509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77404452757562651006570339 116106679136343976509855509)
              ·
                refine ⟨5442500584516123898899477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 116106679136343976509855509 5442500584516123898899477)
                ·
                  refine ⟨255117214899193307760913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5442500584516123898899477 255117214899193307760913)
                  ·
                    rfl

theorem cell23_4471551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 6].length) (baseStart_4471551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471551 prefixEnd_4471551 := by exact prefixLift 4471551
  have htrace : WordTrace (prefixWord ++ tailWord_4471551) baseStart_4471551 baseEnd_4471551 := by
    simpa [prefixWord, tailWord_4471551, baseEnd_4471551] using wordTrace_append hprefix tailTrace_4471551
  have hstable : (prefixWord ++ tailWord_4471551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471551).length < 2 ^ (prefixWord ++ tailWord_4471551).sum := by decide
  have hdescent : baseEnd_4471551 < baseStart_4471551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471628 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 1, 6]
def baseStart_4471628 : Nat := 118140960795 + 4471628 * 2 ^ 59
def prefixEnd_4471628 : Nat := 4983230072969 + 3 ^ 40 * 4471628 * 2
def baseEnd_4471628 : Nat := 765364824034378656195121

theorem tailTrace_4471628 : CollatzResearch.WordTrace tailWord_4471628 prefixEnd_4471628 765364824034378656195121 := by
  unfold tailWord_4471628
  simp only [CollatzResearch.WordTrace]
  refine ⟨81546835922031462053391769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108729114562708616071189025 81546835922031462053391769)
  ·
    refine ⟨61160126941523596540043827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81546835922031462053391769 61160126941523596540043827)
    ·
      refine ⟨91740190412285394810065741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61160126941523596540043827 91740190412285394810065741)
      ·
        refine ⟨34402571404607023053774653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91740190412285394810065741 34402571404607023053774653)
        ·
          refine ⟨12900964276727633645165495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34402571404607023053774653 12900964276727633645165495)
          ·
            refine ⟨19351446415091450467748243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12900964276727633645165495 19351446415091450467748243)
            ·
              refine ⟨29027169622637175701622365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19351446415091450467748243 29027169622637175701622365)
              ·
                refine ⟨10885188608488940888108387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29027169622637175701622365 10885188608488940888108387)
                ·
                  refine ⟨16327782912733411332162581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10885188608488940888108387 16327782912733411332162581)
                  ·
                    refine ⟨765364824034378656195121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16327782912733411332162581 765364824034378656195121)
                    ·
                      rfl

theorem cell23_4471628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_4471628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471628 prefixEnd_4471628 := by exact prefixLift 4471628
  have htrace : WordTrace (prefixWord ++ tailWord_4471628) baseStart_4471628 baseEnd_4471628 := by
    simpa [prefixWord, tailWord_4471628, baseEnd_4471628] using wordTrace_append hprefix tailTrace_4471628
  have hstable : (prefixWord ++ tailWord_4471628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471628).length < 2 ^ (prefixWord ++ tailWord_4471628).sum := by decide
  have hdescent : baseEnd_4471628 < baseStart_4471628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471629 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 3]
def baseStart_4471629 : Nat := 118140960795 + 4471629 * 2 ^ 59
def prefixEnd_4471629 : Nat := 4983230072969 + 3 ^ 40 * 4471629 * 2
def baseEnd_4471629 : Nat := 2296094985583790464672859

theorem tailTrace_4471629 : CollatzResearch.WordTrace tailWord_4471629 prefixEnd_4471629 2296094985583790464672859 := by
  unfold tailWord_4471629
  simp only [CollatzResearch.WordTrace]
  refine ⟨163093708317059301277569941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108729138878039534185046627 163093708317059301277569941)
  ·
    refine ⟨7645017577362154747386091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163093708317059301277569941 7645017577362154747386091)
    ·
      refine ⟨11467526366043232121079137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645017577362154747386091 11467526366043232121079137)
      ·
        refine ⟨8600644774532424090809353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11467526366043232121079137 8600644774532424090809353)
        ·
          refine ⟨6450483580899318068107015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8600644774532424090809353 6450483580899318068107015)
          ·
            refine ⟨9675725371348977102160523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450483580899318068107015 9675725371348977102160523)
            ·
              refine ⟨14513588057023465653240785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675725371348977102160523 14513588057023465653240785)
              ·
                refine ⟨10885191042767599239930589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14513588057023465653240785 10885191042767599239930589)
                ·
                  refine ⟨4081946641037849714973971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10885191042767599239930589 4081946641037849714973971)
                  ·
                    refine ⟨6122919961556774572460957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4081946641037849714973971 6122919961556774572460957)
                    ·
                      refine ⟨2296094985583790464672859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6122919961556774572460957 2296094985583790464672859)
                      ·
                        rfl

theorem cell23_4471629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_4471629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471629 prefixEnd_4471629 := by exact prefixLift 4471629
  have htrace : WordTrace (prefixWord ++ tailWord_4471629) baseStart_4471629 baseEnd_4471629 := by
    simpa [prefixWord, tailWord_4471629, baseEnd_4471629] using wordTrace_append hprefix tailTrace_4471629
  have hstable : (prefixWord ++ tailWord_4471629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471629).length < 2 ^ (prefixWord ++ tailWord_4471629).sum := by decide
  have hdescent : baseEnd_4471629 < baseStart_4471629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471648 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4]
def baseStart_4471648 : Nat := 118140960795 + 4471648 * 2 ^ 59
def prefixEnd_4471648 : Nat := 4983230072969 + 3 ^ 40 * 4471648 * 2
def baseEnd_4471648 : Nat := 2296104741716225890335271

theorem tailTrace_4471648 : CollatzResearch.WordTrace tailWord_4471648 prefixEnd_4471648 2296104741716225890335271 := by
  unfold tailWord_4471648
  simp only [CollatzResearch.WordTrace]
  refine ⟨81547200651995233761255799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108729600869326978348341065 81547200651995233761255799)
  ·
    refine ⟨122320800977992850641883699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81547200651995233761255799 122320800977992850641883699)
    ·
      refine ⟨183481201466989275962825549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122320800977992850641883699 183481201466989275962825549)
      ·
        refine ⟨68805450550120978486059581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183481201466989275962825549 68805450550120978486059581)
        ·
          refine ⟨25802043956295366932272343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68805450550120978486059581 25802043956295366932272343)
          ·
            refine ⟨38703065934443050398408515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25802043956295366932272343 38703065934443050398408515)
            ·
              refine ⟨58054598901664575597612773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38703065934443050398408515 58054598901664575597612773)
              ·
                refine ⟨10885237294062107924552395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58054598901664575597612773 10885237294062107924552395)
                ·
                  refine ⟨16327855941093161886828593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10885237294062107924552395 16327855941093161886828593)
                  ·
                    refine ⟨12245891955819871415121445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16327855941093161886828593 12245891955819871415121445)
                    ·
                      refine ⟨2296104741716225890335271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12245891955819871415121445 2296104741716225890335271)
                      ·
                        rfl

theorem cell23_4471648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_4471648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471648 prefixEnd_4471648 := by exact prefixLift 4471648
  have htrace : WordTrace (prefixWord ++ tailWord_4471648) baseStart_4471648 baseEnd_4471648 := by
    simpa [prefixWord, tailWord_4471648, baseEnd_4471648] using wordTrace_append hprefix tailTrace_4471648
  have hstable : (prefixWord ++ tailWord_4471648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471648).length < 2 ^ (prefixWord ++ tailWord_4471648).sum := by decide
  have hdescent : baseEnd_4471648 < baseStart_4471648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471652 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_4471652 : Nat := 118140960795 + 4471652 * 2 ^ 59
def prefixEnd_4471652 : Nat := 4983230072969 + 3 ^ 40 * 4471652 * 2
def baseEnd_4471652 : Nat := 2296106795638843874685253

theorem tailTrace_4471652 : CollatzResearch.WordTrace tailWord_4471652 prefixEnd_4471652 2296106795638843874685253 := by
  unfold tailWord_4471652
  simp only [CollatzResearch.WordTrace]
  refine ⟨81547273597987988102828605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108729698130650650803771473 81547273597987988102828605)
  ·
    refine ⟨30580227599245495538560727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81547273597987988102828605 30580227599245495538560727)
    ·
      refine ⟨45870341398868243307841091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30580227599245495538560727 45870341398868243307841091)
      ·
        refine ⟨68805512098302364961761637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45870341398868243307841091 68805512098302364961761637)
        ·
          refine ⟨12901033518431693430330307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68805512098302364961761637 12901033518431693430330307)
          ·
            refine ⟨19351550277647540145495461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12901033518431693430330307 19351550277647540145495461)
            ·
              refine ⟨3628415677058913777280399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19351550277647540145495461 3628415677058913777280399)
              ·
                refine ⟨5442623515588370665920599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628415677058913777280399 5442623515588370665920599)
                ·
                  refine ⟨8163935273382555998880899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442623515588370665920599 8163935273382555998880899)
                  ·
                    refine ⟨12245902910073833998321349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8163935273382555998880899 12245902910073833998321349)
                    ·
                      refine ⟨2296106795638843874685253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12245902910073833998321349 2296106795638843874685253)
                      ·
                        rfl

theorem cell23_4471652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_4471652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471652 prefixEnd_4471652 := by exact prefixLift 4471652
  have htrace : WordTrace (prefixWord ++ tailWord_4471652) baseStart_4471652 baseEnd_4471652 := by
    simpa [prefixWord, tailWord_4471652, baseEnd_4471652] using wordTrace_append hprefix tailTrace_4471652
  have hstable : (prefixWord ++ tailWord_4471652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471652).length < 2 ^ (prefixWord ++ tailWord_4471652).sum := by decide
  have hdescent : baseEnd_4471652 < baseStart_4471652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471662 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4471662 : Nat := 118140960795 + 4471662 * 2 ^ 59
def prefixEnd_4471662 : Nat := 4983230072969 + 3 ^ 40 * 4471662 * 2
def baseEnd_4471662 : Nat := 765370643481796278520069

theorem tailTrace_4471662 : CollatzResearch.WordTrace tailWord_4471662 prefixEnd_4471662 765370643481796278520069 := by
  unfold tailWord_4471662
  simp only [CollatzResearch.WordTrace]
  refine ⟨20386863990742468489190155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108729941283959831942347493 20386863990742468489190155)
  ·
    refine ⟨30580295986113702733785233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20386863990742468489190155 30580295986113702733785233)
    ·
      refine ⟨22935221989585277050338925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30580295986113702733785233 22935221989585277050338925)
      ·
        refine ⟨8600708246094478893877097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22935221989585277050338925 8600708246094478893877097)
        ·
          refine ⟨6450531184570859170407823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8600708246094478893877097 6450531184570859170407823)
          ·
            refine ⟨9675796776856288755611735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6450531184570859170407823 9675796776856288755611735)
            ·
              refine ⟨14513695165284433133417603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9675796776856288755611735 14513695165284433133417603)
              ·
                refine ⟨21770542747926649700126405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14513695165284433133417603 21770542747926649700126405)
                ·
                  refine ⟨4081976765236246818773701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21770542747926649700126405 4081976765236246818773701)
                  ·
                    refine ⟨765370643481796278520069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4081976765236246818773701 765370643481796278520069)
                    ·
                      rfl

theorem cell23_4471662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4471662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471662 prefixEnd_4471662 := by exact prefixLift 4471662
  have htrace : WordTrace (prefixWord ++ tailWord_4471662) baseStart_4471662 baseEnd_4471662 := by
    simpa [prefixWord, tailWord_4471662, baseEnd_4471662] using wordTrace_append hprefix tailTrace_4471662
  have hstable : (prefixWord ++ tailWord_4471662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471662).length < 2 ^ (prefixWord ++ tailWord_4471662).sum := by decide
  have hdescent : baseEnd_4471662 < baseStart_4471662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471669 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4471669 : Nat := 118140960795 + 4471669 * 2 ^ 59
def prefixEnd_4471669 : Nat := 4983230072969 + 3 ^ 40 * 4471669 * 2
def baseEnd_4471669 : Nat := 2296115524809970308172675

theorem tailTrace_4471669 : CollatzResearch.WordTrace tailWord_4471669 prefixEnd_4471669 2296115524809970308172675 := by
  unfold tailWord_4471669
  simp only [CollatzResearch.WordTrace]
  refine ⟨163095167236914388109026061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108730111491276258739350707 163095167236914388109026061)
  ·
    refine ⟨61160687713842895540884773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163095167236914388109026061 61160687713842895540884773)
    ·
      refine ⟨11467628946345542913915895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61160687713842895540884773 11467628946345542913915895)
      ·
        refine ⟨17201443419518314370873843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11467628946345542913915895 17201443419518314370873843)
        ·
          refine ⟨25802165129277471556310765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17201443419518314370873843 25802165129277471556310765)
          ·
            refine ⟨9675811923479051833616537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25802165129277471556310765 9675811923479051833616537)
            ·
              refine ⟨7256858942609288875212403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9675811923479051833616537 7256858942609288875212403)
              ·
                refine ⟨10885288413913933312818605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7256858942609288875212403 10885288413913933312818605)
                ·
                  refine ⟨4081983155217724992306977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10885288413913933312818605 4081983155217724992306977)
                  ·
                    refine ⟨3061487366413293744230233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4081983155217724992306977 3061487366413293744230233)
                    ·
                      refine ⟨2296115524809970308172675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061487366413293744230233 2296115524809970308172675)
                      ·
                        rfl

theorem cell23_4471669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4471669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471669 prefixEnd_4471669 := by exact prefixLift 4471669
  have htrace : WordTrace (prefixWord ++ tailWord_4471669) baseStart_4471669 baseEnd_4471669 := by
    simpa [prefixWord, tailWord_4471669, baseEnd_4471669] using wordTrace_append hprefix tailTrace_4471669
  have hstable : (prefixWord ++ tailWord_4471669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471669).length < 2 ^ (prefixWord ++ tailWord_4471669).sum := by decide
  have hdescent : baseEnd_4471669 < baseStart_4471669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471671 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 1, 9]
def baseStart_4471671 : Nat := 118140960795 + 4471671 * 2 ^ 59
def prefixEnd_4471671 : Nat := 4983230072969 + 3 ^ 40 * 4471671 * 2
def baseEnd_4471671 : Nat := 765372183923759766782555

theorem tailTrace_4471671 : CollatzResearch.WordTrace tailWord_4471671 prefixEnd_4471671 765372183923759766782555 := by
  unfold tailWord_4471671
  simp only [CollatzResearch.WordTrace]
  refine ⟨163095240182907142450598867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108730160121938094967065911 163095240182907142450598867)
  ·
    refine ⟨244642860274360713675898301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163095240182907142450598867 244642860274360713675898301)
    ·
      refine ⟨91741072602885267628461863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244642860274360713675898301 91741072602885267628461863)
      ·
        refine ⟨137611608904327901442692795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91741072602885267628461863 137611608904327901442692795)
        ·
          refine ⟨206417413356491852164039193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137611608904327901442692795 206417413356491852164039193)
          ·
            refine ⟨154813060017368889123029395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206417413356491852164039193 154813060017368889123029395)
            ·
              refine ⟨232219590026053333684544093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154813060017368889123029395 232219590026053333684544093)
              ·
                refine ⟨87082346259770000131704035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232219590026053333684544093 87082346259770000131704035)
                ·
                  refine ⟨130623519389655000197556053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87082346259770000131704035 130623519389655000197556053)
                  ·
                    refine ⟨765372183923759766782555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 130623519389655000197556053 765372183923759766782555)
                    ·
                      rfl

theorem cell23_4471671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_4471671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471671 prefixEnd_4471671 := by exact prefixLift 4471671
  have htrace : WordTrace (prefixWord ++ tailWord_4471671) baseStart_4471671 baseEnd_4471671 := by
    simpa [prefixWord, tailWord_4471671, baseEnd_4471671] using wordTrace_append hprefix tailTrace_4471671
  have hstable : (prefixWord ++ tailWord_4471671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471671).length < 2 ^ (prefixWord ++ tailWord_4471671).sum := by decide
  have hdescent : baseEnd_4471671 < baseStart_4471671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471685 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_4471685 : Nat := 118140960795 + 4471685 * 2 ^ 59
def prefixEnd_4471685 : Nat := 4983230072969 + 3 ^ 40 * 4471685 * 2
def baseEnd_4471685 : Nat := 2296123740500442245572601

theorem tailTrace_4471685 : CollatzResearch.WordTrace tailWord_4471685 prefixEnd_4471685 2296123740500442245572601 := by
  unfold tailWord_4471685
  simp only [CollatzResearch.WordTrace]
  refine ⟨163095750804856422841608509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108730500536570948561072339 163095750804856422841608509)
  ·
    refine ⟨61160906551821158565603191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163095750804856422841608509 61160906551821158565603191)
    ·
      refine ⟨91741359827731737848404787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61160906551821158565603191 91741359827731737848404787)
      ·
        refine ⟨137612039741597606772607181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91741359827731737848404787 137612039741597606772607181)
        ·
          refine ⟨51604514903099102539727693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137612039741597606772607181 51604514903099102539727693)
          ·
            refine ⟨19351693088662163452397885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51604514903099102539727693 19351693088662163452397885)
            ·
              refine ⟨7256884908248311294649207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19351693088662163452397885 7256884908248311294649207)
              ·
                refine ⟨10885327362372466941973811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7256884908248311294649207 10885327362372466941973811)
                ·
                  refine ⟨16327991043558700412960717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10885327362372466941973811 16327991043558700412960717)
                  ·
                    refine ⟨6122996641334512654860269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16327991043558700412960717 6122996641334512654860269)
                    ·
                      refine ⟨2296123740500442245572601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6122996641334512654860269 2296123740500442245572601)
                      ·
                        rfl

theorem cell23_4471685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_4471685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471685 prefixEnd_4471685 := by exact prefixLift 4471685
  have htrace : WordTrace (prefixWord ++ tailWord_4471685) baseStart_4471685 baseEnd_4471685 := by
    simpa [prefixWord, tailWord_4471685, baseEnd_4471685] using wordTrace_append hprefix tailTrace_4471685
  have hstable : (prefixWord ++ tailWord_4471685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471685).length < 2 ^ (prefixWord ++ tailWord_4471685).sum := by decide
  have hdescent : baseEnd_4471685 < baseStart_4471685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471712 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2]
def baseStart_4471712 : Nat := 118140960795 + 4471712 * 2 ^ 59
def prefixEnd_4471712 : Nat := 4983230072969 + 3 ^ 40 * 4471712 * 2
def baseEnd_4471712 : Nat := 2296137604478113639934977

theorem tailTrace_4471712 : CollatzResearch.WordTrace tailWord_4471712 prefixEnd_4471712 2296137604478113639934977 := by
  unfold tailWord_4471712
  simp only [CollatzResearch.WordTrace]
  refine ⟨81548367787879303226420695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108731157050505737635227593 81548367787879303226420695)
  ·
    refine ⟨122322551681818954839631043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81548367787879303226420695 122322551681818954839631043)
    ·
      refine ⟨183483827522728432259446565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122322551681818954839631043 183483827522728432259446565)
      ·
        refine ⟨34403217660511581048646231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183483827522728432259446565 34403217660511581048646231)
        ·
          refine ⟨51604826490767371572969347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34403217660511581048646231 51604826490767371572969347)
          ·
            refine ⟨77407239736151057359454021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51604826490767371572969347 77407239736151057359454021)
            ·
              refine ⟨14513857450528323254897629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77407239736151057359454021 14513857450528323254897629)
              ·
                refine ⟨5442696543948121220586611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14513857450528323254897629 5442696543948121220586611)
                ·
                  refine ⟨8164044815922181830879917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442696543948121220586611 8164044815922181830879917)
                  ·
                    refine ⟨3061516805970818186579969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8164044815922181830879917 3061516805970818186579969)
                    ·
                      refine ⟨2296137604478113639934977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061516805970818186579969 2296137604478113639934977)
                      ·
                        rfl

theorem cell23_4471712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_4471712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471712 prefixEnd_4471712 := by exact prefixLift 4471712
  have htrace : WordTrace (prefixWord ++ tailWord_4471712) baseStart_4471712 baseEnd_4471712 := by
    simpa [prefixWord, tailWord_4471712, baseEnd_4471712] using wordTrace_append hprefix tailTrace_4471712
  have hstable : (prefixWord ++ tailWord_4471712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471712).length < 2 ^ (prefixWord ++ tailWord_4471712).sum := by decide
  have hdescent : baseEnd_4471712 < baseStart_4471712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471738 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_4471738 : Nat := 118140960795 + 4471738 * 2 ^ 59
def prefixEnd_4471738 : Nat := 4983230072969 + 3 ^ 40 * 4471738 * 2
def baseEnd_4471738 : Nat := 2296150954975130538209857

theorem tailTrace_4471738 : CollatzResearch.WordTrace tailWord_4471738 prefixEnd_4471738 2296150954975130538209857 := by
  unfold tailWord_4471738
  simp only [CollatzResearch.WordTrace]
  refine ⟨40774420968416103223321967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108731789249109608595525245 40774420968416103223321967)
  ·
    refine ⟨61161631452624154834982951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40774420968416103223321967 61161631452624154834982951)
    ·
      refine ⟨91742447178936232252474427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61161631452624154834982951 91742447178936232252474427)
      ·
        refine ⟨137613670768404348378711641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91742447178936232252474427 137613670768404348378711641)
        ·
          refine ⟨103210253076303261284033731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137613670768404348378711641 103210253076303261284033731)
          ·
            refine ⟨154815379614454891926050597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103210253076303261284033731 154815379614454891926050597)
            ·
              refine ⟨29027883677710292236134487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154815379614454891926050597 29027883677710292236134487)
              ·
                refine ⟨43541825516565438354201731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29027883677710292236134487 43541825516565438354201731)
                ·
                  refine ⟨65312738274848157531302597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43541825516565438354201731 65312738274848157531302597)
                  ·
                    refine ⟨12246138426534029537119237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65312738274848157531302597 12246138426534029537119237)
                    ·
                      refine ⟨2296150954975130538209857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12246138426534029537119237 2296150954975130538209857)
                      ·
                        rfl

theorem cell23_4471738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_4471738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471738 prefixEnd_4471738 := by exact prefixLift 4471738
  have htrace : WordTrace (prefixWord ++ tailWord_4471738) baseStart_4471738 baseEnd_4471738 := by
    simpa [prefixWord, tailWord_4471738, baseEnd_4471738] using wordTrace_append hprefix tailTrace_4471738
  have hstable : (prefixWord ++ tailWord_4471738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471738).length < 2 ^ (prefixWord ++ tailWord_4471738).sum := by decide
  have hdescent : baseEnd_4471738 < baseStart_4471738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471742 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2]
def baseStart_4471742 : Nat := 118140960795 + 4471742 * 2 ^ 59
def prefixEnd_4471742 : Nat := 4983230072969 + 3 ^ 40 * 4471742 * 2
def baseEnd_4471742 : Nat := 2296153008897748522559839

theorem tailTrace_4471742 : CollatzResearch.WordTrace tailWord_4471742 prefixEnd_4471742 2296153008897748522559839 := by
  unfold tailWord_4471742
  simp only [CollatzResearch.WordTrace]
  refine ⟨20387228720706240197054185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108731886510433281050955653 20387228720706240197054185)
  ·
    refine ⟨15290421540529680147790639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20387228720706240197054185 15290421540529680147790639)
    ·
      refine ⟨22935632310794520221685959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15290421540529680147790639 22935632310794520221685959)
      ·
        refine ⟨34403448466191780332528939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22935632310794520221685959 34403448466191780332528939)
        ·
          refine ⟨51605172699287670498793409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34403448466191780332528939 51605172699287670498793409)
          ·
            refine ⟨38703879524465752874095057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51605172699287670498793409 38703879524465752874095057)
            ·
              refine ⟨29027909643349314655571293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38703879524465752874095057 29027909643349314655571293)
              ·
                refine ⟨10885466116255992995839235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29027909643349314655571293 10885466116255992995839235)
                ·
                  refine ⟨16328199174383989493758853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10885466116255992995839235 16328199174383989493758853)
                  ·
                    refine ⟨3061537345196998030079785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16328199174383989493758853 3061537345196998030079785)
                    ·
                      refine ⟨2296153008897748522559839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061537345196998030079785 2296153008897748522559839)
                      ·
                        rfl

theorem cell23_4471742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_4471742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471742 prefixEnd_4471742 := by exact prefixLift 4471742
  have htrace : WordTrace (prefixWord ++ tailWord_4471742) baseStart_4471742 baseEnd_4471742 := by
    simpa [prefixWord, tailWord_4471742, baseEnd_4471742] using wordTrace_append hprefix tailTrace_4471742
  have hstable : (prefixWord ++ tailWord_4471742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471742).length < 2 ^ (prefixWord ++ tailWord_4471742).sum := by decide
  have hdescent : baseEnd_4471742 < baseStart_4471742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471815 : List Nat := [1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4471815 : Nat := 118140960795 + 4471815 * 2 ^ 59
def prefixEnd_4471815 : Nat := 4983230072969 + 3 ^ 40 * 4471815 * 2
def baseEnd_4471815 : Nat := 2296190492985526736947003

theorem tailTrace_4471815 : CollatzResearch.WordTrace tailWord_4471815 prefixEnd_4471815 2296190492985526736947003 := by
  unfold tailWord_4471815
  simp only [CollatzResearch.WordTrace]
  refine ⟨163100492294385455043840899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108733661529590303362560599 163100492294385455043840899)
  ·
    refine ⟨244650738441578182565761349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163100492294385455043840899 244650738441578182565761349)
    ·
      refine ⟨45872013457795909231080253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244650738441578182565761349 45872013457795909231080253)
      ·
        refine ⟨17202005046673465961655095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45872013457795909231080253 17202005046673465961655095)
        ·
          refine ⟨25803007570010198942482643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17202005046673465961655095 25803007570010198942482643)
          ·
            refine ⟨38704511355015298413723965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25803007570010198942482643 38704511355015298413723965)
            ·
              refine ⟨14514191758130736905146487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38704511355015298413723965 14514191758130736905146487)
              ·
                refine ⟨21771287637196105357719731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14514191758130736905146487 21771287637196105357719731)
                ·
                  refine ⟨32656931455794158036579597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21771287637196105357719731 32656931455794158036579597)
                  ·
                    refine ⟨12246349295922809263717349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32656931455794158036579597 12246349295922809263717349)
                    ·
                      refine ⟨2296190492985526736947003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12246349295922809263717349 2296190492985526736947003)
                      ·
                        rfl

theorem cell23_4471815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4471815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471815 prefixEnd_4471815 := by exact prefixLift 4471815
  have htrace : WordTrace (prefixWord ++ tailWord_4471815) baseStart_4471815 baseEnd_4471815 := by
    simpa [prefixWord, tailWord_4471815, baseEnd_4471815] using wordTrace_append hprefix tailTrace_4471815
  have hstable : (prefixWord ++ tailWord_4471815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471815).length < 2 ^ (prefixWord ++ tailWord_4471815).sum := by decide
  have hdescent : baseEnd_4471815 < baseStart_4471815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471832 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4471832 : Nat := 118140960795 + 4471832 * 2 ^ 59
def prefixEnd_4471832 : Nat := 4983230072969 + 3 ^ 40 * 4471832 * 2
def baseEnd_4471832 : Nat := 2296199222156653170434425

theorem tailTrace_4471832 : CollatzResearch.WordTrace tailWord_4471832 prefixEnd_4471832 2296199222156653170434425 := by
  unfold tailWord_4471832
  simp only [CollatzResearch.WordTrace]
  refine ⟨81550556167661933473604875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108734074890215911298139833 81550556167661933473604875)
  ·
    refine ⟨122325834251492900210407313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81550556167661933473604875 122325834251492900210407313)
    ·
      refine ⟨91744375688619675157805485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122325834251492900210407313 91744375688619675157805485)
      ·
        refine ⟨34404140883232378184177057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91744375688619675157805485 34404140883232378184177057)
        ·
          refine ⟨25803105662424283638132793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34404140883232378184177057 25803105662424283638132793)
          ·
            refine ⟨19352329246818212728599595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25803105662424283638132793 19352329246818212728599595)
            ·
              refine ⟨29028493870227319092899393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19352329246818212728599595 29028493870227319092899393)
              ·
                refine ⟨21771370402670489319674545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29028493870227319092899393 21771370402670489319674545)
                ·
                  refine ⟨16328527802002866989755909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21771370402670489319674545 16328527802002866989755909)
                  ·
                    refine ⟨3061598962875537560579233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16328527802002866989755909 3061598962875537560579233)
                    ·
                      refine ⟨2296199222156653170434425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061598962875537560579233 2296199222156653170434425)
                      ·
                        rfl

theorem cell23_4471832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4471832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471832 prefixEnd_4471832 := by exact prefixLift 4471832
  have htrace : WordTrace (prefixWord ++ tailWord_4471832) baseStart_4471832 baseEnd_4471832 := by
    simpa [prefixWord, tailWord_4471832, baseEnd_4471832] using wordTrace_append hprefix tailTrace_4471832
  have hstable : (prefixWord ++ tailWord_4471832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471832).length < 2 ^ (prefixWord ++ tailWord_4471832).sum := by decide
  have hdescent : baseEnd_4471832 < baseStart_4471832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471842 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 3, 4]
def baseStart_4471842 : Nat := 118140960795 + 4471842 * 2 ^ 59
def prefixEnd_4471842 : Nat := 4983230072969 + 3 ^ 40 * 4471842 * 2
def baseEnd_4471842 : Nat := 765401452321066043769793

theorem tailTrace_4471842 : CollatzResearch.WordTrace tailWord_4471842 prefixEnd_4471842 765401452321066043769793 := by
  unfold tailWord_4471842
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775369266321909663768445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108734318043525092436715853 40775369266321909663768445)
  ·
    refine ⟨15290763474870716123913167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40775369266321909663768445 15290763474870716123913167)
    ·
      refine ⟨22936145212306074185869751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15290763474870716123913167 22936145212306074185869751)
      ·
        refine ⟨34404217818459111278804627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22936145212306074185869751 34404217818459111278804627)
        ·
          refine ⟨51606326727688666918206941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34404217818459111278804627 51606326727688666918206941)
          ·
            refine ⟨19352372522883250094327603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51606326727688666918206941 19352372522883250094327603)
            ·
              refine ⟨29028558784324875141491405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19352372522883250094327603 29028558784324875141491405)
              ·
                refine ⟨10885709544121828178059277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29028558784324875141491405 10885709544121828178059277)
                ·
                  refine ⟨4082141079045685566772229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10885709544121828178059277 4082141079045685566772229)
                  ·
                    refine ⟨765401452321066043769793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4082141079045685566772229 765401452321066043769793)
                    ·
                      rfl

theorem cell23_4471842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_4471842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471842 prefixEnd_4471842 := by exact prefixLift 4471842
  have htrace : WordTrace (prefixWord ++ tailWord_4471842) baseStart_4471842 baseEnd_4471842 := by
    simpa [prefixWord, tailWord_4471842, baseEnd_4471842] using wordTrace_append hprefix tailTrace_4471842
  have hstable : (prefixWord ++ tailWord_4471842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471842).length < 2 ^ (prefixWord ++ tailWord_4471842).sum := by decide
  have hdescent : baseEnd_4471842 < baseStart_4471842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471882 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_4471882 : Nat := 118140960795 + 4471882 * 2 ^ 59
def prefixEnd_4471882 : Nat := 4983230072969 + 3 ^ 40 * 4471882 * 2
def baseEnd_4471882 : Nat := 2296224896189377974809195

theorem tailTrace_4471882 : CollatzResearch.WordTrace tailWord_4471882 prefixEnd_4471882 2296224896189377974809195 := by
  unfold tailWord_4471882
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775733996285681371632475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108735290656761816991019933 40775733996285681371632475)
  ·
    refine ⟨61163600994428522057448713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40775733996285681371632475 61163600994428522057448713)
    ·
      refine ⟨45872700745821391543086535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61163600994428522057448713 45872700745821391543086535)
      ·
        refine ⟨68809051118732087314629803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45872700745821391543086535 68809051118732087314629803)
        ·
          refine ⟨103213576678098130971944705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68809051118732087314629803 103213576678098130971944705)
          ·
            refine ⟨77410182508573598228958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103213576678098130971944705 77410182508573598228958529)
            ·
              refine ⟨58057636881430198671718897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77410182508573598228958529 58057636881430198671718897)
              ·
                refine ⟨43543227661072649003789173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58057636881430198671718897 43543227661072649003789173)
                ·
                  refine ⟨4082177593225560844105235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43543227661072649003789173 4082177593225560844105235)
                  ·
                    refine ⟨6123266389838341266157853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4082177593225560844105235 6123266389838341266157853)
                    ·
                      refine ⟨2296224896189377974809195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6123266389838341266157853 2296224896189377974809195)
                      ·
                        rfl

theorem cell23_4471882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_4471882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471882 prefixEnd_4471882 := by exact prefixLift 4471882
  have htrace : WordTrace (prefixWord ++ tailWord_4471882) baseStart_4471882 baseEnd_4471882 := by
    simpa [prefixWord, tailWord_4471882, baseEnd_4471882] using wordTrace_append hprefix tailTrace_4471882
  have hstable : (prefixWord ++ tailWord_4471882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471882).length < 2 ^ (prefixWord ++ tailWord_4471882).sum := by decide
  have hdescent : baseEnd_4471882 < baseStart_4471882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471906 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 6]
def baseStart_4471906 : Nat := 118140960795 + 4471906 * 2 ^ 59
def prefixEnd_4471906 : Nat := 4983230072969 + 3 ^ 40 * 4471906 * 2
def baseEnd_4471906 : Nat := 255137468858342875656565

theorem tailTrace_4471906 : CollatzResearch.WordTrace tailWord_4471906 prefixEnd_4471906 255137468858342875656565 := by
  unfold tailWord_4471906
  simp only [CollatzResearch.WordTrace]
  refine ⟨40775952834263944396350893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108735874224703851723602381 40775952834263944396350893)
  ·
    refine ⟨15290982312848979148631585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40775952834263944396350893 15290982312848979148631585)
    ·
      refine ⟨11468236734636734361473689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15290982312848979148631585 11468236734636734361473689)
      ·
        refine ⟨8601177550977550771105267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11468236734636734361473689 8601177550977550771105267)
        ·
          refine ⟨12901766326466326156657901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601177550977550771105267 12901766326466326156657901)
          ·
            refine ⟨4838162372424872308746713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12901766326466326156657901 4838162372424872308746713)
            ·
              refine ⟨3628621779318654231560035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838162372424872308746713 3628621779318654231560035)
              ·
                refine ⟨5442932668977981347340053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628621779318654231560035 5442932668977981347340053)
                ·
                  refine ⟨255137468858342875656565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5442932668977981347340053 255137468858342875656565)
                  ·
                    rfl

theorem cell23_4471906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_4471906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471906 prefixEnd_4471906 := by exact prefixLift 4471906
  have htrace : WordTrace (prefixWord ++ tailWord_4471906) baseStart_4471906 baseEnd_4471906 := by
    simpa [prefixWord, tailWord_4471906, baseEnd_4471906] using wordTrace_append hprefix tailTrace_4471906
  have hstable : (prefixWord ++ tailWord_4471906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471906).length < 2 ^ (prefixWord ++ tailWord_4471906).sum := by decide
  have hdescent : baseEnd_4471906 < baseStart_4471906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471922 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4471922 : Nat := 118140960795 + 4471922 * 2 ^ 59
def prefixEnd_4471922 : Nat := 4983230072969 + 3 ^ 40 * 4471922 * 2
def baseEnd_4471922 : Nat := 2296245435415557818309011

theorem tailTrace_4471922 : CollatzResearch.WordTrace tailWord_4471922 prefixEnd_4471922 2296245435415557818309011 := by
  unfold tailWord_4471922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40776098726249453079496505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108736263269998541545324013 40776098726249453079496505)
  ·
    refine ⟨30582074044687089809622379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40776098726249453079496505 30582074044687089809622379)
    ·
      refine ⟨45873111067030634714433569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30582074044687089809622379 45873111067030634714433569)
      ·
        refine ⟨34404833300272976035825177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45873111067030634714433569 34404833300272976035825177)
        ·
          refine ⟨25803624975204732026868883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34404833300272976035825177 25803624975204732026868883)
          ·
            refine ⟨38705437462807098040303325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25803624975204732026868883 38705437462807098040303325)
            ·
              refine ⟨14514539048552661765113747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38705437462807098040303325 14514539048552661765113747)
              ·
                refine ⟨21771808572828992647670621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14514539048552661765113747 21771808572828992647670621)
                ·
                  refine ⟨8164428214810872242876483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21771808572828992647670621 8164428214810872242876483)
                  ·
                    refine ⟨12246642322216308364314725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8164428214810872242876483 12246642322216308364314725)
                    ·
                      refine ⟨2296245435415557818309011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12246642322216308364314725 2296245435415557818309011)
                      ·
                        rfl

theorem cell23_4471922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4471922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471922 prefixEnd_4471922 := by exact prefixLift 4471922
  have htrace : WordTrace (prefixWord ++ tailWord_4471922) baseStart_4471922 baseEnd_4471922 := by
    simpa [prefixWord, tailWord_4471922, baseEnd_4471922] using wordTrace_append hprefix tailTrace_4471922
  have hstable : (prefixWord ++ tailWord_4471922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471922).length < 2 ^ (prefixWord ++ tailWord_4471922).sum := by decide
  have hdescent : baseEnd_4471922 < baseStart_4471922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471926 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4471926 : Nat := 118140960795 + 4471926 * 2 ^ 59
def prefixEnd_4471926 : Nat := 4983230072969 + 3 ^ 40 * 4471926 * 2
def baseEnd_4471926 : Nat := 2296247489338175802658993

theorem tailTrace_4471926 : CollatzResearch.WordTrace tailWord_4471926 prefixEnd_4471926 2296247489338175802658993 := by
  unfold tailWord_4471926
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194033799811457562570727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108736360531322214000754421 10194033799811457562570727)
  ·
    refine ⟨15291050699717186343856091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10194033799811457562570727 15291050699717186343856091)
    ·
      refine ⟨22936576049575779515784137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15291050699717186343856091 22936576049575779515784137)
      ·
        refine ⟨17202432037181834636838103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22936576049575779515784137 17202432037181834636838103)
        ·
          refine ⟨25803648055772751955257155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17202432037181834636838103 25803648055772751955257155)
          ·
            refine ⟨38705472083659127932885733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25803648055772751955257155 38705472083659127932885733)
            ·
              refine ⟨7257276015686086487416075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38705472083659127932885733 7257276015686086487416075)
              ·
                refine ⟨10885914023529129731124113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7257276015686086487416075 10885914023529129731124113)
                ·
                  refine ⟨8164435517646847298343085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10885914023529129731124113 8164435517646847298343085)
                  ·
                    refine ⟨3061663319117567736878657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8164435517646847298343085 3061663319117567736878657)
                    ·
                      refine ⟨2296247489338175802658993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061663319117567736878657 2296247489338175802658993)
                      ·
                        rfl

theorem cell23_4471926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4471926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471926 prefixEnd_4471926 := by exact prefixLift 4471926
  have htrace : WordTrace (prefixWord ++ tailWord_4471926) baseStart_4471926 baseEnd_4471926 := by
    simpa [prefixWord, tailWord_4471926, baseEnd_4471926] using wordTrace_append hprefix tailTrace_4471926
  have hstable : (prefixWord ++ tailWord_4471926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471926).length < 2 ^ (prefixWord ++ tailWord_4471926).sum := by decide
  have hdescent : baseEnd_4471926 < baseStart_4471926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471939 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 1, 1, 4]
def baseStart_4471939 : Nat := 118140960795 + 4471939 * 2 ^ 59
def prefixEnd_4471939 : Nat := 4983230072969 + 3 ^ 40 * 4471939 * 2
def baseEnd_4471939 : Nat := 2296254164586684251796433

theorem tailTrace_4471939 : CollatzResearch.WordTrace tailWord_4471939 prefixEnd_4471939 2296254164586684251796433 := by
  unfold tailWord_4471939
  simp only [CollatzResearch.WordTrace]
  refine ⟨163105014945936224221354871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108736676630624149480903247 163105014945936224221354871)
  ·
    refine ⟨244657522418904336332032307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163105014945936224221354871 244657522418904336332032307)
    ·
      refine ⟨366986283628356504498048461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244657522418904336332032307 366986283628356504498048461)
      ·
        refine ⟨137619856360633689186768173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 366986283628356504498048461 137619856360633689186768173)
        ·
          refine ⟨51607446135237633445038065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137619856360633689186768173 51607446135237633445038065)
          ·
            refine ⟨38705584601428225083778549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51607446135237633445038065 38705584601428225083778549)
            ·
              refine ⟨3628648556383896101604239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38705584601428225083778549 3628648556383896101604239)
              ·
                refine ⟨5442972834575844152406359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628648556383896101604239 5442972834575844152406359)
                ·
                  refine ⟨8164459251863766228609539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5442972834575844152406359 8164459251863766228609539)
                  ·
                    refine ⟨12246688877795649342914309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8164459251863766228609539 12246688877795649342914309)
                    ·
                      refine ⟨2296254164586684251796433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12246688877795649342914309 2296254164586684251796433)
                      ·
                        rfl

theorem cell23_4471939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 1, 1, 4].length) (baseStart_4471939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471939 prefixEnd_4471939 := by exact prefixLift 4471939
  have htrace : WordTrace (prefixWord ++ tailWord_4471939) baseStart_4471939 baseEnd_4471939 := by
    simpa [prefixWord, tailWord_4471939, baseEnd_4471939] using wordTrace_append hprefix tailTrace_4471939
  have hstable : (prefixWord ++ tailWord_4471939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471939).length < 2 ^ (prefixWord ++ tailWord_4471939).sum := by decide
  have hdescent : baseEnd_4471939 < baseStart_4471939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471950 : List Nat := [4, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4471950 : Nat := 118140960795 + 4471950 * 2 ^ 59
def prefixEnd_4471950 : Nat := 4983230072969 + 3 ^ 40 * 4471950 * 2
def baseEnd_4471950 : Nat := 2296259812873883708758883

theorem tailTrace_4471950 : CollatzResearch.WordTrace tailWord_4471950 prefixEnd_4471950 2296259812873883708758883 := by
  unfold tailWord_4471950
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388177018612046637500663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108736944099264248733336869 20388177018612046637500663)
  ·
    refine ⟨30582265527918069956250995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20388177018612046637500663 30582265527918069956250995)
    ·
      refine ⟨45873398291877104934376493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30582265527918069956250995 45873398291877104934376493)
      ·
        refine ⟨17202524359453914350391185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45873398291877104934376493 17202524359453914350391185)
        ·
          refine ⟨12901893269590435762793389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17202524359453914350391185 12901893269590435762793389)
          ·
            refine ⟨4838209976096413411047521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12901893269590435762793389 4838209976096413411047521)
            ·
              refine ⟨3628657482072310058285641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4838209976096413411047521 3628657482072310058285641)
              ·
                refine ⟨2721493111554232543714231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3628657482072310058285641 2721493111554232543714231)
                ·
                  refine ⟨4082239667331348815571347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721493111554232543714231 4082239667331348815571347)
                  ·
                    refine ⟨6123359500997023223357021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4082239667331348815571347 6123359500997023223357021)
                    ·
                      refine ⟨2296259812873883708758883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6123359500997023223357021 2296259812873883708758883)
                      ·
                        rfl

theorem cell23_4471950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4471950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471950 prefixEnd_4471950 := by exact prefixLift 4471950
  have htrace : WordTrace (prefixWord ++ tailWord_4471950) baseStart_4471950 baseEnd_4471950 := by
    simpa [prefixWord, tailWord_4471950, baseEnd_4471950] using wordTrace_append hprefix tailTrace_4471950
  have hstable : (prefixWord ++ tailWord_4471950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471950).length < 2 ^ (prefixWord ++ tailWord_4471950).sum := by decide
  have hdescent : baseEnd_4471950 < baseStart_4471950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471962 : List Nat := [3, 1, 1, 5, 1, 1, 3, 8]
def baseStart_4471962 : Nat := 118140960795 + 4471962 * 2 ^ 59
def prefixEnd_4471962 : Nat := 4983230072969 + 3 ^ 40 * 4471962 * 2
def baseEnd_4471962 : Nat := 85046887949693987474401

theorem tailTrace_4471962 : CollatzResearch.WordTrace tailWord_4471962 prefixEnd_4471962 85046887949693987474401 := by
  unfold tailWord_4471962
  simp only [CollatzResearch.WordTrace]
  refine ⟨40776463456213224787360535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108737235883235266099628093 40776463456213224787360535)
  ·
    refine ⟨61164695184319837181040803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40776463456213224787360535 61164695184319837181040803)
    ·
      refine ⟨91747042776479755771561205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61164695184319837181040803 91747042776479755771561205)
      ·
        refine ⟨8601285260294977103583863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91747042776479755771561205 8601285260294977103583863)
        ·
          refine ⟨12901927890442465655375795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601285260294977103583863 12901927890442465655375795)
          ·
            refine ⟨19352891835663698483063693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12901927890442465655375795 19352891835663698483063693)
            ·
              refine ⟨7257334438373886931148885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19352891835663698483063693 7257334438373886931148885)
              ·
                refine ⟨85046887949693987474401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7257334438373886931148885 85046887949693987474401)
                ·
                  rfl

theorem cell23_4471962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 8].length) (baseStart_4471962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471962 prefixEnd_4471962 := by exact prefixLift 4471962
  have htrace : WordTrace (prefixWord ++ tailWord_4471962) baseStart_4471962 baseEnd_4471962 := by
    simpa [prefixWord, tailWord_4471962, baseEnd_4471962] using wordTrace_append hprefix tailTrace_4471962
  have hstable : (prefixWord ++ tailWord_4471962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471962).length < 2 ^ (prefixWord ++ tailWord_4471962).sum := by decide
  have hdescent : baseEnd_4471962 < baseStart_4471962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471966 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4471966 : Nat := 118140960795 + 4471966 * 2 ^ 59
def prefixEnd_4471966 : Nat := 4983230072969 + 3 ^ 40 * 4471966 * 2
def baseEnd_4471966 : Nat := 765422676188118548719603

theorem tailTrace_4471966 : CollatzResearch.WordTrace tailWord_4471966 prefixEnd_4471966 765422676188118548719603 := by
  unfold tailWord_4471966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388249964604800979073469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108737333144558938555058501 20388249964604800979073469)
  ·
    refine ⟨7645593736726800367152551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20388249964604800979073469 7645593736726800367152551)
    ·
      refine ⟨11468390605090200550728827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7645593736726800367152551 11468390605090200550728827)
      ·
        refine ⟨17202585907635300826093241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11468390605090200550728827 17202585907635300826093241)
        ·
          refine ⟨12901939430726475619569931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17202585907635300826093241 12901939430726475619569931)
          ·
            refine ⟨19352909146089713429354897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12901939430726475619569931 19352909146089713429354897)
            ·
              refine ⟨14514681859567285072016173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19352909146089713429354897 14514681859567285072016173)
              ·
                refine ⟨5443005697337731902006065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14514681859567285072016173 5443005697337731902006065)
                ·
                  refine ⟨4082254273003298926504549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5443005697337731902006065 4082254273003298926504549)
                  ·
                    refine ⟨765422676188118548719603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4082254273003298926504549 765422676188118548719603)
                    ·
                      rfl

theorem cell23_4471966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4471966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471966 prefixEnd_4471966 := by exact prefixLift 4471966
  have htrace : WordTrace (prefixWord ++ tailWord_4471966) baseStart_4471966 baseEnd_4471966 := by
    simpa [prefixWord, tailWord_4471966, baseEnd_4471966] using wordTrace_append hprefix tailTrace_4471966
  have hstable : (prefixWord ++ tailWord_4471966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471966).length < 2 ^ (prefixWord ++ tailWord_4471966).sum := by decide
  have hdescent : baseEnd_4471966 < baseStart_4471966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4471995 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4]
def baseStart_4471995 : Nat := 118140960795 + 4471995 * 2 ^ 59
def prefixEnd_4471995 : Nat := 4983230072969 + 3 ^ 40 * 4471995 * 2
def baseEnd_4471995 : Nat := 2296282919503336032696175

theorem tailTrace_4471995 : CollatzResearch.WordTrace tailWord_4471995 prefixEnd_4471995 2296282919503336032696175 := by
  unfold tailWord_4471995
  simp only [CollatzResearch.WordTrace]
  refine ⟨163107057433733345785393439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108738038289155563856928959 163107057433733345785393439)
  ·
    refine ⟨244660586150600018678090159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163107057433733345785393439 244660586150600018678090159)
    ·
      refine ⟨366990879225900028017135239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244660586150600018678090159 366990879225900028017135239)
      ·
        refine ⟨550486318838850042025702859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366990879225900028017135239 550486318838850042025702859)
        ·
          refine ⟨825729478258275063038554289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550486318838850042025702859 825729478258275063038554289)
          ·
            refine ⟨619297108693706297278915717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 825729478258275063038554289 619297108693706297278915717)
            ·
              refine ⟨116118207880069930739796697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 619297108693706297278915717 116118207880069930739796697)
              ·
                refine ⟨87088655910052448054847523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116118207880069930739796697 87088655910052448054847523)
                ·
                  refine ⟨130632983865078672082271285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87088655910052448054847523 130632983865078672082271285)
                  ·
                    refine ⟨12246842237351125507712933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 130632983865078672082271285 12246842237351125507712933)
                    ·
                      refine ⟨2296282919503336032696175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12246842237351125507712933 2296282919503336032696175)
                      ·
                        rfl

theorem cell23_4471995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 1, 5, 4].length) (baseStart_4471995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4471995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4471995 prefixEnd_4471995 := by exact prefixLift 4471995
  have htrace : WordTrace (prefixWord ++ tailWord_4471995) baseStart_4471995 baseEnd_4471995 := by
    simpa [prefixWord, tailWord_4471995, baseEnd_4471995] using wordTrace_append hprefix tailTrace_4471995
  have hstable : (prefixWord ++ tailWord_4471995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4471995).length < 2 ^ (prefixWord ++ tailWord_4471995).sum := by decide
  have hdescent : baseEnd_4471995 < baseStart_4471995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4471995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472015 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5]
def baseStart_4472015 : Nat := 118140960795 + 4472015 * 2 ^ 59
def prefixEnd_4472015 : Nat := 4983230072969 + 3 ^ 40 * 4472015 * 2
def baseEnd_4472015 : Nat := 2296293189116425954446083

theorem tailTrace_4472015 : CollatzResearch.WordTrace tailWord_4472015 prefixEnd_4472015 2296293189116425954446083 := by
  unfold tailWord_4472015
  simp only [CollatzResearch.WordTrace]
  refine ⟨163107786893660889201121499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108738524595773926134080999 163107786893660889201121499)
  ·
    refine ⟨244661680340491333801682249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163107786893660889201121499 244661680340491333801682249)
    ·
      refine ⟨183496260255368500351261687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244661680340491333801682249 183496260255368500351261687)
      ·
        refine ⟨275244390383052750526892531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183496260255368500351261687 275244390383052750526892531)
        ·
          refine ⟨412866585574579125790338797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275244390383052750526892531 412866585574579125790338797)
          ·
            refine ⟨154824969590467172171377049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 412866585574579125790338797 154824969590467172171377049)
            ·
              refine ⟨116118727192850379128532787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154824969590467172171377049 116118727192850379128532787)
              ·
                refine ⟨174178090789275568692799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116118727192850379128532787 174178090789275568692799181)
                ·
                  refine ⟨65316784045978338259799693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174178090789275568692799181 65316784045978338259799693)
                  ·
                    refine ⟨24493794017241876847424885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65316784045978338259799693 24493794017241876847424885)
                    ·
                      refine ⟨2296293189116425954446083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24493794017241876847424885 2296293189116425954446083)
                      ·
                        rfl

theorem cell23_4472015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 5].length) (baseStart_4472015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472015 prefixEnd_4472015 := by exact prefixLift 4472015
  have htrace : WordTrace (prefixWord ++ tailWord_4472015) baseStart_4472015 baseEnd_4472015 := by
    simpa [prefixWord, tailWord_4472015, baseEnd_4472015] using wordTrace_append hprefix tailTrace_4472015
  have hstable : (prefixWord ++ tailWord_4472015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472015).length < 2 ^ (prefixWord ++ tailWord_4472015).sum := by decide
  have hdescent : baseEnd_4472015 < baseStart_4472015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472046 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2]
def baseStart_4472046 : Nat := 118140960795 + 4472046 * 2 ^ 59
def prefixEnd_4472046 : Nat := 4983230072969 + 3 ^ 40 * 4472046 * 2
def baseEnd_4472046 : Nat := 2296309107016715333158441

theorem tailTrace_4472046 : CollatzResearch.WordTrace tailWord_4472046 prefixEnd_4472046 2296309107016715333158441 := by
  unfold tailWord_4472046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20388614694568572686937499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108739278371032387663666661 20388614694568572686937499)
  ·
    refine ⟨30582922041852859030406249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20388614694568572686937499 30582922041852859030406249)
    ·
      refine ⟨22937191531389644272804687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30582922041852859030406249 22937191531389644272804687)
      ·
        refine ⟨34405787297084466409207031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22937191531389644272804687 34405787297084466409207031)
        ·
          refine ⟨51608680945626699613810547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34405787297084466409207031 51608680945626699613810547)
          ·
            refine ⟨77413021418440049420715821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51608680945626699613810547 77413021418440049420715821)
            ·
              refine ⟨29029883031915018532768433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77413021418440049420715821 29029883031915018532768433)
              ·
                refine ⟨21772412273936263899576325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29029883031915018532768433 21772412273936263899576325)
                ·
                  refine ⟨4082327301363049481170561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21772412273936263899576325 4082327301363049481170561)
                  ·
                    refine ⟨3061745476022287110877921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4082327301363049481170561 3061745476022287110877921)
                    ·
                      refine ⟨2296309107016715333158441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061745476022287110877921 2296309107016715333158441)
                      ·
                        rfl

theorem cell23_4472046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_4472046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472046 prefixEnd_4472046 := by exact prefixLift 4472046
  have htrace : WordTrace (prefixWord ++ tailWord_4472046) baseStart_4472046 baseEnd_4472046 := by
    simpa [prefixWord, tailWord_4472046, baseEnd_4472046] using wordTrace_append hprefix tailTrace_4472046
  have hstable : (prefixWord ++ tailWord_4472046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472046).length < 2 ^ (prefixWord ++ tailWord_4472046).sum := by decide
  have hdescent : baseEnd_4472046 < baseStart_4472046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472099 : List Nat := [1, 1, 1, 4, 2, 4, 2, 1, 2, 5]
def baseStart_4472099 : Nat := 118140960795 + 4472099 * 2 ^ 59
def prefixEnd_4472099 : Nat := 4983230072969 + 3 ^ 40 * 4472099 * 2
def baseEnd_4472099 : Nat := 765445440497134541931899

theorem tailTrace_4472099 : CollatzResearch.WordTrace tailWord_4472099 prefixEnd_4472099 765445440497134541931899 := by
  unfold tailWord_4472099
  simp only [CollatzResearch.WordTrace]
  refine ⟨163110850625356571547179351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108740567083571047698119567 163110850625356571547179351)
  ·
    refine ⟨244666275938034857320769027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163110850625356571547179351 244666275938034857320769027)
    ·
      refine ⟨366999413907052285981153541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244666275938034857320769027 366999413907052285981153541)
      ·
        refine ⟨68812390107572303621466289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 366999413907052285981153541 68812390107572303621466289)
        ·
          refine ⟨51609292580679227716099717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68812390107572303621466289 51609292580679227716099717)
          ·
            refine ⟨9676742358877355196768697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51609292580679227716099717 9676742358877355196768697)
            ·
              refine ⟨7257556769158016397576523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9676742358877355196768697 7257556769158016397576523)
              ·
                refine ⟨10886335153737024596364785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7257556769158016397576523 10886335153737024596364785)
                ·
                  refine ⟨8164751365302768447273589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10886335153737024596364785 8164751365302768447273589)
                  ·
                    refine ⟨765445440497134541931899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8164751365302768447273589 765445440497134541931899)
                    ·
                      rfl

theorem cell23_4472099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 5].length) (baseStart_4472099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472099 prefixEnd_4472099 := by exact prefixLift 4472099
  have htrace : WordTrace (prefixWord ++ tailWord_4472099) baseStart_4472099 baseEnd_4472099 := by
    simpa [prefixWord, tailWord_4472099, baseEnd_4472099] using wordTrace_append hprefix tailTrace_4472099
  have hstable : (prefixWord ++ tailWord_4472099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472099).length < 2 ^ (prefixWord ++ tailWord_4472099).sum := by decide
  have hdescent : baseEnd_4472099 < baseStart_4472099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472122 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_4472122 : Nat := 118140960795 + 4472122 * 2 ^ 59
def prefixEnd_4472122 : Nat := 4983230072969 + 3 ^ 40 * 4472122 * 2
def baseEnd_4472122 : Nat := 2296348131546457035808091

theorem tailTrace_4472122 : CollatzResearch.WordTrace tailWord_4472122 prefixEnd_4472122 2296348131546457035808091 := by
  unfold tailWord_4472122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40777922376068311618816655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108741126336182164316844413 40777922376068311618816655)
  ·
    refine ⟨61166883564102467428224983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40777922376068311618816655 61166883564102467428224983)
    ·
      refine ⟨91750325346153701142337475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61166883564102467428224983 91750325346153701142337475)
      ·
        refine ⟨137625488019230551713506213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91750325346153701142337475 137625488019230551713506213)
        ·
          refine ⟨25804779003605728446282415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137625488019230551713506213 25804779003605728446282415)
          ·
            refine ⟨38707168505408592669423623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25804779003605728446282415 38707168505408592669423623)
            ·
              refine ⟨58060752758112889004135435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38707168505408592669423623 58060752758112889004135435)
              ·
                refine ⟨87091129137169333506203153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58060752758112889004135435 87091129137169333506203153)
                ·
                  refine ⟨65318346852877000129652365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 87091129137169333506203153 65318346852877000129652365)
                  ·
                    refine ⟨24494380069828875048619637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 65318346852877000129652365 24494380069828875048619637)
                    ·
                      refine ⟨2296348131546457035808091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24494380069828875048619637 2296348131546457035808091)
                      ·
                        rfl

theorem cell23_4472122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_4472122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472122 prefixEnd_4472122 := by exact prefixLift 4472122
  have htrace : WordTrace (prefixWord ++ tailWord_4472122) baseStart_4472122 baseEnd_4472122 := by
    simpa [prefixWord, tailWord_4472122, baseEnd_4472122] using wordTrace_append hprefix tailTrace_4472122
  have hstable : (prefixWord ++ tailWord_4472122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472122).length < 2 ^ (prefixWord ++ tailWord_4472122).sum := by decide
  have hdescent : baseEnd_4472122 < baseStart_4472122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472150 : List Nat := [5, 2, 3, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4472150 : Nat := 118140960795 + 4472150 * 2 ^ 59
def prefixEnd_4472150 : Nat := 4983230072969 + 3 ^ 40 * 4472150 * 2
def baseEnd_4472150 : Nat := 765454169668260975419321

theorem tailTrace_4472150 : CollatzResearch.WordTrace tailWord_4472150 prefixEnd_4472150 765454169668260975419321 := by
  unfold tailWord_4472150
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194544421760737953580369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108741807165447871504857269 10194544421760737953580369)
  ·
    refine ⟨7645908316320553465185277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10194544421760737953580369 7645908316320553465185277)
    ·
      refine ⟨2867215618620207549444479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7645908316320553465185277 2867215618620207549444479)
      ·
        refine ⟨4300823427930311324166719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2867215618620207549444479 4300823427930311324166719)
        ·
          refine ⟨6451235141895466986250079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4300823427930311324166719 6451235141895466986250079)
          ·
            refine ⟨9676852712843200479375119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6451235141895466986250079 9676852712843200479375119)
            ·
              refine ⟨14515279069264800719062679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9676852712843200479375119 14515279069264800719062679)
              ·
                refine ⟨21772918603897201078594019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14515279069264800719062679 21772918603897201078594019)
                ·
                  refine ⟨32659377905845801617891029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21772918603897201078594019 32659377905845801617891029)
                  ·
                    refine ⟨765454169668260975419321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32659377905845801617891029 765454169668260975419321)
                    ·
                      rfl

theorem cell23_4472150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4472150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472150 prefixEnd_4472150 := by exact prefixLift 4472150
  have htrace : WordTrace (prefixWord ++ tailWord_4472150) baseStart_4472150 baseEnd_4472150 := by
    simpa [prefixWord, tailWord_4472150, baseEnd_4472150] using wordTrace_append hprefix tailTrace_4472150
  have hstable : (prefixWord ++ tailWord_4472150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472150).length < 2 ^ (prefixWord ++ tailWord_4472150).sum := by decide
  have hdescent : baseEnd_4472150 < baseStart_4472150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472163 : List Nat := [1, 1, 1, 5, 2, 3, 2, 3, 1, 4]
def baseStart_4472163 : Nat := 118140960795 + 4472163 * 2 ^ 59
def prefixEnd_4472163 : Nat := 4983230072969 + 3 ^ 40 * 4472163 * 2
def baseEnd_4472163 : Nat := 765456394751097125131801

theorem tailTrace_4472163 : CollatzResearch.WordTrace tailWord_4472163 prefixEnd_4472163 765456394751097125131801 := by
  unfold tailWord_4472163
  simp only [CollatzResearch.WordTrace]
  refine ⟨163113184897124710477509143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108742123264749806985006095 163113184897124710477509143)
  ·
    refine ⟨244669777345687065716263715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163113184897124710477509143 244669777345687065716263715)
    ·
      refine ⟨367004666018530598574395573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244669777345687065716263715 367004666018530598574395573)
      ·
        refine ⟨34406687439237243616349585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 367004666018530598574395573 34406687439237243616349585)
        ·
          refine ⟨25805015579427932712262189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34406687439237243616349585 25805015579427932712262189)
          ·
            refine ⟨9676880842285474767098321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25805015579427932712262189 9676880842285474767098321)
            ·
              refine ⟨7257660631714106075323741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9676880842285474767098321 7257660631714106075323741)
              ·
                refine ⟨2721622736892789778246403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7257660631714106075323741 2721622736892789778246403)
                ·
                  refine ⟨4082434105339184667369605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2721622736892789778246403 4082434105339184667369605)
                  ·
                    refine ⟨765456394751097125131801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4082434105339184667369605 765456394751097125131801)
                    ·
                      rfl

theorem cell23_4472163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 3, 1, 4].length) (baseStart_4472163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472163 prefixEnd_4472163 := by exact prefixLift 4472163
  have htrace : WordTrace (prefixWord ++ tailWord_4472163) baseStart_4472163 baseEnd_4472163 := by
    simpa [prefixWord, tailWord_4472163, baseEnd_4472163] using wordTrace_append hprefix tailTrace_4472163
  have hstable : (prefixWord ++ tailWord_4472163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472163).length < 2 ^ (prefixWord ++ tailWord_4472163).sum := by decide
  have hdescent : baseEnd_4472163 < baseStart_4472163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472179 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 5, 5, 2]
def baseStart_4472179 : Nat := 118140960795 + 4472179 * 2 ^ 59
def prefixEnd_4472179 : Nat := 4983230072969 + 3 ^ 40 * 4472179 * 2
def baseEnd_4472179 : Nat := 2296377399943763312795329

theorem tailTrace_4472179 : CollatzResearch.WordTrace tailWord_4472179 prefixEnd_4472179 2296377399943763312795329 := by
  unfold tailWord_4472179
  simp only [CollatzResearch.WordTrace]
  refine ⟨163113768465066745210091591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108742512310044496806727727 163113768465066745210091591)
  ·
    refine ⟨244670652697600117815137387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163113768465066745210091591 244670652697600117815137387)
    ·
      refine ⟨367005979046400176722706081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244670652697600117815137387 367005979046400176722706081)
      ·
        refine ⟨275254484284800132542029561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367005979046400176722706081 275254484284800132542029561)
        ·
          refine ⟨206440863213600099406522171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275254484284800132542029561 206440863213600099406522171)
          ·
            refine ⟨309661294820400149109783257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206440863213600099406522171 309661294820400149109783257)
            ·
              refine ⟨232245971115300111832337443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309661294820400149109783257 232245971115300111832337443)
              ·
                refine ⟨348368956672950167748506165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232245971115300111832337443 348368956672950167748506165)
                ·
                  refine ⟨32659589688089078226422453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348368956672950167748506165 32659589688089078226422453)
                  ·
                    refine ⟨3061836533258351083727105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32659589688089078226422453 3061836533258351083727105)
                    ·
                      refine ⟨2296377399943763312795329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061836533258351083727105 2296377399943763312795329)
                      ·
                        rfl

theorem cell23_4472179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 5, 5, 2].length) (baseStart_4472179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472179 prefixEnd_4472179 := by exact prefixLift 4472179
  have htrace : WordTrace (prefixWord ++ tailWord_4472179) baseStart_4472179 baseEnd_4472179 := by
    simpa [prefixWord, tailWord_4472179, baseEnd_4472179] using wordTrace_append hprefix tailTrace_4472179
  have hstable : (prefixWord ++ tailWord_4472179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472179).length < 2 ^ (prefixWord ++ tailWord_4472179).sum := by decide
  have hdescent : baseEnd_4472179 < baseStart_4472179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472193 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 6]
def baseStart_4472193 : Nat := 118140960795 + 4472193 * 2 ^ 59
def prefixEnd_4472193 : Nat := 4983230072969 + 3 ^ 40 * 4472193 * 2
def baseEnd_4472193 : Nat := 255153843185880695335585

theorem tailTrace_4472193 : CollatzResearch.WordTrace tailWord_4472193 prefixEnd_4472193 255153843185880695335585 := by
  unfold tailWord_4472193
  simp only [CollatzResearch.WordTrace]
  refine ⟨163114279087016025601101233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108742852724677350400734155 163114279087016025601101233)
  ·
    refine ⟨122335709315262019200825925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163114279087016025601101233 122335709315262019200825925)
    ·
      refine ⟨22937945496611628600154861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122335709315262019200825925 22937945496611628600154861)
      ·
        refine ⟨8601729561229360725058073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22937945496611628600154861 8601729561229360725058073)
        ·
          refine ⟨6451297170922020543793555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8601729561229360725058073 6451297170922020543793555)
          ·
            refine ⟨9676945756383030815690333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6451297170922020543793555 9676945756383030815690333)
            ·
              refine ⟨3628854658643636555883875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9676945756383030815690333 3628854658643636555883875)
              ·
                refine ⟨5443281987965454833825813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3628854658643636555883875 5443281987965454833825813)
                ·
                  refine ⟨255153843185880695335585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5443281987965454833825813 255153843185880695335585)
                  ·
                    rfl

theorem cell23_4472193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 6].length) (baseStart_4472193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472193 prefixEnd_4472193 := by exact prefixLift 4472193
  have htrace : WordTrace (prefixWord ++ tailWord_4472193) baseStart_4472193 baseEnd_4472193 := by
    simpa [prefixWord, tailWord_4472193, baseEnd_4472193] using wordTrace_append hprefix tailTrace_4472193
  have hstable : (prefixWord ++ tailWord_4472193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472193).length < 2 ^ (prefixWord ++ tailWord_4472193).sum := by decide
  have hdescent : baseEnd_4472193 < baseStart_4472193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472196 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_4472196 : Nat := 118140960795 + 4472196 * 2 ^ 59
def prefixEnd_4472196 : Nat := 4983230072969 + 3 ^ 40 * 4472196 * 2
def baseEnd_4472196 : Nat := 2296386129114889746282751

theorem tailTrace_4472196 : CollatzResearch.WordTrace tailWord_4472196 prefixEnd_4472196 2296386129114889746282751 := by
  unfold tailWord_4472196
  simp only [CollatzResearch.WordTrace]
  refine ⟨81557194253002578556730221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108742925670670104742306961 81557194253002578556730221)
  ·
    refine ⟨30583947844875966958773833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81557194253002578556730221 30583947844875966958773833)
    ·
      refine ⟨22937960883656975219080375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30583947844875966958773833 22937960883656975219080375)
      ·
        refine ⟨34406941325485462828620563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22937960883656975219080375 34406941325485462828620563)
        ·
          refine ⟨51610411988228194242930845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34406941325485462828620563 51610411988228194242930845)
          ·
            refine ⟨19353904495585572841099067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51610411988228194242930845 19353904495585572841099067)
            ·
              refine ⟨29030856743378359261648601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19353904495585572841099067 29030856743378359261648601)
              ·
                refine ⟨21773142557533769446236451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29030856743378359261648601 21773142557533769446236451)
                ·
                  refine ⟨32659713836300654169354677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21773142557533769446236451 32659713836300654169354677)
                  ·
                    refine ⟨3061848172153186328377001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32659713836300654169354677 3061848172153186328377001)
                    ·
                      refine ⟨2296386129114889746282751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3061848172153186328377001 2296386129114889746282751)
                      ·
                        rfl

theorem cell23_4472196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_4472196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472196 prefixEnd_4472196 := by exact prefixLift 4472196
  have htrace : WordTrace (prefixWord ++ tailWord_4472196) baseStart_4472196 baseEnd_4472196 := by
    simpa [prefixWord, tailWord_4472196, baseEnd_4472196] using wordTrace_append hprefix tailTrace_4472196
  have hstable : (prefixWord ++ tailWord_4472196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472196).length < 2 ^ (prefixWord ++ tailWord_4472196).sum := by decide
  have hdescent : baseEnd_4472196 < baseStart_4472196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472260 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4472260 : Nat := 118140960795 + 4472260 * 2 ^ 59
def prefixEnd_4472260 : Nat := 4983230072969 + 3 ^ 40 * 4472260 * 2
def baseEnd_4472260 : Nat := 2296418991876777495882457

theorem tailTrace_4472260 : CollatzResearch.WordTrace tailWord_4472260 prefixEnd_4472260 2296418991876777495882457 := by
  unfold tailWord_4472260
  simp only [CollatzResearch.WordTrace]
  refine ⟨81558361388886648021895117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108744481851848864029193489 81558361388886648021895117)
  ·
    refine ⟨30584385520832493008210669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81558361388886648021895117 30584385520832493008210669)
    ·
      refine ⟨11469144570312184878079001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30584385520832493008210669 11469144570312184878079001)
      ·
        refine ⟨8601858427734138658559251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11469144570312184878079001 8601858427734138658559251)
        ·
          refine ⟨12902787641601207987838877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8601858427734138658559251 12902787641601207987838877)
          ·
            refine ⟨4838545365600452995439579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12902787641601207987838877 4838545365600452995439579)
            ·
              refine ⟨7257818048400679493159369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4838545365600452995439579 7257818048400679493159369)
              ·
                refine ⟨5443363536300509619869527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7257818048400679493159369 5443363536300509619869527)
                ·
                  refine ⟨8165045304450764429804291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5443363536300509619869527 8165045304450764429804291)
                  ·
                    refine ⟨12247567956676146644706437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8165045304450764429804291 12247567956676146644706437)
                    ·
                      refine ⟨2296418991876777495882457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12247567956676146644706437 2296418991876777495882457)
                      ·
                        rfl

theorem cell23_4472260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4472260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472260 prefixEnd_4472260 := by exact prefixLift 4472260
  have htrace : WordTrace (prefixWord ++ tailWord_4472260) baseStart_4472260 baseEnd_4472260 := by
    simpa [prefixWord, tailWord_4472260, baseEnd_4472260] using wordTrace_append hprefix tailTrace_4472260
  have hstable : (prefixWord ++ tailWord_4472260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472260).length < 2 ^ (prefixWord ++ tailWord_4472260).sum := by decide
  have hdescent : baseEnd_4472260 < baseStart_4472260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472310 : List Nat := [5, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4472310 : Nat := 118140960795 + 4472310 * 2 ^ 59
def prefixEnd_4472310 : Nat := 4983230072969 + 3 ^ 40 * 4472310 * 2
def baseEnd_4472310 : Nat := 2296444665909502300257227

theorem tailTrace_4472310 : CollatzResearch.WordTrace tailWord_4472310 prefixEnd_4472310 2296444665909502300257227 := by
  unfold tailWord_4472310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10194909151724509661444399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108745697618394769722073589 10194909151724509661444399)
  ·
    refine ⟨15292363727586764492166599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10194909151724509661444399 15292363727586764492166599)
    ·
      refine ⟨22938545591380146738249899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15292363727586764492166599 22938545591380146738249899)
      ·
        refine ⟨34407818387070220107374849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22938545591380146738249899 34407818387070220107374849)
        ·
          refine ⟨25805863790302665080531137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34407818387070220107374849 25805863790302665080531137)
          ·
            refine ⟨19354397842726998810398353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25805863790302665080531137 19354397842726998810398353)
            ·
              refine ⟨14515798382045249107798765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19354397842726998810398353 14515798382045249107798765)
              ·
                refine ⟨5443424393266968415424537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14515798382045249107798765 5443424393266968415424537)
                ·
                  refine ⟨4082568294950226311568403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5443424393266968415424537 4082568294950226311568403)
                  ·
                    refine ⟨6123852442425339467352605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4082568294950226311568403 6123852442425339467352605)
                    ·
                      refine ⟨2296444665909502300257227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6123852442425339467352605 2296444665909502300257227)
                      ·
                        rfl

theorem cell23_4472310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4472310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472310 prefixEnd_4472310 := by exact prefixLift 4472310
  have htrace : WordTrace (prefixWord ++ tailWord_4472310) baseStart_4472310 baseEnd_4472310 := by
    simpa [prefixWord, tailWord_4472310, baseEnd_4472310] using wordTrace_append hprefix tailTrace_4472310
  have hstable : (prefixWord ++ tailWord_4472310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472310).length < 2 ^ (prefixWord ++ tailWord_4472310).sum := by decide
  have hdescent : baseEnd_4472310 < baseStart_4472310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472319 : List Nat := [1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5]
def baseStart_4472319 : Nat := 118140960795 + 4472319 * 2 ^ 59
def prefixEnd_4472319 : Nat := 4983230072969 + 3 ^ 40 * 4472319 * 2
def baseEnd_4472319 : Nat := 2296449287235392765044685

theorem tailTrace_4472319 : CollatzResearch.WordTrace tailWord_4472319 prefixEnd_4472319 2296449287235392765044685 := by
  unfold tailWord_4472319
  simp only [CollatzResearch.WordTrace]
  refine ⟨163118874684559549120188011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108745916456373032746792007 163118874684559549120188011)
  ·
    refine ⟨244678312026839323680282017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163118874684559549120188011 244678312026839323680282017)
    ·
      refine ⟨183508734020129492760211513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244678312026839323680282017 183508734020129492760211513)
      ·
        refine ⟨137631550515097119570158635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183508734020129492760211513 137631550515097119570158635)
        ·
          refine ⟨206447325772645679355237953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137631550515097119570158635 206447325772645679355237953)
          ·
            refine ⟨154835494329484259516428465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206447325772645679355237953 154835494329484259516428465)
            ·
              refine ⟨116126620747113194637321349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154835494329484259516428465 116126620747113194637321349)
              ·
                refine ⟨21773741390083723994497753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116126620747113194637321349 21773741390083723994497753)
                ·
                  refine ⟨16330306042562792995873315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21773741390083723994497753 16330306042562792995873315)
                  ·
                    refine ⟨24495459063844189493809973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16330306042562792995873315 24495459063844189493809973)
                    ·
                      refine ⟨2296449287235392765044685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24495459063844189493809973 2296449287235392765044685)
                      ·
                        rfl

theorem cell23_4472319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_4472319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472319 prefixEnd_4472319 := by exact prefixLift 4472319
  have htrace : WordTrace (prefixWord ++ tailWord_4472319) baseStart_4472319 baseEnd_4472319 := by
    simpa [prefixWord, tailWord_4472319, baseEnd_4472319] using wordTrace_append hprefix tailTrace_4472319
  have hstable : (prefixWord ++ tailWord_4472319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472319).length < 2 ^ (prefixWord ++ tailWord_4472319).sum := by decide
  have hdescent : baseEnd_4472319 < baseStart_4472319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472329 : List Nat := [1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 4]
def baseStart_4472329 : Nat := 118140960795 + 4472329 * 2 ^ 59
def prefixEnd_4472329 : Nat := 4983230072969 + 3 ^ 40 * 4472329 * 2
def baseEnd_4472329 : Nat := 2296454422041937725919639

theorem tailTrace_4472329 : CollatzResearch.WordTrace tailWord_4472329 prefixEnd_4472329 2296454422041937725919639 := by
  unfold tailWord_4472329
  simp only [CollatzResearch.WordTrace]
  refine ⟨163119239414523320828052041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108746159609682213885368027 163119239414523320828052041)
  ·
    refine ⟨122339429560892490621039031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163119239414523320828052041 122339429560892490621039031)
    ·
      refine ⟨183509144341338735931558547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122339429560892490621039031 183509144341338735931558547)
      ·
        refine ⟨275263716512008103897337821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183509144341338735931558547 275263716512008103897337821)
        ·
          refine ⟨103223893692003038961501683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275263716512008103897337821 103223893692003038961501683)
          ·
            refine ⟨154835840538004558442252525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103223893692003038961501683 154835840538004558442252525)
            ·
              refine ⟨58063440201751709415844697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154835840538004558442252525 58063440201751709415844697)
              ·
                refine ⟨43547580151313782061883523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58063440201751709415844697 43547580151313782061883523)
                ·
                  refine ⟨65321370226970673092825285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43547580151313782061883523 65321370226970673092825285)
                  ·
                    refine ⟨12247756917557001204904741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65321370226970673092825285 12247756917557001204904741)
                    ·
                      refine ⟨2296454422041937725919639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12247756917557001204904741 2296454422041937725919639)
                      ·
                        rfl

theorem cell23_4472329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_4472329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472329 prefixEnd_4472329 := by exact prefixLift 4472329
  have htrace : WordTrace (prefixWord ++ tailWord_4472329) baseStart_4472329 baseEnd_4472329 := by
    simpa [prefixWord, tailWord_4472329, baseEnd_4472329] using wordTrace_append hprefix tailTrace_4472329
  have hstable : (prefixWord ++ tailWord_4472329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472329).length < 2 ^ (prefixWord ++ tailWord_4472329).sum := by decide
  have hdescent : baseEnd_4472329 < baseStart_4472329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472423 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 2, 4, 2]
def baseStart_4472423 : Nat := 118140960795 + 4472423 * 2 ^ 59
def prefixEnd_4472423 : Nat := 4983230072969 + 3 ^ 40 * 4472423 * 2
def baseEnd_4472423 : Nat := 2296502689223460358144207

theorem tailTrace_4472423 : CollatzResearch.WordTrace tailWord_4472423 prefixEnd_4472423 2296502689223460358144207 := by
  unfold tailWord_4472423
  simp only [CollatzResearch.WordTrace]
  refine ⟨163122667876182774881973923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108748445250788516587982615 163122667876182774881973923)
  ·
    refine ⟨244684001814274162322960885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163122667876182774881973923 244684001814274162322960885)
    ·
      refine ⟨22939125170088202717777583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 244684001814274162322960885 22939125170088202717777583)
      ·
        refine ⟨34408687755132304076666375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22939125170088202717777583 34408687755132304076666375)
        ·
          refine ⟨51613031632698456114999563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34408687755132304076666375 51613031632698456114999563)
          ·
            refine ⟨77419547449047684172499345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51613031632698456114999563 77419547449047684172499345)
            ·
              refine ⟨58064660586785763129374509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77419547449047684172499345 58064660586785763129374509)
              ·
                refine ⟨21774247720044661173515441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58064660586785763129374509 21774247720044661173515441)
                ·
                  refine ⟨16330685790033495880136581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21774247720044661173515441 16330685790033495880136581)
                  ·
                    refine ⟨3062003585631280477525609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16330685790033495880136581 3062003585631280477525609)
                    ·
                      refine ⟨2296502689223460358144207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062003585631280477525609 2296502689223460358144207)
                      ·
                        rfl

theorem cell23_4472423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_4472423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472423 prefixEnd_4472423 := by exact prefixLift 4472423
  have htrace : WordTrace (prefixWord ++ tailWord_4472423) baseStart_4472423 baseEnd_4472423 := by
    simpa [prefixWord, tailWord_4472423, baseEnd_4472423] using wordTrace_append hprefix tailTrace_4472423
  have hstable : (prefixWord ++ tailWord_4472423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472423).length < 2 ^ (prefixWord ++ tailWord_4472423).sum := by decide
  have hdescent : baseEnd_4472423 < baseStart_4472423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472443 : List Nat := [1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3]
def baseStart_4472443 : Nat := 118140960795 + 4472443 * 2 ^ 59
def prefixEnd_4472443 : Nat := 4983230072969 + 3 ^ 40 * 4472443 * 2
def baseEnd_4472443 : Nat := 2296512958836550279894115

theorem tailTrace_4472443 : CollatzResearch.WordTrace tailWord_4472443 prefixEnd_4472443 2296512958836550279894115 := by
  unfold tailWord_4472443
  simp only [CollatzResearch.WordTrace]
  refine ⟨163123397336110318297701983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108748931557406878865134655 163123397336110318297701983)
  ·
    refine ⟨244685096004165477446552975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163123397336110318297701983 244685096004165477446552975)
    ·
      refine ⟨367027644006248216169829463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244685096004165477446552975 367027644006248216169829463)
      ·
        refine ⟨550541466009372324254744195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367027644006248216169829463 550541466009372324254744195)
        ·
          refine ⟨825812199014058486382116293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550541466009372324254744195 825812199014058486382116293)
          ·
            refine ⟨154839787315135966196646805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 825812199014058486382116293 154839787315135966196646805)
            ·
              refine ⟨7258115030396998415467819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 154839787315135966196646805 7258115030396998415467819)
              ·
                refine ⟨10887172545595497623201729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7258115030396998415467819 10887172545595497623201729)
                ·
                  refine ⟨8165379409196623217401297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10887172545595497623201729 8165379409196623217401297)
                  ·
                    refine ⟨6124034556897467413050973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8165379409196623217401297 6124034556897467413050973)
                    ·
                      refine ⟨2296512958836550279894115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124034556897467413050973 2296512958836550279894115)
                      ·
                        rfl

theorem cell23_4472443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 1, 2, 2, 3].length) (baseStart_4472443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472443 prefixEnd_4472443 := by exact prefixLift 4472443
  have htrace : WordTrace (prefixWord ++ tailWord_4472443) baseStart_4472443 baseEnd_4472443 := by
    simpa [prefixWord, tailWord_4472443, baseEnd_4472443] using wordTrace_append hprefix tailTrace_4472443
  have hstable : (prefixWord ++ tailWord_4472443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472443).length < 2 ^ (prefixWord ++ tailWord_4472443).sum := by decide
  have hdescent : baseEnd_4472443 < baseStart_4472443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472483 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 1, 5, 2]
def baseStart_4472483 : Nat := 118140960795 + 4472483 * 2 ^ 59
def prefixEnd_4472483 : Nat := 4983230072969 + 3 ^ 40 * 4472483 * 2
def baseEnd_4472483 : Nat := 2296533498062730123393931

theorem tailTrace_4472483 : CollatzResearch.WordTrace tailWord_4472483 prefixEnd_4472483 2296533498062730123393931 := by
  unfold tailWord_4472483
  simp only [CollatzResearch.WordTrace]
  refine ⟨163124856255965405129158103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108749904170643603419438735 163124856255965405129158103)
  ·
    refine ⟨244687284383948107693737155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163124856255965405129158103 244687284383948107693737155)
    ·
      refine ⟨367030926575922161540605733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244687284383948107693737155 367030926575922161540605733)
      ·
        refine ⟨68818298732985405288863575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367030926575922161540605733 68818298732985405288863575)
        ·
          refine ⟨103227448099478107933295363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68818298732985405288863575 103227448099478107933295363)
          ·
            refine ⟨154841172149217161899943045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103227448099478107933295363 154841172149217161899943045)
            ·
              refine ⟨29032719777978217856239321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 154841172149217161899943045 29032719777978217856239321)
              ·
                refine ⟨21774539833483663392179491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29032719777978217856239321 21774539833483663392179491)
                ·
                  refine ⟨32661809750225495088269237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21774539833483663392179491 32661809750225495088269237)
                  ·
                    refine ⟨3062044664083640164525241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32661809750225495088269237 3062044664083640164525241)
                    ·
                      refine ⟨2296533498062730123393931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062044664083640164525241 2296533498062730123393931)
                      ·
                        rfl

theorem cell23_4472483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 5, 2].length) (baseStart_4472483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472483 prefixEnd_4472483 := by exact prefixLift 4472483
  have htrace : WordTrace (prefixWord ++ tailWord_4472483) baseStart_4472483 baseEnd_4472483 := by
    simpa [prefixWord, tailWord_4472483, baseEnd_4472483] using wordTrace_append hprefix tailTrace_4472483
  have hstable : (prefixWord ++ tailWord_4472483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472483).length < 2 ^ (prefixWord ++ tailWord_4472483).sum := by decide
  have hdescent : baseEnd_4472483 < baseStart_4472483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472493 : List Nat := [1, 5, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4472493 : Nat := 118140960795 + 4472493 * 2 ^ 59
def prefixEnd_4472493 : Nat := 4983230072969 + 3 ^ 40 * 4472493 * 2
def baseEnd_4472493 : Nat := 765512877623091694756295

theorem tailTrace_4472493 : CollatzResearch.WordTrace tailWord_4472493 prefixEnd_4472493 765512877623091694756295 := by
  unfold tailWord_4472493
  simp only [CollatzResearch.WordTrace]
  refine ⟨163125220985929176837022133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108750147323952784558014755 163125220985929176837022133)
  ·
    refine ⟨15292989467430860328470825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163125220985929176837022133 15292989467430860328470825)
    ·
      refine ⟨11469742100573145246353119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15292989467430860328470825 11469742100573145246353119)
      ·
        refine ⟨17204613150859717869529679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11469742100573145246353119 17204613150859717869529679)
        ·
          refine ⟨25806919726289576804294519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17204613150859717869529679 25806919726289576804294519)
          ·
            refine ⟨38710379589434365206441779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25806919726289576804294519 38710379589434365206441779)
            ·
              refine ⟨58065569384151547809662669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38710379589434365206441779 58065569384151547809662669)
              ·
                refine ⟨21774588519056830428623501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58065569384151547809662669 21774588519056830428623501)
                ·
                  refine ⟨8165470694646311410733813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21774588519056830428623501 8165470694646311410733813)
                  ·
                    refine ⟨765512877623091694756295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8165470694646311410733813 765512877623091694756295)
                    ·
                      rfl

theorem cell23_4472493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4472493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472493 prefixEnd_4472493 := by exact prefixLift 4472493
  have htrace : WordTrace (prefixWord ++ tailWord_4472493) baseStart_4472493 baseEnd_4472493 := by
    simpa [prefixWord, tailWord_4472493, baseEnd_4472493] using wordTrace_append hprefix tailTrace_4472493
  have hstable : (prefixWord ++ tailWord_4472493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472493).length < 2 ^ (prefixWord ++ tailWord_4472493).sum := by decide
  have hdescent : baseEnd_4472493 < baseStart_4472493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472494 : List Nat := [4, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_4472494 : Nat := 118140960795 + 4472494 * 2 ^ 59
def prefixEnd_4472494 : Nat := 4983230072969 + 3 ^ 40 * 4472494 * 2
def baseEnd_4472494 : Nat := 2296539146349929580356381

theorem tailTrace_4472494 : CollatzResearch.WordTrace tailWord_4472494 prefixEnd_4472494 2296539146349929580356381 := by
  unfold tailWord_4472494
  simp only [CollatzResearch.WordTrace]
  refine ⟨20390657182365694250976067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108750171639283702671872357 20390657182365694250976067)
  ·
    refine ⟨30585985773548541376464101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20390657182365694250976067 30585985773548541376464101)
    ·
      refine ⟨5734872332540351508087019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30585985773548541376464101 5734872332540351508087019)
      ·
        refine ⟨8602308498810527262130529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734872332540351508087019 8602308498810527262130529)
        ·
          refine ⟨6451731374107895446597897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8602308498810527262130529 6451731374107895446597897)
          ·
            refine ⟨4838798530580921584948423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6451731374107895446597897 4838798530580921584948423)
            ·
              refine ⟨7258197795871382377422635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4838798530580921584948423 7258197795871382377422635)
              ·
                refine ⟨10887296693807073566133953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7258197795871382377422635 10887296693807073566133953)
                ·
                  refine ⟨8165472520355305174600465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10887296693807073566133953 8165472520355305174600465)
                  ·
                    refine ⟨6124104390266478880950349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8165472520355305174600465 6124104390266478880950349)
                    ·
                      refine ⟨2296539146349929580356381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124104390266478880950349 2296539146349929580356381)
                      ·
                        rfl

theorem cell23_4472494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_4472494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472494 prefixEnd_4472494 := by exact prefixLift 4472494
  have htrace : WordTrace (prefixWord ++ tailWord_4472494) baseStart_4472494 baseEnd_4472494 := by
    simpa [prefixWord, tailWord_4472494, baseEnd_4472494] using wordTrace_append hprefix tailTrace_4472494
  have hstable : (prefixWord ++ tailWord_4472494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472494).length < 2 ^ (prefixWord ++ tailWord_4472494).sum := by decide
  have hdescent : baseEnd_4472494 < baseStart_4472494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472510 : List Nat := [4, 2, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_4472510 : Nat := 118140960795 + 4472510 * 2 ^ 59
def prefixEnd_4472510 : Nat := 4983230072969 + 3 ^ 40 * 4472510 * 2
def baseEnd_4472510 : Nat := 765515787346800505918769

theorem tailTrace_4472510 : CollatzResearch.WordTrace tailWord_4472510 prefixEnd_4472510 765515787346800505918769 := by
  unfold tailWord_4472510
  simp only [CollatzResearch.WordTrace]
  refine ⟨20390730128358448592548873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108750560684578392493593989 20390730128358448592548873)
  ·
    refine ⟨15293047596268836444411655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20390730128358448592548873 15293047596268836444411655)
    ·
      refine ⟨22939571394403254666617483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15293047596268836444411655 22939571394403254666617483)
      ·
        refine ⟨34409357091604881999926225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22939571394403254666617483 34409357091604881999926225)
        ·
          refine ⟨25807017818703661499944669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34409357091604881999926225 25807017818703661499944669)
          ·
            refine ⟨9677631682013873062479251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25807017818703661499944669 9677631682013873062479251)
            ·
              refine ⟨14516447523020809593718877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677631682013873062479251 14516447523020809593718877)
              ·
                refine ⟨5443667821132803597644579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14516447523020809593718877 5443667821132803597644579)
                ·
                  refine ⟨8165501731699205396466869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5443667821132803597644579 8165501731699205396466869)
                  ·
                    refine ⟨765515787346800505918769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8165501731699205396466869 765515787346800505918769)
                    ·
                      rfl

theorem cell23_4472510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_4472510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472510 prefixEnd_4472510 := by exact prefixLift 4472510
  have htrace : WordTrace (prefixWord ++ tailWord_4472510) baseStart_4472510 baseEnd_4472510 := by
    simpa [prefixWord, tailWord_4472510, baseEnd_4472510] using wordTrace_append hprefix tailTrace_4472510
  have hstable : (prefixWord ++ tailWord_4472510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472510).length < 2 ^ (prefixWord ++ tailWord_4472510).sum := by decide
  have hdescent : baseEnd_4472510 < baseStart_4472510 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472536 : List Nat := [2, 1, 2, 2, 3, 1, 2, 10]
def baseStart_4472536 : Nat := 118140960795 + 4472536 * 2 ^ 59
def prefixEnd_4472536 : Nat := 4983230072969 + 3 ^ 40 * 4472536 * 2
def baseEnd_4472536 : Nat := 85057804168052533927081

theorem tailTrace_4472536 : CollatzResearch.WordTrace tailWord_4472536 prefixEnd_4472536 85057804168052533927081 := by
  unfold tailWord_4472536
  simp only [CollatzResearch.WordTrace]
  refine ⟨81563394662386697590418731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108751192883182263453891641 81563394662386697590418731)
  ·
    refine ⟨122345091993580046385628097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81563394662386697590418731 122345091993580046385628097)
    ·
      refine ⟨91758818995185034789221073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122345091993580046385628097 91758818995185034789221073)
      ·
        refine ⟨68819114246388776091915805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91758818995185034789221073 68819114246388776091915805)
        ·
          refine ⟨25807167842395791034468427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68819114246388776091915805 25807167842395791034468427)
          ·
            refine ⟨38710751763593686551702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25807167842395791034468427 38710751763593686551702641)
            ·
              refine ⟨29033063822695264913776981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38710751763593686551702641 29033063822695264913776981)
              ·
                refine ⟨85057804168052533927081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29033063822695264913776981 85057804168052533927081)
                ·
                  rfl

theorem cell23_4472536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 10].length) (baseStart_4472536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472536 prefixEnd_4472536 := by exact prefixLift 4472536
  have htrace : WordTrace (prefixWord ++ tailWord_4472536) baseStart_4472536 baseEnd_4472536 := by
    simpa [prefixWord, tailWord_4472536, baseEnd_4472536] using wordTrace_append hprefix tailTrace_4472536
  have hstable : (prefixWord ++ tailWord_4472536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472536).length < 2 ^ (prefixWord ++ tailWord_4472536).sum := by decide
  have hdescent : baseEnd_4472536 < baseStart_4472536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472547 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4472547 : Nat := 118140960795 + 4472547 * 2 ^ 59
def prefixEnd_4472547 : Nat := 4983230072969 + 3 ^ 40 * 4472547 * 2
def baseEnd_4472547 : Nat := 2296566360824617872993637

theorem tailTrace_4472547 : CollatzResearch.WordTrace tailWord_4472547 prefixEnd_4472547 2296566360824617872993637 := by
  unfold tailWord_4472547
  simp only [CollatzResearch.WordTrace]
  refine ⟨163127190527733544059487895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108751460351822362706325263 163127190527733544059487895)
  ·
    refine ⟨244690785791600316089231843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163127190527733544059487895 244690785791600316089231843)
    ·
      refine ⟨367036178687400474133847765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244690785791600316089231843 367036178687400474133847765)
      ·
        refine ⟨8602410437985948612512057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 367036178687400474133847765 8602410437985948612512057)
        ·
          refine ⟨6451807828489461459384043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8602410437985948612512057 6451807828489461459384043)
          ·
            refine ⟨9677711742734192189076065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6451807828489461459384043 9677711742734192189076065)
            ·
              refine ⟨7258283807050644141807049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9677711742734192189076065 7258283807050644141807049)
              ·
                refine ⟨5443712855287983106355287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7258283807050644141807049 5443712855287983106355287)
                ·
                  refine ⟨8165569282931974659532931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5443712855287983106355287 8165569282931974659532931)
                  ·
                    refine ⟨12248353924397961989299397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8165569282931974659532931 12248353924397961989299397)
                    ·
                      refine ⟨2296566360824617872993637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12248353924397961989299397 2296566360824617872993637)
                      ·
                        rfl

theorem cell23_4472547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4472547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472547 prefixEnd_4472547 := by exact prefixLift 4472547
  have htrace : WordTrace (prefixWord ++ tailWord_4472547) baseStart_4472547 baseEnd_4472547 := by
    simpa [prefixWord, tailWord_4472547, baseEnd_4472547] using wordTrace_append hprefix tailTrace_4472547
  have hstable : (prefixWord ++ tailWord_4472547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472547).length < 2 ^ (prefixWord ++ tailWord_4472547).sum := by decide
  have hdescent : baseEnd_4472547 < baseStart_4472547 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472563 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3]
def baseStart_4472563 : Nat := 118140960795 + 4472563 * 2 ^ 59
def prefixEnd_4472563 : Nat := 4983230072969 + 3 ^ 40 * 4472563 * 2
def baseEnd_4472563 : Nat := 2296574576515089810393563

theorem tailTrace_4472563 : CollatzResearch.WordTrace tailWord_4472563 prefixEnd_4472563 2296574576515089810393563 := by
  unfold tailWord_4472563
  simp only [CollatzResearch.WordTrace]
  refine ⟨163127774095675578792070343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108751849397117052528046895 163127774095675578792070343)
  ·
    refine ⟨244691661143513368188105515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163127774095675578792070343 244691661143513368188105515)
    ·
      refine ⟨367037491715270052282158273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244691661143513368188105515 367037491715270052282158273)
      ·
        refine ⟨275278118786452539211618705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367037491715270052282158273 275278118786452539211618705)
        ·
          refine ⟨206458589089839404408714029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275278118786452539211618705 206458589089839404408714029)
          ·
            refine ⟨77421970908689776653267761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206458589089839404408714029 77421970908689776653267761)
            ·
              refine ⟨58066478181517332489950821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77421970908689776653267761 58066478181517332489950821)
              ·
                refine ⟨10887464659034499841865779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58066478181517332489950821 10887464659034499841865779)
                ·
                  refine ⟨16331196988551749762798669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10887464659034499841865779 16331196988551749762798669)
                  ·
                    refine ⟨6124198870706906161049501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16331196988551749762798669 6124198870706906161049501)
                    ·
                      refine ⟨2296574576515089810393563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124198870706906161049501 2296574576515089810393563)
                      ·
                        rfl

theorem cell23_4472563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_4472563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472563 prefixEnd_4472563 := by exact prefixLift 4472563
  have htrace : WordTrace (prefixWord ++ tailWord_4472563) baseStart_4472563 baseEnd_4472563 := by
    simpa [prefixWord, tailWord_4472563, baseEnd_4472563] using wordTrace_append hprefix tailTrace_4472563
  have hstable : (prefixWord ++ tailWord_4472563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472563).length < 2 ^ (prefixWord ++ tailWord_4472563).sum := by decide
  have hdescent : baseEnd_4472563 < baseStart_4472563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472564 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4472564 : Nat := 118140960795 + 4472564 * 2 ^ 59
def prefixEnd_4472564 : Nat := 4983230072969 + 3 ^ 40 * 4472564 * 2
def baseEnd_4472564 : Nat := 2296575089995744306481059

theorem tailTrace_4472564 : CollatzResearch.WordTrace tailWord_4472564 prefixEnd_4472564 2296575089995744306481059 := by
  unfold tailWord_4472564
  simp only [CollatzResearch.WordTrace]
  refine ⟨81563905284335977981428373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108751873712447970641904497 81563905284335977981428373)
  ·
    refine ⟨3823308060203248967879455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 81563905284335977981428373 3823308060203248967879455)
    ·
      refine ⟨5734962090304873451819183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3823308060203248967879455 5734962090304873451819183)
      ·
        refine ⟨8602443135457310177728775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5734962090304873451819183 8602443135457310177728775)
        ·
          refine ⟨12903664703185965266593163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8602443135457310177728775 12903664703185965266593163)
          ·
            refine ⟨19355497054778947899889745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12903664703185965266593163 19355497054778947899889745)
            ·
              refine ⟨14516622791084210924917309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19355497054778947899889745 14516622791084210924917309)
              ·
                refine ⟨5443733546656579096843991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14516622791084210924917309 5443733546656579096843991)
                ·
                  refine ⟨8165600319984868645265987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5443733546656579096843991 8165600319984868645265987)
                  ·
                    refine ⟨12248400479977302967898981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8165600319984868645265987 12248400479977302967898981)
                    ·
                      refine ⟨2296575089995744306481059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12248400479977302967898981 2296575089995744306481059)
                      ·
                        rfl

theorem cell23_4472564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4472564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472564 prefixEnd_4472564 := by exact prefixLift 4472564
  have htrace : WordTrace (prefixWord ++ tailWord_4472564) baseStart_4472564 baseEnd_4472564 := by
    simpa [prefixWord, tailWord_4472564, baseEnd_4472564] using wordTrace_append hprefix tailTrace_4472564
  have hstable : (prefixWord ++ tailWord_4472564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472564).length < 2 ^ (prefixWord ++ tailWord_4472564).sum := by decide
  have hdescent : baseEnd_4472564 < baseStart_4472564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472597 : List Nat := [1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_4472597 : Nat := 118140960795 + 4472597 * 2 ^ 59
def prefixEnd_4472597 : Nat := 4983230072969 + 3 ^ 40 * 4472597 * 2
def baseEnd_4472597 : Nat := 2296592034857342677368407

theorem tailTrace_4472597 : CollatzResearch.WordTrace tailWord_4472597 prefixEnd_4472597 2296592034857342677368407 := by
  unfold tailWord_4472597
  simp only [CollatzResearch.WordTrace]
  refine ⟨163129014177552402598808045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108752676118368268399205363 163129014177552402598808045)
  ·
    refine ⟨61173380316582150974553017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163129014177552402598808045 61173380316582150974553017)
    ·
      refine ⟨45880035237436613230914763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61173380316582150974553017 45880035237436613230914763)
      ·
        refine ⟨68820052856154919846372145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45880035237436613230914763 68820052856154919846372145)
        ·
          refine ⟨51615039642116189884779109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68820052856154919846372145 51615039642116189884779109)
          ·
            refine ⟨9677819932896785603396083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51615039642116189884779109 9677819932896785603396083)
            ·
              refine ⟨14516729899345178405094125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677819932896785603396083 14516729899345178405094125)
              ·
                refine ⟨5443773712254441901910297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14516729899345178405094125 5443773712254441901910297)
                ·
                  refine ⟨4082830284190831426432723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5443773712254441901910297 4082830284190831426432723)
                  ·
                    refine ⟨6124245426286247139649085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4082830284190831426432723 6124245426286247139649085)
                    ·
                      refine ⟨2296592034857342677368407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124245426286247139649085 2296592034857342677368407)
                      ·
                        rfl

theorem cell23_4472597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_4472597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472597 prefixEnd_4472597 := by exact prefixLift 4472597
  have htrace : WordTrace (prefixWord ++ tailWord_4472597) baseStart_4472597 baseEnd_4472597 := by
    simpa [prefixWord, tailWord_4472597, baseEnd_4472597] using wordTrace_append hprefix tailTrace_4472597
  have hstable : (prefixWord ++ tailWord_4472597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472597).length < 2 ^ (prefixWord ++ tailWord_4472597).sum := by decide
  have hdescent : baseEnd_4472597 < baseStart_4472597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472620 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 3, 4, 2]
def baseStart_4472620 : Nat := 118140960795 + 4472620 * 2 ^ 59
def prefixEnd_4472620 : Nat := 4983230072969 + 3 ^ 40 * 4472620 * 2
def baseEnd_4472620 : Nat := 2296603844912396087380801

theorem tailTrace_4472620 : CollatzResearch.WordTrace tailWord_4472620 prefixEnd_4472620 2296603844912396087380801 := by
  unfold tailWord_4472620
  simp only [CollatzResearch.WordTrace]
  refine ⟨81564926528234538763447657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108753235370979385017930209 81564926528234538763447657)
  ·
    refine ⟨61173694896175904072585743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81564926528234538763447657 61173694896175904072585743)
    ·
      refine ⟨91760542344263856108878615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61173694896175904072585743 91760542344263856108878615)
      ·
        refine ⟨137640813516395784163317923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91760542344263856108878615 137640813516395784163317923)
        ·
          refine ⟨206461220274593676244976885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137640813516395784163317923 206461220274593676244976885)
          ·
            refine ⟨19355739400743157147966583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 206461220274593676244976885 19355739400743157147966583)
            ·
              refine ⟨29033609101114735721949875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19355739400743157147966583 29033609101114735721949875)
              ·
                refine ⟨43550413651672103582924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29033609101114735721949875 43550413651672103582924813)
                ·
                  refine ⟨16331405119377038843596805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43550413651672103582924813 16331405119377038843596805)
                  ·
                    refine ⟨3062138459883194783174401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16331405119377038843596805 3062138459883194783174401)
                    ·
                      refine ⟨2296603844912396087380801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062138459883194783174401 2296603844912396087380801)
                      ·
                        rfl

theorem cell23_4472620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_4472620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472620 prefixEnd_4472620 := by exact prefixLift 4472620
  have htrace : WordTrace (prefixWord ++ tailWord_4472620) baseStart_4472620 baseEnd_4472620 := by
    simpa [prefixWord, tailWord_4472620, baseEnd_4472620] using wordTrace_append hprefix tailTrace_4472620
  have hstable : (prefixWord ++ tailWord_4472620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472620).length < 2 ^ (prefixWord ++ tailWord_4472620).sum := by decide
  have hdescent : baseEnd_4472620 < baseStart_4472620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472660 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 7]
def baseStart_4472660 : Nat := 118140960795 + 4472660 * 2 ^ 59
def prefixEnd_4472660 : Nat := 4983230072969 + 3 ^ 40 * 4472660 * 2
def baseEnd_4472660 : Nat := 255180487126508436764513

theorem tailTrace_4472660 : CollatzResearch.WordTrace tailWord_4472660 prefixEnd_4472660 255180487126508436764513 := by
  unfold tailWord_4472660
  simp only [CollatzResearch.WordTrace]
  refine ⟨81565655988162082179175717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108754207984216109572234289 81565655988162082179175717)
  ·
    refine ⟨15293560497780390408595447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81565655988162082179175717 15293560497780390408595447)
    ·
      refine ⟨22940340746670585612893171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15293560497780390408595447 22940340746670585612893171)
      ·
        refine ⟨34410511120005878419339757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22940340746670585612893171 34410511120005878419339757)
        ·
          refine ⟨12903941670002204407252409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34410511120005878419339757 12903941670002204407252409)
          ·
            refine ⟨9677956252501653305439307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12903941670002204407252409 9677956252501653305439307)
            ·
              refine ⟨14516934378752479958158961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9677956252501653305439307 14516934378752479958158961)
              ·
                refine ⟨10887700784064359968619221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14516934378752479958158961 10887700784064359968619221)
                ·
                  refine ⟨255180487126508436764513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10887700784064359968619221 255180487126508436764513)
                  ·
                    rfl

theorem cell23_4472660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_4472660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472660 prefixEnd_4472660 := by exact prefixLift 4472660
  have htrace : WordTrace (prefixWord ++ tailWord_4472660) baseStart_4472660 baseEnd_4472660 := by
    simpa [prefixWord, tailWord_4472660, baseEnd_4472660] using wordTrace_append hprefix tailTrace_4472660
  have hstable : (prefixWord ++ tailWord_4472660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472660).length < 2 ^ (prefixWord ++ tailWord_4472660).sum := by decide
  have hdescent : baseEnd_4472660 < baseStart_4472660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472673 : List Nat := [1, 2, 3, 1, 1, 1, 5, 1, 1, 7]
def baseStart_4472673 : Nat := 118140960795 + 4472673 * 2 ^ 59
def prefixEnd_4472673 : Nat := 4983230072969 + 3 ^ 40 * 4472673 * 2
def baseEnd_4472673 : Nat := 765543686462361460006019

theorem tailTrace_4472673 : CollatzResearch.WordTrace tailWord_4472673 prefixEnd_4472673 765543686462361460006019 := by
  unfold tailWord_4472673
  simp only [CollatzResearch.WordTrace]
  refine ⟨163131786125277067578574673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108754524083518045052383115 163131786125277067578574673)
  ·
    refine ⟨122348839593957800683931005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163131786125277067578574673 122348839593957800683931005)
    ·
      refine ⟨45880814847734175256474127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122348839593957800683931005 45880814847734175256474127)
      ·
        refine ⟨68821222271601262884711191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45880814847734175256474127 68821222271601262884711191)
        ·
          refine ⟨103231833407401894327066787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68821222271601262884711191 103231833407401894327066787)
          ·
            refine ⟨154847750111102841490600181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103231833407401894327066787 154847750111102841490600181)
            ·
              refine ⟨14516976572915891389743767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154847750111102841490600181 14516976572915891389743767)
              ·
                refine ⟨21775464859373837084615651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14516976572915891389743767 21775464859373837084615651)
                ·
                  refine ⟨32663197289060755626923477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21775464859373837084615651 32663197289060755626923477)
                  ·
                    refine ⟨765543686462361460006019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32663197289060755626923477 765543686462361460006019)
                    ·
                      rfl

theorem cell23_4472673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_4472673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472673 prefixEnd_4472673 := by exact prefixLift 4472673
  have htrace : WordTrace (prefixWord ++ tailWord_4472673) baseStart_4472673 baseEnd_4472673 := by
    simpa [prefixWord, tailWord_4472673, baseEnd_4472673] using wordTrace_append hprefix tailTrace_4472673
  have hstable : (prefixWord ++ tailWord_4472673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472673).length < 2 ^ (prefixWord ++ tailWord_4472673).sum := by decide
  have hdescent : baseEnd_4472673 < baseStart_4472673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472773 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_4472773 : Nat := 118140960795 + 4472773 * 2 ^ 59
def prefixEnd_4472773 : Nat := 4983230072969 + 3 ^ 40 * 4472773 * 2
def baseEnd_4472773 : Nat := 2296682407452533988767597

theorem tailTrace_4472773 : CollatzResearch.WordTrace tailWord_4472773 prefixEnd_4472773 2296682407452533988767597 := by
  unfold tailWord_4472773
  simp only [CollatzResearch.WordTrace]
  refine ⟨163135433424914784657214973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108756955616609856438143315 163135433424914784657214973)
  ·
    refine ⟨61175787534343044246455615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163135433424914784657214973 61175787534343044246455615)
    ·
      refine ⟨91763681301514566369683423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61175787534343044246455615 91763681301514566369683423)
      ·
        refine ⟨137645521952271849554525135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91763681301514566369683423 137645521952271849554525135)
        ·
          refine ⟨206468282928407774331787703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137645521952271849554525135 206468282928407774331787703)
          ·
            refine ⟨309702424392611661497681555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206468282928407774331787703 309702424392611661497681555)
            ·
              refine ⟨464553636588917492246522333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309702424392611661497681555 464553636588917492246522333)
              ·
                refine ⟨174207613720844059592445875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 464553636588917492246522333 174207613720844059592445875)
                ·
                  refine ⟨261311420581266089388668813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 174207613720844059592445875 261311420581266089388668813)
                  ·
                    refine ⟨97991782717974783520750805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 261311420581266089388668813 97991782717974783520750805)
                    ·
                      refine ⟨2296682407452533988767597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 97991782717974783520750805 2296682407452533988767597)
                      ·
                        rfl

theorem cell23_4472773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_4472773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472773 prefixEnd_4472773 := by exact prefixLift 4472773
  have htrace : WordTrace (prefixWord ++ tailWord_4472773) baseStart_4472773 baseEnd_4472773 := by
    simpa [prefixWord, tailWord_4472773, baseEnd_4472773] using wordTrace_append hprefix tailTrace_4472773
  have hstable : (prefixWord ++ tailWord_4472773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472773).length < 2 ^ (prefixWord ++ tailWord_4472773).sum := by decide
  have hdescent : baseEnd_4472773 < baseStart_4472773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472810 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 3, 6]
def baseStart_4472810 : Nat := 118140960795 + 4472810 * 2 ^ 59
def prefixEnd_4472810 : Nat := 4983230072969 + 3 ^ 40 * 4472810 * 2
def baseEnd_4472810 : Nat := 765567135412250114668309

theorem tailTrace_4472810 : CollatzResearch.WordTrace tailWord_4472810 prefixEnd_4472810 765567135412250114668309 := by
  unfold tailWord_4472810
  simp only [CollatzResearch.WordTrace]
  refine ⟨40784195731445184994077971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108757855283853826650874589 40784195731445184994077971)
  ·
    refine ⟨61176293597167777491116957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40784195731445184994077971 61176293597167777491116957)
    ·
      refine ⟨22941110098937916559168859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61176293597167777491116957 22941110098937916559168859)
      ·
        refine ⟨34411665148406874838753289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22941110098937916559168859 34411665148406874838753289)
        ·
          refine ⟨25808748861305156129064967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34411665148406874838753289 25808748861305156129064967)
          ·
            refine ⟨38713123291957734193597451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25808748861305156129064967 38713123291957734193597451)
            ·
              refine ⟨58069684937936601290396177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38713123291957734193597451 58069684937936601290396177)
              ·
                refine ⟨43552263703452450967797133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58069684937936601290396177 43552263703452450967797133)
                ·
                  refine ⟨16332098888794669112923925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43552263703452450967797133 16332098888794669112923925)
                  ·
                    refine ⟨765567135412250114668309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16332098888794669112923925 765567135412250114668309)
                    ·
                      rfl

theorem cell23_4472810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_4472810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472810 prefixEnd_4472810 := by exact prefixLift 4472810
  have htrace : WordTrace (prefixWord ++ tailWord_4472810) baseStart_4472810 baseEnd_4472810 := by
    simpa [prefixWord, tailWord_4472810, baseEnd_4472810] using wordTrace_append hprefix tailTrace_4472810
  have hstable : (prefixWord ++ tailWord_4472810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472810).length < 2 ^ (prefixWord ++ tailWord_4472810).sum := by decide
  have hdescent : baseEnd_4472810 < baseStart_4472810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472827 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 2, 4]
def baseStart_4472827 : Nat := 118140960795 + 4472827 * 2 ^ 59
def prefixEnd_4472827 : Nat := 4983230072969 + 3 ^ 40 * 4472827 * 2
def baseEnd_4472827 : Nat := 765570045135958925830783

theorem tailTrace_4472827 : CollatzResearch.WordTrace tailWord_4472827 prefixEnd_4472827 765570045135958925830783 := by
  unfold tailWord_4472827
  simp only [CollatzResearch.WordTrace]
  refine ⟨163137402966719151879680735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108758268644479434586453823 163137402966719151879680735)
  ·
    refine ⟨244706104450078727819521103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163137402966719151879680735 244706104450078727819521103)
    ·
      refine ⟨367059156675118091729281655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244706104450078727819521103 367059156675118091729281655)
      ·
        refine ⟨550588735012677137593922483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367059156675118091729281655 550588735012677137593922483)
        ·
          refine ⟨825883102519015706390883725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550588735012677137593922483 825883102519015706390883725)
          ·
            refine ⟨309706163444630889896581397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 825883102519015706390883725 309706163444630889896581397)
            ·
              refine ⟨14517476411467072963902253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 309706163444630889896581397 14517476411467072963902253)
              ·
                refine ⟨5444053654300152361463345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14517476411467072963902253 5444053654300152361463345)
                ·
                  refine ⟨4083040240725114271097509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5444053654300152361463345 4083040240725114271097509)
                  ·
                    refine ⟨765570045135958925830783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083040240725114271097509 765570045135958925830783)
                    ·
                      rfl

theorem cell23_4472827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 2, 4].length) (baseStart_4472827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472827 prefixEnd_4472827 := by exact prefixLift 4472827
  have htrace : WordTrace (prefixWord ++ tailWord_4472827) baseStart_4472827 baseEnd_4472827 := by
    simpa [prefixWord, tailWord_4472827, baseEnd_4472827] using wordTrace_append hprefix tailTrace_4472827
  have hstable : (prefixWord ++ tailWord_4472827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472827).length < 2 ^ (prefixWord ++ tailWord_4472827).sum := by decide
  have hdescent : baseEnd_4472827 < baseStart_4472827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472837 : List Nat := [1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_4472837 : Nat := 118140960795 + 4472837 * 2 ^ 59
def prefixEnd_4472837 : Nat := 4983230072969 + 3 ^ 40 * 4472837 * 2
def baseEnd_4472837 : Nat := 2296715270214421738367303

theorem tailTrace_4472837 : CollatzResearch.WordTrace tailWord_4472837 prefixEnd_4472837 2296715270214421738367303 := by
  unfold tailWord_4472837
  simp only [CollatzResearch.WordTrace]
  refine ⟨163137767696682923587544765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108758511797788615725029843 163137767696682923587544765)
  ·
    refine ⟨61176662886256096345329287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163137767696682923587544765 61176662886256096345329287)
    ·
      refine ⟨91764994329384144517993931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61176662886256096345329287 91764994329384144517993931)
      ·
        refine ⟨137647491494076216776990897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91764994329384144517993931 137647491494076216776990897)
        ·
          refine ⟨103235618620557162582743173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137647491494076216776990897 103235618620557162582743173)
          ·
            refine ⟨19356678491354467984264345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103235618620557162582743173 19356678491354467984264345)
            ·
              refine ⟨14517508868515850988198259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19356678491354467984264345 14517508868515850988198259)
              ·
                refine ⟨21776263302773776482297389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14517508868515850988198259 21776263302773776482297389)
                ·
                  refine ⟨8166098738540166180861521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21776263302773776482297389 8166098738540166180861521)
                  ·
                    refine ⟨6124574053905124635646141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8166098738540166180861521 6124574053905124635646141)
                    ·
                      refine ⟨2296715270214421738367303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124574053905124635646141 2296715270214421738367303)
                      ·
                        rfl

theorem cell23_4472837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_4472837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472837 prefixEnd_4472837 := by exact prefixLift 4472837
  have htrace : WordTrace (prefixWord ++ tailWord_4472837) baseStart_4472837 baseEnd_4472837 := by
    simpa [prefixWord, tailWord_4472837, baseEnd_4472837] using wordTrace_append hprefix tailTrace_4472837
  have hstable : (prefixWord ++ tailWord_4472837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472837).length < 2 ^ (prefixWord ++ tailWord_4472837).sum := by decide
  have hdescent : baseEnd_4472837 < baseStart_4472837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472851 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 1, 2, 2]
def baseStart_4472851 : Nat := 118140960795 + 4472851 * 2 ^ 59
def prefixEnd_4472851 : Nat := 4983230072969 + 3 ^ 40 * 4472851 * 2
def baseEnd_4472851 : Nat := 2296722458943584683592239

theorem tailTrace_4472851 : CollatzResearch.WordTrace tailWord_4472851 prefixEnd_4472851 2296722458943584683592239 := by
  unfold tailWord_4472851
  simp only [CollatzResearch.WordTrace]
  refine ⟨163138278318632203978554407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108758852212421469319036271 163138278318632203978554407)
  ·
    refine ⟨244707417477948305967831611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163138278318632203978554407 244707417477948305967831611)
    ·
      refine ⟨367061126216922458951747417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244707417477948305967831611 367061126216922458951747417)
      ·
        refine ⟨275295844662691844213810563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367061126216922458951747417 275295844662691844213810563)
        ·
          refine ⟨412943766994037766320715845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275295844662691844213810563 412943766994037766320715845)
          ·
            refine ⟨77426956311382081185134221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 412943766994037766320715845 77426956311382081185134221)
            ·
              refine ⟨29035108616768280444425333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77426956311382081185134221 29035108616768280444425333)
              ·
                refine ⟨2722041432822026291664875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29035108616768280444425333 2722041432822026291664875)
                ·
                  refine ⟨4083062149233039437497313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722041432822026291664875 4083062149233039437497313)
                  ·
                    refine ⟨3062296611924779578122985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083062149233039437497313 3062296611924779578122985)
                    ·
                      refine ⟨2296722458943584683592239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062296611924779578122985 2296722458943584683592239)
                      ·
                        rfl

theorem cell23_4472851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 1, 2, 2].length) (baseStart_4472851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472851 prefixEnd_4472851 := by exact prefixLift 4472851
  have htrace : WordTrace (prefixWord ++ tailWord_4472851) baseStart_4472851 baseEnd_4472851 := by
    simpa [prefixWord, tailWord_4472851, baseEnd_4472851] using wordTrace_append hprefix tailTrace_4472851
  have hstable : (prefixWord ++ tailWord_4472851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472851).length < 2 ^ (prefixWord ++ tailWord_4472851).sum := by decide
  have hdescent : baseEnd_4472851 < baseStart_4472851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472861 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4472861 : Nat := 118140960795 + 4472861 * 2 ^ 59
def prefixEnd_4472861 : Nat := 4983230072969 + 3 ^ 40 * 4472861 * 2
def baseEnd_4472861 : Nat := 765575864583376548155731

theorem tailTrace_4472861 : CollatzResearch.WordTrace tailWord_4472861 prefixEnd_4472861 765575864583376548155731 := by
  unfold tailWord_4472861
  simp only [CollatzResearch.WordTrace]
  refine ⟨163138643048595975686418437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108759095365730650457612291 163138643048595975686418437)
  ·
    refine ⟨30588495571611745441203457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163138643048595975686418437 30588495571611745441203457)
    ·
      refine ⟨22941371678708809080902593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30588495571611745441203457 22941371678708809080902593)
      ·
        refine ⟨17206028759031606810676945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22941371678708809080902593 17206028759031606810676945)
        ·
          refine ⟨12904521569273705108007709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17206028759031606810676945 12904521569273705108007709)
          ·
            refine ⟨4839195588477639415502891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12904521569273705108007709 4839195588477639415502891)
            ·
              refine ⟨7258793382716459123254337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839195588477639415502891 7258793382716459123254337)
              ·
                refine ⟨5444095037037344342440753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7258793382716459123254337 5444095037037344342440753)
                ·
                  refine ⟨4083071277778008256830565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5444095037037344342440753 4083071277778008256830565)
                  ·
                    refine ⟨765575864583376548155731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083071277778008256830565 765575864583376548155731)
                    ·
                      rfl

theorem cell23_4472861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4472861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472861 prefixEnd_4472861 := by exact prefixLift 4472861
  have htrace : WordTrace (prefixWord ++ tailWord_4472861) baseStart_4472861 baseEnd_4472861 := by
    simpa [prefixWord, tailWord_4472861, baseEnd_4472861] using wordTrace_append hprefix tailTrace_4472861
  have hstable : (prefixWord ++ tailWord_4472861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472861).length < 2 ^ (prefixWord ++ tailWord_4472861).sum := by decide
  have hdescent : baseEnd_4472861 < baseStart_4472861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472868 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4472868 : Nat := 118140960795 + 4472868 * 2 ^ 59
def prefixEnd_4472868 : Nat := 4983230072969 + 3 ^ 40 * 4472868 * 2
def baseEnd_4472868 : Nat := 2296731188114711117079661

theorem tailTrace_4472868 : CollatzResearch.WordTrace tailWord_4472868 prefixEnd_4472868 2296731188114711117079661 := by
  unfold tailWord_4472868
  simp only [CollatzResearch.WordTrace]
  refine ⟨81569449179785307940961629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108759265573047077254615505 81569449179785307940961629)
  ·
    refine ⟨30588543442419490477860611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81569449179785307940961629 30588543442419490477860611)
    ·
      refine ⟨45882815163629235716790917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30588543442419490477860611 45882815163629235716790917)
      ·
        refine ⟨8603027843180481696898297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45882815163629235716790917 8603027843180481696898297)
        ·
          refine ⟨6452270882385361272673723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8603027843180481696898297 6452270882385361272673723)
          ·
            refine ⟨9678406323578041909010585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6452270882385361272673723 9678406323578041909010585)
            ·
              refine ⟨7258804742683531431757939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9678406323578041909010585 7258804742683531431757939)
              ·
                refine ⟨10888207114025297147636909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7258804742683531431757939 10888207114025297147636909)
                ·
                  refine ⟨4083077667759486430363841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10888207114025297147636909 4083077667759486430363841)
                  ·
                    refine ⟨3062308250819614822772881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083077667759486430363841 3062308250819614822772881)
                    ·
                      refine ⟨2296731188114711117079661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062308250819614822772881 2296731188114711117079661)
                      ·
                        rfl

theorem cell23_4472868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4472868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472868 prefixEnd_4472868 := by exact prefixLift 4472868
  have htrace : WordTrace (prefixWord ++ tailWord_4472868) baseStart_4472868 baseEnd_4472868 := by
    simpa [prefixWord, tailWord_4472868, baseEnd_4472868] using wordTrace_append hprefix tailTrace_4472868
  have hstable : (prefixWord ++ tailWord_4472868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472868).length < 2 ^ (prefixWord ++ tailWord_4472868).sum := by decide
  have hdescent : baseEnd_4472868 < baseStart_4472868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472897 : List Nat := [1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4472897 : Nat := 118140960795 + 4472897 * 2 ^ 59
def prefixEnd_4472897 : Nat := 4983230072969 + 3 ^ 40 * 4472897 * 2
def baseEnd_4472897 : Nat := 2296746079053691503617027

theorem tailTrace_4472897 : CollatzResearch.WordTrace tailWord_4472897 prefixEnd_4472897 2296746079053691503617027 := by
  unfold tailWord_4472897
  simp only [CollatzResearch.WordTrace]
  refine ⟨163139956076465553834728945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108759970717643702556485963 163139956076465553834728945)
  ·
    refine ⟨122354967057349165376046709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163139956076465553834728945 122354967057349165376046709)
    ·
      refine ⟨11470778161626484254004379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122354967057349165376046709 11470778161626484254004379)
      ·
        refine ⟨17206167242439726381006569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11470778161626484254004379 17206167242439726381006569)
        ·
          refine ⟨12904625431829794785754927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17206167242439726381006569 12904625431829794785754927)
          ·
            refine ⟨19356938147744692178632391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12904625431829794785754927 19356938147744692178632391)
            ·
              refine ⟨29035407221617038267948587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19356938147744692178632391 29035407221617038267948587)
              ·
                refine ⟨43553110832425557401922881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29035407221617038267948587 43553110832425557401922881)
                ·
                  refine ⟨32664833124319168051442161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43553110832425557401922881 32664833124319168051442161)
                  ·
                    refine ⟨24498624843239376038581621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32664833124319168051442161 24498624843239376038581621)
                    ·
                      refine ⟨2296746079053691503617027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24498624843239376038581621 2296746079053691503617027)
                      ·
                        rfl

theorem cell23_4472897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4472897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472897 prefixEnd_4472897 := by exact prefixLift 4472897
  have htrace : WordTrace (prefixWord ++ tailWord_4472897) baseStart_4472897 baseEnd_4472897 := by
    simpa [prefixWord, tailWord_4472897, baseEnd_4472897] using wordTrace_append hprefix tailTrace_4472897
  have hstable : (prefixWord ++ tailWord_4472897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472897).length < 2 ^ (prefixWord ++ tailWord_4472897).sum := by decide
  have hdescent : baseEnd_4472897 < baseStart_4472897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472918 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4472918 : Nat := 118140960795 + 4472918 * 2 ^ 59
def prefixEnd_4472918 : Nat := 4983230072969 + 3 ^ 40 * 4472918 * 2
def baseEnd_4472918 : Nat := 2296756862147435921454431

theorem tailTrace_4472918 : CollatzResearch.WordTrace tailWord_4472918 prefixEnd_4472918 2296756862147435921454431 := by
  unfold tailWord_4472918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10196295125586842151327713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108760481339592982947495605 10196295125586842151327713)
  ·
    refine ⟨7647221344190131613495785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10196295125586842151327713 7647221344190131613495785)
    ·
      refine ⟨5735416008142598710121839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7647221344190131613495785 5735416008142598710121839)
      ·
        refine ⟨8603124012213898065182759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5735416008142598710121839 8603124012213898065182759)
        ·
          refine ⟨12904686018320847097774139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8603124012213898065182759 12904686018320847097774139)
          ·
            refine ⟨19357029027481270646661209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12904686018320847097774139 19357029027481270646661209)
            ·
              refine ⟨14517771770610952984995907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19357029027481270646661209 14517771770610952984995907)
              ·
                refine ⟨21776657655916429477493861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14517771770610952984995907 21776657655916429477493861)
                ·
                  refine ⟨4083123310484330527030099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21776657655916429477493861 4083123310484330527030099)
                  ·
                    refine ⟨6124684965726495790545149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083123310484330527030099 6124684965726495790545149)
                    ·
                      refine ⟨2296756862147435921454431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124684965726495790545149 2296756862147435921454431)
                      ·
                        rfl

theorem cell23_4472918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4472918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472918 prefixEnd_4472918 := by exact prefixLift 4472918
  have htrace : WordTrace (prefixWord ++ tailWord_4472918) baseStart_4472918 baseEnd_4472918 := by
    simpa [prefixWord, tailWord_4472918, baseEnd_4472918] using wordTrace_append hprefix tailTrace_4472918
  have hstable : (prefixWord ++ tailWord_4472918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472918).length < 2 ^ (prefixWord ++ tailWord_4472918).sum := by decide
  have hdescent : baseEnd_4472918 < baseStart_4472918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472964 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 5]
def baseStart_4472964 : Nat := 118140960795 + 4472964 * 2 ^ 59
def prefixEnd_4472964 : Nat := 4983230072969 + 3 ^ 40 * 4472964 * 2
def baseEnd_4472964 : Nat := 255197831361949193497691

theorem tailTrace_4472964 : CollatzResearch.WordTrace tailWord_4472964 prefixEnd_4472964 255197831361949193497691 := by
  unfold tailWord_4472964
  simp only [CollatzResearch.WordTrace]
  refine ⟨81571199883611412138708973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108761599844815216184945297 81571199883611412138708973)
  ·
    refine ⟨30589199956354279552015865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81571199883611412138708973 30589199956354279552015865)
    ·
      refine ⟨22941899967265709664011899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30589199956354279552015865 22941899967265709664011899)
      ·
        refine ⟨34412849950898564496017849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22941899967265709664011899 34412849950898564496017849)
        ·
          refine ⟨25809637463173923372013387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34412849950898564496017849 25809637463173923372013387)
          ·
            refine ⟨38714456194760885058020081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25809637463173923372013387 38714456194760885058020081)
            ·
              refine ⟨29035842146070663793515061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38714456194760885058020081 29035842146070663793515061)
              ·
                refine ⟨2722110201194124730642037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29035842146070663793515061 2722110201194124730642037)
                ·
                  refine ⟨255197831361949193497691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722110201194124730642037 255197831361949193497691)
                  ·
                    rfl

theorem cell23_4472964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_4472964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472964 prefixEnd_4472964 := by exact prefixLift 4472964
  have htrace : WordTrace (prefixWord ++ tailWord_4472964) baseStart_4472964 baseEnd_4472964 := by
    simpa [prefixWord, tailWord_4472964, baseEnd_4472964] using wordTrace_append hprefix tailTrace_4472964
  have hstable : (prefixWord ++ tailWord_4472964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472964).length < 2 ^ (prefixWord ++ tailWord_4472964).sum := by decide
  have hdescent : baseEnd_4472964 < baseStart_4472964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4472997 : List Nat := [1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_4472997 : Nat := 118140960795 + 4472997 * 2 ^ 59
def prefixEnd_4472997 : Nat := 4983230072969 + 3 ^ 40 * 4472997 * 2
def baseEnd_4472997 : Nat := 2296797427119141112366567

theorem tailTrace_4472997 : CollatzResearch.WordTrace tailWord_4472997 prefixEnd_4472997 2296797427119141112366567 := by
  unfold tailWord_4472997
  simp only [CollatzResearch.WordTrace]
  refine ⟨163143603376103270913369245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108762402250735513942246163 163143603376103270913369245)
  ·
    refine ⟨61178851266038726592513467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163143603376103270913369245 61178851266038726592513467)
    ·
      refine ⟨91768276899058089888770201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61178851266038726592513467 91768276899058089888770201)
      ·
        refine ⟨68826207674293567416577651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91768276899058089888770201 68826207674293567416577651)
        ·
          refine ⟨103239311511440351124866477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68826207674293567416577651 103239311511440351124866477)
          ·
            refine ⟨38714741816790131671824929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103239311511440351124866477 38714741816790131671824929)
            ·
              refine ⟨29036056362592598753868697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38714741816790131671824929 29036056362592598753868697)
              ·
                refine ⟨21777042271944449065401523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29036056362592598753868697 21777042271944449065401523)
                ·
                  refine ⟨32665563407916673598102285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21777042271944449065401523 32665563407916673598102285)
                  ·
                    refine ⟨12249586277968752599288357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32665563407916673598102285 12249586277968752599288357)
                    ·
                      refine ⟨2296797427119141112366567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12249586277968752599288357 2296797427119141112366567)
                      ·
                        rfl

theorem cell23_4472997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_4472997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4472997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4472997 prefixEnd_4472997 := by exact prefixLift 4472997
  have htrace : WordTrace (prefixWord ++ tailWord_4472997) baseStart_4472997 baseEnd_4472997 := by
    simpa [prefixWord, tailWord_4472997, baseEnd_4472997] using wordTrace_append hprefix tailTrace_4472997
  have hstable : (prefixWord ++ tailWord_4472997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4472997).length < 2 ^ (prefixWord ++ tailWord_4472997).sum := by decide
  have hdescent : baseEnd_4472997 < baseStart_4472997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4472997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473034 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_4473034 : Nat := 118140960795 + 4473034 * 2 ^ 59
def prefixEnd_4473034 : Nat := 4983230072969 + 3 ^ 40 * 4473034 * 2
def baseEnd_4473034 : Nat := 2296816425903357467603897

theorem tailTrace_4473034 : CollatzResearch.WordTrace tailWord_4473034 prefixEnd_4473034 2296816425903357467603897 := by
  unfold tailWord_4473034
  simp only [CollatzResearch.WordTrace]
  refine ⟨40786238219242306558116539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108763301917979484154977437 40786238219242306558116539)
  ·
    refine ⟨61179357328863459837174809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40786238219242306558116539 61179357328863459837174809)
    ·
      refine ⟨45884517996647594877881107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61179357328863459837174809 45884517996647594877881107)
      ·
        refine ⟨68826776994971392316821661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45884517996647594877881107 68826776994971392316821661)
        ·
          refine ⟨25810041373114272118808123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68826776994971392316821661 25810041373114272118808123)
          ·
            refine ⟨38715062059671408178212185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25810041373114272118808123 38715062059671408178212185)
            ·
              refine ⟨29036296544753556133659139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38715062059671408178212185 29036296544753556133659139)
              ·
                refine ⟨43554444817130334200488709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29036296544753556133659139 43554444817130334200488709)
                ·
                  refine ⟨8166458403211937662591633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43554444817130334200488709 8166458403211937662591633)
                  ·
                    refine ⟨6124843802408953246943725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8166458403211937662591633 6124843802408953246943725)
                    ·
                      refine ⟨2296816425903357467603897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124843802408953246943725 2296816425903357467603897)
                      ·
                        rfl

theorem cell23_4473034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_4473034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473034 prefixEnd_4473034 := by exact prefixLift 4473034
  have htrace : WordTrace (prefixWord ++ tailWord_4473034) baseStart_4473034 baseEnd_4473034 := by
    simpa [prefixWord, tailWord_4473034, baseEnd_4473034] using wordTrace_append hprefix tailTrace_4473034
  have hstable : (prefixWord ++ tailWord_4473034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473034).length < 2 ^ (prefixWord ++ tailWord_4473034).sum := by decide
  have hdescent : baseEnd_4473034 < baseStart_4473034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473041 : List Nat := [1, 2, 2, 1, 2, 2, 4, 4, 1, 4]
def baseStart_4473041 : Nat := 118140960795 + 4473041 * 2 ^ 59
def prefixEnd_4473041 : Nat := 4983230072969 + 3 ^ 40 * 4473041 * 2
def baseEnd_4473041 : Nat := 765606673422646313405455

theorem tailTrace_4473041 : CollatzResearch.WordTrace tailWord_4473041 prefixEnd_4473041 765606673422646313405455 := by
  unfold tailWord_4473041
  simp only [CollatzResearch.WordTrace]
  refine ⟨163145208187943866427970977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108763472125295910951980651 163145208187943866427970977)
  ·
    refine ⟨122358906140957899820978233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163145208187943866427970977 122358906140957899820978233)
    ·
      refine ⟨91769179605718424865733675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122358906140957899820978233 91769179605718424865733675)
      ·
        refine ⟨137653769408577637298600513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91769179605718424865733675 137653769408577637298600513)
        ·
          refine ⟨103240327056433227973950385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137653769408577637298600513 103240327056433227973950385)
          ·
            refine ⟨77430245292324920980462789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103240327056433227973950385 77430245292324920980462789)
            ·
              refine ⟨14518170992310922683836773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77430245292324920980462789 14518170992310922683836773)
              ·
                refine ⟨2722157061058298003219395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14518170992310922683836773 2722157061058298003219395)
                ·
                  refine ⟨4083235591587447004829093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722157061058298003219395 4083235591587447004829093)
                  ·
                    refine ⟨765606673422646313405455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083235591587447004829093 765606673422646313405455)
                    ·
                      rfl

theorem cell23_4473041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 4, 1, 4].length) (baseStart_4473041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473041 prefixEnd_4473041 := by exact prefixLift 4473041
  have htrace : WordTrace (prefixWord ++ tailWord_4473041) baseStart_4473041 baseEnd_4473041 := by
    simpa [prefixWord, tailWord_4473041, baseEnd_4473041] using wordTrace_append hprefix tailTrace_4473041
  have hstable : (prefixWord ++ tailWord_4473041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473041).length < 2 ^ (prefixWord ++ tailWord_4473041).sum := by decide
  have hdescent : baseEnd_4473041 < baseStart_4473041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473057 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_4473057 : Nat := 118140960795 + 4473057 * 2 ^ 59
def prefixEnd_4473057 : Nat := 4983230072969 + 3 ^ 40 * 4473057 * 2
def baseEnd_4473057 : Nat := 2296828235958410877616291

theorem tailTrace_4473057 : CollatzResearch.WordTrace tailWord_4473057 prefixEnd_4473057 2296828235958410877616291 := by
  unfold tailWord_4473057
  simp only [CollatzResearch.WordTrace]
  refine ⟨163145791755885901160553425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108763861170590600773702283 163145791755885901160553425)
  ·
    refine ⟨122359343816914425870415069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163145791755885901160553425 122359343816914425870415069)
    ·
      refine ⟨45884753931342909701405651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122359343816914425870415069 45884753931342909701405651)
      ·
        refine ⟨68827130897014364552108477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45884753931342909701405651 68827130897014364552108477)
        ·
          refine ⟨25810174086380386707040679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68827130897014364552108477 25810174086380386707040679)
          ·
            refine ⟨38715261129570580060561019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25810174086380386707040679 38715261129570580060561019)
            ·
              refine ⟨58072891694355870090841529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38715261129570580060561019 58072891694355870090841529)
              ·
                refine ⟨43554668770766902568131147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58072891694355870090841529 43554668770766902568131147)
                ·
                  refine ⟨65332003156150353852196721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43554668770766902568131147 65332003156150353852196721)
                  ·
                    refine ⟨48999002367112765389147541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 65332003156150353852196721 48999002367112765389147541)
                    ·
                      refine ⟨2296828235958410877616291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48999002367112765389147541 2296828235958410877616291)
                      ·
                        rfl

theorem cell23_4473057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_4473057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473057 prefixEnd_4473057 := by exact prefixLift 4473057
  have htrace : WordTrace (prefixWord ++ tailWord_4473057) baseStart_4473057 baseEnd_4473057 := by
    simpa [prefixWord, tailWord_4473057, baseEnd_4473057] using wordTrace_append hprefix tailTrace_4473057
  have hstable : (prefixWord ++ tailWord_4473057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473057).length < 2 ^ (prefixWord ++ tailWord_4473057).sum := by decide
  have hdescent : baseEnd_4473057 < baseStart_4473057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473091 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 2, 3, 2]
def baseStart_4473091 : Nat := 118140960795 + 4473091 * 2 ^ 59
def prefixEnd_4473091 : Nat := 4983230072969 + 3 ^ 40 * 4473091 * 2
def baseEnd_4473091 : Nat := 2296845694300663744591135

theorem tailTrace_4473091 : CollatzResearch.WordTrace tailWord_4473091 prefixEnd_4473091 2296845694300663744591135 := by
  unfold tailWord_4473091
  simp only [CollatzResearch.WordTrace]
  refine ⟨163147031837762724967291127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108764687891841816644860751 163147031837762724967291127)
  ·
    refine ⟨244720547756644087450936691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163147031837762724967291127 244720547756644087450936691)
    ·
      refine ⟨367080821634966131176405037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244720547756644087450936691 367080821634966131176405037)
      ·
        refine ⟨137655308113112299191151889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367080821634966131176405037 137655308113112299191151889)
        ·
          refine ⟨103241481084834224393363917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137655308113112299191151889 103241481084834224393363917)
          ·
            refine ⟨38715555406812834147511469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103241481084834224393363917 38715555406812834147511469)
            ·
              refine ⟨14518333277554812805316801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38715555406812834147511469 14518333277554812805316801)
              ·
                refine ⟨10888749958166109603987601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14518333277554812805316801 10888749958166109603987601)
                ·
                  refine ⟨8166562468624582202990701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10888749958166109603987601 8166562468624582202990701)
                  ·
                    refine ⟨3062460925734218326121513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8166562468624582202990701 3062460925734218326121513)
                    ·
                      refine ⟨2296845694300663744591135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062460925734218326121513 2296845694300663744591135)
                      ·
                        rfl

theorem cell23_4473091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 3, 2].length) (baseStart_4473091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473091 prefixEnd_4473091 := by exact prefixLift 4473091
  have htrace : WordTrace (prefixWord ++ tailWord_4473091) baseStart_4473091 baseEnd_4473091 := by
    simpa [prefixWord, tailWord_4473091, baseEnd_4473091] using wordTrace_append hprefix tailTrace_4473091
  have hstable : (prefixWord ++ tailWord_4473091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473091).length < 2 ^ (prefixWord ++ tailWord_4473091).sum := by decide
  have hdescent : baseEnd_4473091 < baseStart_4473091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473098 : List Nat := [3, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_4473098 : Nat := 118140960795 + 4473098 * 2 ^ 59
def prefixEnd_4473098 : Nat := 4983230072969 + 3 ^ 40 * 4473098 * 2
def baseEnd_4473098 : Nat := 2296849288665245217203603

theorem tailTrace_4473098 : CollatzResearch.WordTrace tailWord_4473098 prefixEnd_4473098 2296849288665245217203603 := by
  unfold tailWord_4473098
  simp only [CollatzResearch.WordTrace]
  refine ⟨40786821787184341290698987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108764858099158243441863965 40786821787184341290698987)
  ·
    refine ⟨61180232680776511936048481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40786821787184341290698987 61180232680776511936048481)
    ·
      refine ⟨45885174510582383952036361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61180232680776511936048481 45885174510582383952036361)
      ·
        refine ⟨34413880882936787964027271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45885174510582383952036361 34413880882936787964027271)
        ·
          refine ⟨51620821324405181946040907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34413880882936787964027271 51620821324405181946040907)
          ·
            refine ⟨77431231986607772919061361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51620821324405181946040907 77431231986607772919061361)
            ·
              refine ⟨58073423989955829689296021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77431231986607772919061361 58073423989955829689296021)
              ·
                refine ⟨2722191749529179516685751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58073423989955829689296021 2722191749529179516685751)
                ·
                  refine ⟨4083287624293769275028627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722191749529179516685751 4083287624293769275028627)
                  ·
                    refine ⟨6124931436440653912542941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083287624293769275028627 6124931436440653912542941)
                    ·
                      refine ⟨2296849288665245217203603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6124931436440653912542941 2296849288665245217203603)
                      ·
                        rfl

theorem cell23_4473098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_4473098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473098 prefixEnd_4473098 := by exact prefixLift 4473098
  have htrace : WordTrace (prefixWord ++ tailWord_4473098) baseStart_4473098 baseEnd_4473098 := by
    simpa [prefixWord, tailWord_4473098, baseEnd_4473098] using wordTrace_append hprefix tailTrace_4473098
  have hstable : (prefixWord ++ tailWord_4473098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473098).length < 2 ^ (prefixWord ++ tailWord_4473098).sum := by decide
  have hdescent : baseEnd_4473098 < baseStart_4473098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473118 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4473118 : Nat := 118140960795 + 4473118 * 2 ^ 59
def prefixEnd_4473118 : Nat := 4983230072969 + 3 ^ 40 * 4473118 * 2
def baseEnd_4473118 : Nat := 765619852759445046317837

theorem tailTrace_4473118 : CollatzResearch.WordTrace tailWord_4473118 prefixEnd_4473118 765619852759445046317837 := by
  unfold tailWord_4473118
  simp only [CollatzResearch.WordTrace]
  refine ⟨20393502076083113572315501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108765344405776605719016005 20393502076083113572315501)
  ·
    refine ⟨7647563278531167589618313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20393502076083113572315501 7647563278531167589618313)
    ·
      refine ⟨5735672458898375692213735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7647563278531167589618313 5735672458898375692213735)
      ·
        refine ⟨8603508688347563538320603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5735672458898375692213735 8603508688347563538320603)
        ·
          refine ⟨12905263032521345307480905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8603508688347563538320603 12905263032521345307480905)
          ·
            refine ⟨9678947274391008980610679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12905263032521345307480905 9678947274391008980610679)
            ·
              refine ⟨14518420911586513470916019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9678947274391008980610679 14518420911586513470916019)
              ·
                refine ⟨21777631367379770206374029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14518420911586513470916019 21777631367379770206374029)
                ·
                  refine ⟨8166611762767413827390261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21777631367379770206374029 8166611762767413827390261)
                  ·
                    refine ⟨765619852759445046317837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8166611762767413827390261 765619852759445046317837)
                    ·
                      rfl

theorem cell23_4473118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4473118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473118 prefixEnd_4473118 := by exact prefixLift 4473118
  have htrace : WordTrace (prefixWord ++ tailWord_4473118) baseStart_4473118 baseEnd_4473118 := by
    simpa [prefixWord, tailWord_4473118, baseEnd_4473118] using wordTrace_append hprefix tailTrace_4473118
  have hstable : (prefixWord ++ tailWord_4473118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473118).length < 2 ^ (prefixWord ++ tailWord_4473118).sum := by decide
  have hdescent : baseEnd_4473118 < baseStart_4473118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473121 : List Nat := [1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4473121 : Nat := 118140960795 + 4473121 * 2 ^ 59
def prefixEnd_4473121 : Nat := 4983230072969 + 3 ^ 40 * 4473121 * 2
def baseEnd_4473121 : Nat := 2296861098720298627215997

theorem tailTrace_4473121 : CollatzResearch.WordTrace tailWord_4473121 prefixEnd_4473121 2296861098720298627215997 := by
  unfold tailWord_4473121
  simp only [CollatzResearch.WordTrace]
  refine ⟨163148126027654040090883217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108765417351769360060588811 163148126027654040090883217)
  ·
    refine ⟨122361094520740530068162413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163148126027654040090883217 122361094520740530068162413)
    ·
      refine ⟨45885410445277698775560905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122361094520740530068162413 45885410445277698775560905)
      ·
        refine ⟨34414057833958274081670679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45885410445277698775560905 34414057833958274081670679)
        ·
          refine ⟨51621086750937411122506019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34414057833958274081670679 51621086750937411122506019)
          ·
            refine ⟨77431630126406116683759029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51621086750937411122506019 77431630126406116683759029)
            ·
              refine ⟨7259215324350573439102409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 77431630126406116683759029 7259215324350573439102409)
              ·
                refine ⟨5444411493262930079326807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7259215324350573439102409 5444411493262930079326807)
                ·
                  refine ⟨8166617239894395118990211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444411493262930079326807 8166617239894395118990211)
                  ·
                    refine ⟨12249925859841592678485317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8166617239894395118990211 12249925859841592678485317)
                    ·
                      refine ⟨2296861098720298627215997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12249925859841592678485317 2296861098720298627215997)
                      ·
                        rfl

theorem cell23_4473121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4473121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473121 prefixEnd_4473121 := by exact prefixLift 4473121
  have htrace : WordTrace (prefixWord ++ tailWord_4473121) baseStart_4473121 baseEnd_4473121 := by
    simpa [prefixWord, tailWord_4473121, baseEnd_4473121] using wordTrace_append hprefix tailTrace_4473121
  have hstable : (prefixWord ++ tailWord_4473121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473121).length < 2 ^ (prefixWord ++ tailWord_4473121).sum := by decide
  have hdescent : baseEnd_4473121 < baseStart_4473121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473205 : List Nat := [1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4473205 : Nat := 118140960795 + 4473205 * 2 ^ 59
def prefixEnd_4473205 : Nat := 4983230072969 + 3 ^ 40 * 4473205 * 2
def baseEnd_4473205 : Nat := 2296904231095276298565611

theorem tailTrace_4473205 : CollatzResearch.WordTrace tailWord_4473205 prefixEnd_4473205 2296904231095276298565611 := by
  unfold tailWord_4473205
  simp only [CollatzResearch.WordTrace]
  refine ⟨163151189759349722436941069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108767459839566481624627379 163151189759349722436941069)
  ·
    refine ⟨61181696159756145913852901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163151189759349722436941069 61181696159756145913852901)
    ·
      refine ⟨11471568029954277358847419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61181696159756145913852901 11471568029954277358847419)
      ·
        refine ⟨17207352044931416038271129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11471568029954277358847419 17207352044931416038271129)
        ·
          refine ⟨12905514033698562028703347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17207352044931416038271129 12905514033698562028703347)
          ·
            refine ⟨19358271050547843043055021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12905514033698562028703347 19358271050547843043055021)
            ·
              refine ⟨7259351643955441141145633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19358271050547843043055021 7259351643955441141145633)
              ·
                refine ⟨5444513732966580855859225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7259351643955441141145633 5444513732966580855859225)
                ·
                  refine ⟨4083385299724935641894419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5444513732966580855859225 4083385299724935641894419)
                  ·
                    refine ⟨6125077949587403462841629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083385299724935641894419 6125077949587403462841629)
                    ·
                      refine ⟨2296904231095276298565611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125077949587403462841629 2296904231095276298565611)
                      ·
                        rfl

theorem cell23_4473205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4473205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473205 prefixEnd_4473205 := by exact prefixLift 4473205
  have htrace : WordTrace (prefixWord ++ tailWord_4473205) baseStart_4473205 baseEnd_4473205 := by
    simpa [prefixWord, tailWord_4473205, baseEnd_4473205] using wordTrace_append hprefix tailTrace_4473205
  have hstable : (prefixWord ++ tailWord_4473205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473205).length < 2 ^ (prefixWord ++ tailWord_4473205).sum := by decide
  have hdescent : baseEnd_4473205 < baseStart_4473205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473228 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 1, 4, 2]
def baseStart_4473228 : Nat := 118140960795 + 4473228 * 2 ^ 59
def prefixEnd_4473228 : Nat := 4983230072969 + 3 ^ 40 * 4473228 * 2
def baseEnd_4473228 : Nat := 2296916041150329708578005

theorem tailTrace_4473228 : CollatzResearch.WordTrace tailWord_4473228 prefixEnd_4473228 2296916041150329708578005 := by
  unfold tailWord_4473228
  simp only [CollatzResearch.WordTrace]
  refine ⟨81576014319133198682514169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108768019092177598243352225 81576014319133198682514169)
  ·
    refine ⟨61182010739349899011885627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81576014319133198682514169 61182010739349899011885627)
    ·
      refine ⟨91773016109024848517828441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61182010739349899011885627 91773016109024848517828441)
      ·
        refine ⟨68829762081768636388371331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91773016109024848517828441 68829762081768636388371331)
        ·
          refine ⟨103244643122652954582556997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68829762081768636388371331 103244643122652954582556997)
          ·
            refine ⟨19358370585497428984229437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103244643122652954582556997 19358370585497428984229437)
            ·
              refine ⟨7259388969561535869086039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19358370585497428984229437 7259388969561535869086039)
              ·
                refine ⟨10889083454342303803629059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7259388969561535869086039 10889083454342303803629059)
                ·
                  refine ⟨16333625181513455705443589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10889083454342303803629059 16333625181513455705443589)
                  ·
                    refine ⟨3062554721533772944770673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16333625181513455705443589 3062554721533772944770673)
                    ·
                      refine ⟨2296916041150329708578005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062554721533772944770673 2296916041150329708578005)
                      ·
                        rfl

theorem cell23_4473228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_4473228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473228 prefixEnd_4473228 := by exact prefixLift 4473228
  have htrace : WordTrace (prefixWord ++ tailWord_4473228) baseStart_4473228 baseEnd_4473228 := by
    simpa [prefixWord, tailWord_4473228, baseEnd_4473228] using wordTrace_append hprefix tailTrace_4473228
  have hstable : (prefixWord ++ tailWord_4473228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473228).length < 2 ^ (prefixWord ++ tailWord_4473228).sum := by decide
  have hdescent : baseEnd_4473228 < baseStart_4473228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473321 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 3]
def baseStart_4473321 : Nat := 118140960795 + 4473321 * 2 ^ 59
def prefixEnd_4473321 : Nat := 4983230072969 + 3 ^ 40 * 4473321 * 2
def baseEnd_4473321 : Nat := 2296963794851197844715077

theorem tailTrace_4473321 : CollatzResearch.WordTrace tailWord_4473321 prefixEnd_4473321 2296963794851197844715077 := by
  unfold tailWord_4473321
  simp only [CollatzResearch.WordTrace]
  refine ⟨163155420626929474248163817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108770280417952982832109211 163155420626929474248163817)
  ·
    refine ⟨122366565470197105686122863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163155420626929474248163817 122366565470197105686122863)
    ·
      refine ⟨183549848205295658529184295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122366565470197105686122863 183549848205295658529184295)
      ·
        refine ⟨275324772307943487793776443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183549848205295658529184295 275324772307943487793776443)
        ·
          refine ⟨412987158461915231690664665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275324772307943487793776443 412987158461915231690664665)
          ·
            refine ⟨309740368846436423767998499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 412987158461915231690664665 309740368846436423767998499)
            ·
              refine ⟨464610553269654635651997749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309740368846436423767998499 464610553269654635651997749)
              ·
                refine ⟨43557239369030122092374789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464610553269654635651997749 43557239369030122092374789)
                ·
                  refine ⟨8166982381693147892320273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43557239369030122092374789 8166982381693147892320273)
                  ·
                    refine ⟨6125236786269860919240205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8166982381693147892320273 6125236786269860919240205)
                    ·
                      refine ⟨2296963794851197844715077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125236786269860919240205 2296963794851197844715077)
                      ·
                        rfl

theorem cell23_4473321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 2, 3].length) (baseStart_4473321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473321 prefixEnd_4473321 := by exact prefixLift 4473321
  have htrace : WordTrace (prefixWord ++ tailWord_4473321) baseStart_4473321 baseEnd_4473321 := by
    simpa [prefixWord, tailWord_4473321, baseEnd_4473321] using wordTrace_append hprefix tailTrace_4473321
  have hstable : (prefixWord ++ tailWord_4473321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473321).length < 2 ^ (prefixWord ++ tailWord_4473321).sum := by decide
  have hdescent : baseEnd_4473321 < baseStart_4473321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473341 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 6]
def baseStart_4473341 : Nat := 118140960795 + 4473341 * 2 ^ 59
def prefixEnd_4473341 : Nat := 4983230072969 + 3 ^ 40 * 4473341 * 2
def baseEnd_4473341 : Nat := 255219340496031974051665

theorem tailTrace_4473341 : CollatzResearch.WordTrace tailWord_4473341 prefixEnd_4473341 255219340496031974051665 := by
  unfold tailWord_4473341
  simp only [CollatzResearch.WordTrace]
  refine ⟨163156150086857017663891877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108770766724571345109261251 163156150086857017663891877)
  ·
    refine ⟨30591778141285690811979727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163156150086857017663891877 30591778141285690811979727)
    ·
      refine ⟨45887667211928536217969591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30591778141285690811979727 45887667211928536217969591)
      ·
        refine ⟨68831500817892804326954387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45887667211928536217969591 68831500817892804326954387)
        ·
          refine ⟨103247251226839206490431581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68831500817892804326954387 103247251226839206490431581)
          ·
            refine ⟨38717719210064702433911843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103247251226839206490431581 38717719210064702433911843)
            ·
              refine ⟨58076578815097053650867765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38717719210064702433911843 58076578815097053650867765)
              ·
                refine ⟨5444679263915348779768853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58076578815097053650867765 5444679263915348779768853)
                ·
                  refine ⟨255219340496031974051665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5444679263915348779768853 255219340496031974051665)
                  ·
                    rfl

theorem cell23_4473341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 6].length) (baseStart_4473341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473341 prefixEnd_4473341 := by exact prefixLift 4473341
  have htrace : WordTrace (prefixWord ++ tailWord_4473341) baseStart_4473341 baseEnd_4473341 := by
    simpa [prefixWord, tailWord_4473341, baseEnd_4473341] using wordTrace_append hprefix tailTrace_4473341
  have hstable : (prefixWord ++ tailWord_4473341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473341).length < 2 ^ (prefixWord ++ tailWord_4473341).sum := by decide
  have hdescent : baseEnd_4473341 < baseStart_4473341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473355 : List Nat := [1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 3]
def baseStart_4473355 : Nat := 118140960795 + 4473355 * 2 ^ 59
def prefixEnd_4473355 : Nat := 4983230072969 + 3 ^ 40 * 4473355 * 2
def baseEnd_4473355 : Nat := 2296981253193450711689921

theorem tailTrace_4473355 : CollatzResearch.WordTrace tailWord_4473355 prefixEnd_4473355 2296981253193450711689921 := by
  unfold tailWord_4473355
  simp only [CollatzResearch.WordTrace]
  refine ⟨163156660708806298054901519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108771107139204198703267679 163156660708806298054901519)
  ·
    refine ⟨244734991063209447082352279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163156660708806298054901519 244734991063209447082352279)
    ·
      refine ⟨367102486594814170623528419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244734991063209447082352279 367102486594814170623528419)
      ·
        refine ⟨550653729892221255935292629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367102486594814170623528419 550653729892221255935292629)
        ·
          refine ⟨12905946794348935685983421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 550653729892221255935292629 12905946794348935685983421)
          ·
            refine ⟨4839730047880850882243783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12905946794348935685983421 4839730047880850882243783)
            ·
              refine ⟨7259595071821276323365675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4839730047880850882243783 7259595071821276323365675)
              ·
                refine ⟨10889392607731914485048513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7259595071821276323365675 10889392607731914485048513)
                ·
                  refine ⟨8167044455798935863786385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10889392607731914485048513 8167044455798935863786385)
                  ·
                    refine ⟨6125283341849201897839789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8167044455798935863786385 6125283341849201897839789)
                    ·
                      refine ⟨2296981253193450711689921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125283341849201897839789 2296981253193450711689921)
                      ·
                        rfl

theorem cell23_4473355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 1, 2, 2, 3].length) (baseStart_4473355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473355 prefixEnd_4473355 := by exact prefixLift 4473355
  have htrace : WordTrace (prefixWord ++ tailWord_4473355) baseStart_4473355 baseEnd_4473355 := by
    simpa [prefixWord, tailWord_4473355, baseEnd_4473355] using wordTrace_append hprefix tailTrace_4473355
  have hstable : (prefixWord ++ tailWord_4473355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473355).length < 2 ^ (prefixWord ++ tailWord_4473355).sum := by decide
  have hdescent : baseEnd_4473355 < baseStart_4473355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473405 : List Nat := [1, 4, 1, 3, 2, 2, 2, 2, 1, 5]
def baseStart_4473405 : Nat := 118140960795 + 4473405 * 2 ^ 59
def prefixEnd_4473405 : Nat := 4983230072969 + 3 ^ 40 * 4473405 * 2
def baseEnd_4473405 : Nat := 765668975742058505354897

theorem tailTrace_4473405 : CollatzResearch.WordTrace tailWord_4473405 prefixEnd_4473405 765668975742058505354897 := by
  unfold tailWord_4473405
  simp only [CollatzResearch.WordTrace]
  refine ⟨163158484358625156594221669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108772322905750104396147779 163158484358625156594221669)
  ·
    refine ⟨30592215817242216861416563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163158484358625156594221669 30592215817242216861416563)
    ·
      refine ⟨45888323725863325292124845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30592215817242216861416563 45888323725863325292124845)
      ·
        refine ⟨17208121397198746984546817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45888323725863325292124845 17208121397198746984546817)
        ·
          refine ⟨12906091047899060238410113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17208121397198746984546817 12906091047899060238410113)
          ·
            refine ⟨9679568285924295178807585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12906091047899060238410113 9679568285924295178807585)
            ·
              refine ⟨7259676214443221384105689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9679568285924295178807585 7259676214443221384105689)
              ·
                refine ⟨5444757160832416038079267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7259676214443221384105689 5444757160832416038079267)
                ·
                  refine ⟨8167135741248624057118901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444757160832416038079267 8167135741248624057118901)
                  ·
                    refine ⟨765668975742058505354897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8167135741248624057118901 765668975742058505354897)
                    ·
                      rfl

theorem cell23_4473405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_4473405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473405 prefixEnd_4473405 := by exact prefixLift 4473405
  have htrace : WordTrace (prefixWord ++ tailWord_4473405) baseStart_4473405 baseEnd_4473405 := by
    simpa [prefixWord, tailWord_4473405, baseEnd_4473405] using wordTrace_append hprefix tailTrace_4473405
  have hstable : (prefixWord ++ tailWord_4473405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473405).length < 2 ^ (prefixWord ++ tailWord_4473405).sum := by decide
  have hdescent : baseEnd_4473405 < baseStart_4473405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473408 : List Nat := [2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_4473408 : Nat := 118140960795 + 4473408 * 2 ^ 59
def prefixEnd_4473408 : Nat := 4983230072969 + 3 ^ 40 * 4473408 * 2
def baseEnd_4473408 : Nat := 2297008467668139004327177

theorem tailTrace_4473408 : CollatzResearch.WordTrace tailWord_4473408 prefixEnd_4473408 2297008467668139004327177 := by
  unfold tailWord_4473408
  simp only [CollatzResearch.WordTrace]
  refine ⟨81579296888807144053290439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108772395851742858737720585 81579296888807144053290439)
  ·
    refine ⟨122368945333210716079935659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81579296888807144053290439 122368945333210716079935659)
    ·
      refine ⟨183553417999816074119903489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122368945333210716079935659 183553417999816074119903489)
      ·
        refine ⟨137665063499862055589927617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183553417999816074119903489 137665063499862055589927617)
        ·
          refine ⟨103248797624896541692445713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137665063499862055589927617 103248797624896541692445713)
          ·
            refine ⟨77436598218672406269334285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103248797624896541692445713 77436598218672406269334285)
            ·
              refine ⟨29038724332002152351000357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77436598218672406269334285 29038724332002152351000357)
              ·
                refine ⟨5444760812250403565812567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29038724332002152351000357 5444760812250403565812567)
                ·
                  refine ⟨8167141218375605348718851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5444760812250403565812567 8167141218375605348718851)
                  ·
                    refine ⟨12250711827563408023078277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8167141218375605348718851 12250711827563408023078277)
                    ·
                      refine ⟨2297008467668139004327177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12250711827563408023078277 2297008467668139004327177)
                      ·
                        rfl

theorem cell23_4473408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_4473408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473408 prefixEnd_4473408 := by exact prefixLift 4473408
  have htrace : WordTrace (prefixWord ++ tailWord_4473408) baseStart_4473408 baseEnd_4473408 := by
    simpa [prefixWord, tailWord_4473408, baseEnd_4473408] using wordTrace_append hprefix tailTrace_4473408
  have hstable : (prefixWord ++ tailWord_4473408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473408).length < 2 ^ (prefixWord ++ tailWord_4473408).sum := by decide
  have hdescent : baseEnd_4473408 < baseStart_4473408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473411 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3]
def baseStart_4473411 : Nat := 118140960795 + 4473411 * 2 ^ 59
def prefixEnd_4473411 : Nat := 4983230072969 + 3 ^ 40 * 4473411 * 2
def baseEnd_4473411 : Nat := 2297010008110102492589663

theorem tailTrace_4473411 : CollatzResearch.WordTrace tailWord_4473411 prefixEnd_4473411 2297010008110102492589663 := by
  unfold tailWord_4473411
  simp only [CollatzResearch.WordTrace]
  refine ⟨163158703196603419618940087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108772468797735613079293391 163158703196603419618940087)
  ·
    refine ⟨244738054794905129428410131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163158703196603419618940087 244738054794905129428410131)
    ·
      refine ⟨367107082192357694142615197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244738054794905129428410131 367107082192357694142615197)
      ·
        refine ⟨137665155822134135303480699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367107082192357694142615197 137665155822134135303480699)
        ·
          refine ⟨206497733733201202955221049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137665155822134135303480699 206497733733201202955221049)
          ·
            refine ⟨154873300299900902216415787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206497733733201202955221049 154873300299900902216415787)
            ·
              refine ⟨232309950449851353324623681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154873300299900902216415787 232309950449851353324623681)
              ·
                refine ⟨174232462837388514993467761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232309950449851353324623681 174232462837388514993467761)
                ·
                  refine ⟨130674347128041386245100821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 174232462837388514993467761 130674347128041386245100821)
                  ·
                    refine ⟨6125360021626939980239101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130674347128041386245100821 6125360021626939980239101)
                    ·
                      refine ⟨2297010008110102492589663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125360021626939980239101 2297010008110102492589663)
                      ·
                        rfl

theorem cell23_4473411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 6, 3].length) (baseStart_4473411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473411 prefixEnd_4473411 := by exact prefixLift 4473411
  have htrace : WordTrace (prefixWord ++ tailWord_4473411) baseStart_4473411 baseEnd_4473411 := by
    simpa [prefixWord, tailWord_4473411, baseEnd_4473411] using wordTrace_append hprefix tailTrace_4473411
  have hstable : (prefixWord ++ tailWord_4473411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473411).length < 2 ^ (prefixWord ++ tailWord_4473411).sum := by decide
  have hdescent : baseEnd_4473411 < baseStart_4473411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473418 : List Nat := [3, 1, 2, 1, 1, 4, 1, 2, 4, 4]
def baseStart_4473418 : Nat := 118140960795 + 4473418 * 2 ^ 59
def prefixEnd_4473418 : Nat := 4983230072969 + 3 ^ 40 * 4473418 * 2
def baseEnd_4473418 : Nat := 765671200824894655067377

theorem tailTrace_4473418 : CollatzResearch.WordTrace tailWord_4473418 prefixEnd_4473418 765671200824894655067377 := by
  unfold tailWord_4473418
  simp only [CollatzResearch.WordTrace]
  refine ⟨40789739626894514953611227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108772639005052039876296605 40789739626894514953611227)
  ·
    refine ⟨61184609440341772430416841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40789739626894514953611227 61184609440341772430416841)
    ·
      refine ⟨45888457080256329322812631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61184609440341772430416841 45888457080256329322812631)
      ·
        refine ⟨68832685620384493984218947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45888457080256329322812631 68832685620384493984218947)
        ·
          refine ⟨103249028430576740976328421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68832685620384493984218947 103249028430576740976328421)
          ·
            refine ⟨19359192830733138933061579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103249028430576740976328421 19359192830733138933061579)
            ·
              refine ⟨29038789246099708399592369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19359192830733138933061579 29038789246099708399592369)
              ·
                refine ⟨21779091934574781299694277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29038789246099708399592369 21779091934574781299694277)
                ·
                  refine ⟨4083579737732771493692677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21779091934574781299694277 4083579737732771493692677)
                  ·
                    refine ⟨765671200824894655067377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4083579737732771493692677 765671200824894655067377)
                    ·
                      rfl

theorem cell23_4473418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_4473418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473418 prefixEnd_4473418 := by exact prefixLift 4473418
  have htrace : WordTrace (prefixWord ++ tailWord_4473418) baseStart_4473418 baseEnd_4473418 := by
    simpa [prefixWord, tailWord_4473418, baseEnd_4473418] using wordTrace_append hprefix tailTrace_4473418
  have hstable : (prefixWord ++ tailWord_4473418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473418).length < 2 ^ (prefixWord ++ tailWord_4473418).sum := by decide
  have hdescent : baseEnd_4473418 < baseStart_4473418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473428 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_4473428 : Nat := 118140960795 + 4473428 * 2 ^ 59
def prefixEnd_4473428 : Nat := 4983230072969 + 3 ^ 40 * 4473428 * 2
def baseEnd_4473428 : Nat := 2297018737281228926077085

theorem tailTrace_4473428 : CollatzResearch.WordTrace tailWord_4473428 prefixEnd_4473428 2297018737281228926077085 := by
  unfold tailWord_4473428
  simp only [CollatzResearch.WordTrace]
  refine ⟨81579661618770915761154469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108772882158361221014872625 81579661618770915761154469)
  ·
    refine ⟨15296186553519546705216463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81579661618770915761154469 15296186553519546705216463)
    ·
      refine ⟨22944279830279320057824695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296186553519546705216463 22944279830279320057824695)
      ·
        refine ⟨34416419745418980086737043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22944279830279320057824695 34416419745418980086737043)
        ·
          refine ⟨51624629618128470130105565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34416419745418980086737043 51624629618128470130105565)
          ·
            refine ⟨19359236106798176298789587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51624629618128470130105565 19359236106798176298789587)
            ·
              refine ⟨29038854160197264448184381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19359236106798176298789587 29038854160197264448184381)
              ·
                refine ⟨10889570310073974168069143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29038854160197264448184381 10889570310073974168069143)
                ·
                  refine ⟨16334355465110961252103715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10889570310073974168069143 16334355465110961252103715)
                  ·
                    refine ⟨24501533197666441878155573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16334355465110961252103715 24501533197666441878155573)
                    ·
                      refine ⟨2297018737281228926077085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24501533197666441878155573 2297018737281228926077085)
                      ·
                        rfl

theorem cell23_4473428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_4473428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473428 prefixEnd_4473428 := by exact prefixLift 4473428
  have htrace : WordTrace (prefixWord ++ tailWord_4473428) baseStart_4473428 baseEnd_4473428 := by
    simpa [prefixWord, tailWord_4473428, baseEnd_4473428] using wordTrace_append hprefix tailTrace_4473428
  have hstable : (prefixWord ++ tailWord_4473428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473428).length < 2 ^ (prefixWord ++ tailWord_4473428).sum := by decide
  have hdescent : baseEnd_4473428 < baseStart_4473428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473436 : List Nat := [2, 2, 4, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_4473436 : Nat := 118140960795 + 4473436 * 2 ^ 59
def prefixEnd_4473436 : Nat := 4983230072969 + 3 ^ 40 * 4473436 * 2
def baseEnd_4473436 : Nat := 2297022845126464894777049

theorem tailTrace_4473436 : CollatzResearch.WordTrace tailWord_4473436 prefixEnd_4473436 2297022845126464894777049 := by
  unfold tailWord_4473436
  simp only [CollatzResearch.WordTrace]
  refine ⟨81579807510756424444300081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108773076681008565925733441 81579807510756424444300081)
  ·
    refine ⟨61184855633067318333225061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81579807510756424444300081 61184855633067318333225061)
    ·
      refine ⟨11472160431200122187479699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61184855633067318333225061 11472160431200122187479699)
      ·
        refine ⟨17208240646800183281219549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11472160431200122187479699 17208240646800183281219549)
        ·
          refine ⟨6453090242550068730457331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17208240646800183281219549 6453090242550068730457331)
          ·
            refine ⟨9679635363825103095685997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453090242550068730457331 9679635363825103095685997)
            ·
              refine ⟨3629863261434413660882249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9679635363825103095685997 3629863261434413660882249)
              ·
                refine ⟨2722397446075810245661687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3629863261434413660882249 2722397446075810245661687)
                ·
                  refine ⟨4083596169113715368492531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722397446075810245661687 4083596169113715368492531)
                  ·
                    refine ⟨6125394253670573052738797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083596169113715368492531 6125394253670573052738797)
                    ·
                      refine ⟨2297022845126464894777049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125394253670573052738797 2297022845126464894777049)
                      ·
                        rfl

theorem cell23_4473436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_4473436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473436 prefixEnd_4473436 := by exact prefixLift 4473436
  have htrace : WordTrace (prefixWord ++ tailWord_4473436) baseStart_4473436 baseEnd_4473436 := by
    simpa [prefixWord, tailWord_4473436, baseEnd_4473436] using wordTrace_append hprefix tailTrace_4473436
  have hstable : (prefixWord ++ tailWord_4473436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473436).length < 2 ^ (prefixWord ++ tailWord_4473436).sum := by decide
  have hdescent : baseEnd_4473436 < baseStart_4473436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473462 : List Nat := [5, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4473462 : Nat := 118140960795 + 4473462 * 2 ^ 59
def prefixEnd_4473462 : Nat := 4983230072969 + 3 ^ 40 * 4473462 * 2
def baseEnd_4473462 : Nat := 2297036195623481793051929

theorem tailTrace_4473462 : CollatzResearch.WordTrace tailWord_4473462 prefixEnd_4473462 2297036195623481793051929 := by
  unfold tailWord_4473462
  simp only [CollatzResearch.WordTrace]
  refine ⟨10197535207463665958065415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108773708879612436886031093 10197535207463665958065415)
  ·
    refine ⟨15296302811195498937098123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10197535207463665958065415 15296302811195498937098123)
    ·
      refine ⟨22944454216793248405647185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15296302811195498937098123 22944454216793248405647185)
      ·
        refine ⟨17208340662594936304235389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22944454216793248405647185 17208340662594936304235389)
        ·
          refine ⟨6453127748473101114088271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17208340662594936304235389 6453127748473101114088271)
          ·
            refine ⟨9679691622709651671132407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453127748473101114088271 9679691622709651671132407)
            ·
              refine ⟨14519537434064477506698611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9679691622709651671132407 14519537434064477506698611)
              ·
                refine ⟨21779306151096716260047917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14519537434064477506698611 21779306151096716260047917)
                ·
                  refine ⟨8167239806661268597517969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21779306151096716260047917 8167239806661268597517969)
                  ·
                    refine ⟨6125429854995951448138477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8167239806661268597517969 6125429854995951448138477)
                    ·
                      refine ⟨2297036195623481793051929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125429854995951448138477 2297036195623481793051929)
                      ·
                        rfl

theorem cell23_4473462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4473462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473462 prefixEnd_4473462 := by exact prefixLift 4473462
  have htrace : WordTrace (prefixWord ++ tailWord_4473462) baseStart_4473462 baseEnd_4473462 := by
    simpa [prefixWord, tailWord_4473462, baseEnd_4473462] using wordTrace_append hprefix tailTrace_4473462
  have hstable : (prefixWord ++ tailWord_4473462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473462).length < 2 ^ (prefixWord ++ tailWord_4473462).sum := by decide
  have hdescent : baseEnd_4473462 < baseStart_4473462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473471 : List Nat := [1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5]
def baseStart_4473471 : Nat := 118140960795 + 4473471 * 2 ^ 59
def prefixEnd_4473471 : Nat := 4983230072969 + 3 ^ 40 * 4473471 * 2
def baseEnd_4473471 : Nat := 2297040816949372257839387

theorem tailTrace_4473471 : CollatzResearch.WordTrace tailWord_4473471 prefixEnd_4473471 2297040816949372257839387 := by
  unfold tailWord_4473471
  simp only [CollatzResearch.WordTrace]
  refine ⟨163160891576386049866124267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108773927717590699910749511 163160891576386049866124267)
  ·
    refine ⟨244741337364579074799186401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163160891576386049866124267 244741337364579074799186401)
    ·
      refine ⟨183556003023434306099389801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244741337364579074799186401 183556003023434306099389801)
      ·
        refine ⟨137667002267575729574542351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183556003023434306099389801 137667002267575729574542351)
        ·
          refine ⟨206500503401363594361813527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137667002267575729574542351 206500503401363594361813527)
          ·
            refine ⟨309750755102045391542720291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206500503401363594361813527 309750755102045391542720291)
            ·
              refine ⟨464626132653068087314080437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309750755102045391542720291 464626132653068087314080437)
              ·
                refine ⟨43558699936225133185695041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464626132653068087314080437 43558699936225133185695041)
                ·
                  refine ⟨32669024952168849889271281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43558699936225133185695041 32669024952168849889271281)
                  ·
                    refine ⟨24501768714126637416953461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32669024952168849889271281 24501768714126637416953461)
                    ·
                      refine ⟨2297040816949372257839387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24501768714126637416953461 2297040816949372257839387)
                      ·
                        rfl

theorem cell23_4473471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_4473471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473471 prefixEnd_4473471 := by exact prefixLift 4473471
  have htrace : WordTrace (prefixWord ++ tailWord_4473471) baseStart_4473471 baseEnd_4473471 := by
    simpa [prefixWord, tailWord_4473471, baseEnd_4473471] using wordTrace_append hprefix tailTrace_4473471
  have hstable : (prefixWord ++ tailWord_4473471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473471).length < 2 ^ (prefixWord ++ tailWord_4473471).sum := by decide
  have hdescent : baseEnd_4473471 < baseStart_4473471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473491 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 4, 6]
def baseStart_4473491 : Nat := 118140960795 + 4473491 * 2 ^ 59
def prefixEnd_4473491 : Nat := 4983230072969 + 3 ^ 40 * 4473491 * 2
def baseEnd_4473491 : Nat := 765683695520820726529765

theorem tailTrace_4473491 : CollatzResearch.WordTrace tailWord_4473491 prefixEnd_4473491 765683695520820726529765 := by
  unfold tailWord_4473491
  simp only [CollatzResearch.WordTrace]
  refine ⟨163161621036313593281852327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108774414024209062187901551 163161621036313593281852327)
  ·
    refine ⟨244742431554470389922778491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163161621036313593281852327 244742431554470389922778491)
    ·
      refine ⟨367113647331705584884167737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244742431554470389922778491 367113647331705584884167737)
      ·
        refine ⟨275335235498779188663125803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367113647331705584884167737 275335235498779188663125803)
        ·
          refine ⟨413002853248168782994688705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275335235498779188663125803 413002853248168782994688705)
          ·
            refine ⟨309752139936126587246016529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 413002853248168782994688705 309752139936126587246016529)
            ·
              refine ⟨232314104952094940434512397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 309752139936126587246016529 232314104952094940434512397)
              ·
                refine ⟨87117789357035602662942149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232314104952094940434512397 87117789357035602662942149)
                ·
                  refine ⟨16334585504444175499301653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87117789357035602662942149 16334585504444175499301653)
                  ·
                    refine ⟨765683695520820726529765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16334585504444175499301653 765683695520820726529765)
                    ·
                      rfl

theorem cell23_4473491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 6].length) (baseStart_4473491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473491 prefixEnd_4473491 := by exact prefixLift 4473491
  have htrace : WordTrace (prefixWord ++ tailWord_4473491) baseStart_4473491 baseEnd_4473491 := by
    simpa [prefixWord, tailWord_4473491, baseEnd_4473491] using wordTrace_append hprefix tailTrace_4473491
  have hstable : (prefixWord ++ tailWord_4473491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473491).length < 2 ^ (prefixWord ++ tailWord_4473491).sum := by decide
  have hdescent : baseEnd_4473491 < baseStart_4473491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473502 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4473502 : Nat := 118140960795 + 4473502 * 2 ^ 59
def prefixEnd_4473502 : Nat := 4983230072969 + 3 ^ 40 * 4473502 * 2
def baseEnd_4473502 : Nat := 2297056734849661636551745

theorem tailTrace_4473502 : CollatzResearch.WordTrace tailWord_4473502 prefixEnd_4473502 2297056734849661636551745 := by
  unfold tailWord_4473502
  simp only [CollatzResearch.WordTrace]
  refine ⟨20395252779909217770062845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108774681492849161440335173 20395252779909217770062845)
  ·
    refine ⟨7648219792465956663773567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20395252779909217770062845 7648219792465956663773567)
    ·
      refine ⟨11472329688698934995660351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648219792465956663773567 11472329688698934995660351)
      ·
        refine ⟨17208494533048402493490527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11472329688698934995660351 17208494533048402493490527)
        ·
          refine ⟨25812741799572603740235791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17208494533048402493490527 25812741799572603740235791)
          ·
            refine ⟨38719112699358905610353687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25812741799572603740235791 38719112699358905610353687)
            ·
              refine ⟨58078669049038358415530531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38719112699358905610353687 58078669049038358415530531)
              ·
                refine ⟨87118003573557537623295797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58078669049038358415530531 87118003573557537623295797)
                ·
                  refine ⟨8167312835021019152183981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 87118003573557537623295797 8167312835021019152183981)
                  ·
                    refine ⟨3062742313132882182068993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8167312835021019152183981 3062742313132882182068993)
                    ·
                      refine ⟨2297056734849661636551745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062742313132882182068993 2297056734849661636551745)
                      ·
                        rfl

theorem cell23_4473502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4473502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473502 prefixEnd_4473502 := by exact prefixLift 4473502
  have htrace : WordTrace (prefixWord ++ tailWord_4473502) baseStart_4473502 baseEnd_4473502 := by
    simpa [prefixWord, tailWord_4473502, baseEnd_4473502] using wordTrace_append hprefix tailTrace_4473502
  have hstable : (prefixWord ++ tailWord_4473502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473502).length < 2 ^ (prefixWord ++ tailWord_4473502).sum := by decide
  have hdescent : baseEnd_4473502 < baseStart_4473502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473508 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 2, 6]
def baseStart_4473508 : Nat := 118140960795 + 4473508 * 2 ^ 59
def prefixEnd_4473508 : Nat := 4983230072969 + 3 ^ 40 * 4473508 * 2
def baseEnd_4473508 : Nat := 765686605244529537692239

theorem tailTrace_4473508 : CollatzResearch.WordTrace tailWord_4473508 prefixEnd_4473508 765686605244529537692239 := by
  unfold tailWord_4473508
  simp only [CollatzResearch.WordTrace]
  refine ⟨81581120538626002592610589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108774827384834670123480785 81581120538626002592610589)
  ·
    refine ⟨30592920201984750972228971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81581120538626002592610589 30592920201984750972228971)
    ·
      refine ⟨45889380302977126458343457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30592920201984750972228971 45889380302977126458343457)
      ·
        refine ⟨34417035227232844843757593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45889380302977126458343457 34417035227232844843757593)
        ·
          refine ⟨25812776420424633632818195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34417035227232844843757593 25812776420424633632818195)
          ·
            refine ⟨38719164630636950449227293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25812776420424633632818195 38719164630636950449227293)
            ·
              refine ⟨14519686736488856418460235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38719164630636950449227293 14519686736488856418460235)
              ·
                refine ⟨21779530104733284627690353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14519686736488856418460235 21779530104733284627690353)
                ·
                  refine ⟨16334647578549963470767765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21779530104733284627690353 16334647578549963470767765)
                  ·
                    refine ⟨765686605244529537692239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16334647578549963470767765 765686605244529537692239)
                    ·
                      rfl

theorem cell23_4473508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 2, 6].length) (baseStart_4473508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473508 prefixEnd_4473508 := by exact prefixLift 4473508
  have htrace : WordTrace (prefixWord ++ tailWord_4473508) baseStart_4473508 baseEnd_4473508 := by
    simpa [prefixWord, tailWord_4473508, baseEnd_4473508] using wordTrace_append hprefix tailTrace_4473508
  have hstable : (prefixWord ++ tailWord_4473508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473508).length < 2 ^ (prefixWord ++ tailWord_4473508).sum := by decide
  have hdescent : baseEnd_4473508 < baseStart_4473508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473531 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7]
def baseStart_4473531 : Nat := 118140960795 + 4473531 * 2 ^ 59
def prefixEnd_4473531 : Nat := 4983230072969 + 3 ^ 40 * 4473531 * 2
def baseEnd_4473531 : Nat := 2297071625788642023089111

theorem tailTrace_4473531 : CollatzResearch.WordTrace tailWord_4473531 prefixEnd_4473531 2297071625788642023089111 := by
  unfold tailWord_4473531
  simp only [CollatzResearch.WordTrace]
  refine ⟨163163079956168680113308447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108775386637445786742205631 163163079956168680113308447)
  ·
    refine ⟨244744619934253020169962671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163163079956168680113308447 244744619934253020169962671)
    ·
      refine ⟨367116929901379530254944007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244744619934253020169962671 367116929901379530254944007)
      ·
        refine ⟨550675394852069295382416011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367116929901379530254944007 550675394852069295382416011)
        ·
          refine ⟨826013092278103943073624017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550675394852069295382416011 826013092278103943073624017)
          ·
            refine ⟨619509819208577957305218013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826013092278103943073624017 619509819208577957305218013)
            ·
              refine ⟨232316182203216733989456755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 619509819208577957305218013 232316182203216733989456755)
              ·
                refine ⟨348474273304825100984185133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232316182203216733989456755 348474273304825100984185133)
                ·
                  refine ⟨130677852489309412869069425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348474273304825100984185133 130677852489309412869069425)
                  ·
                    refine ⟨98008389366982059651802069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 130677852489309412869069425 98008389366982059651802069)
                    ·
                      refine ⟨2297071625788642023089111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98008389366982059651802069 2297071625788642023089111)
                      ·
                        rfl

theorem cell23_4473531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 7].length) (baseStart_4473531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473531 prefixEnd_4473531 := by exact prefixLift 4473531
  have htrace : WordTrace (prefixWord ++ tailWord_4473531) baseStart_4473531 baseEnd_4473531 := by
    simpa [prefixWord, tailWord_4473531, baseEnd_4473531] using wordTrace_append hprefix tailTrace_4473531
  have hstable : (prefixWord ++ tailWord_4473531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473531).length < 2 ^ (prefixWord ++ tailWord_4473531).sum := by decide
  have hdescent : baseEnd_4473531 < baseStart_4473531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473532 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_4473532 : Nat := 118140960795 + 4473532 * 2 ^ 59
def prefixEnd_4473532 : Nat := 4983230072969 + 3 ^ 40 * 4473532 * 2
def baseEnd_4473532 : Nat := 2297072139269296519176607

theorem tailTrace_4473532 : CollatzResearch.WordTrace tailWord_4473532 prefixEnd_4473532 2297072139269296519176607 := by
  unfold tailWord_4473532
  simp only [CollatzResearch.WordTrace]
  refine ⟨81581558214582528642047425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108775410952776704856063233 81581558214582528642047425)
  ·
    refine ⟨61186168660936896481535569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81581558214582528642047425 61186168660936896481535569)
    ·
      refine ⟨45889626495702672361151677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61186168660936896481535569 45889626495702672361151677)
      ·
        refine ⟨17208609935888502135431879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45889626495702672361151677 17208609935888502135431879)
        ·
          refine ⟨25812914903832753203147819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17208609935888502135431879 25812914903832753203147819)
          ·
            refine ⟨38719372355749129804721729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25812914903832753203147819 38719372355749129804721729)
            ·
              refine ⟨29039529266811847353541297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38719372355749129804721729 29039529266811847353541297)
              ·
                refine ⟨21779646950108885515155973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29039529266811847353541297 21779646950108885515155973)
                ·
                  refine ⟨4083683803145416034091745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21779646950108885515155973 4083683803145416034091745)
                  ·
                    refine ⟨3062762852359062025568809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083683803145416034091745 3062762852359062025568809)
                    ·
                      refine ⟨2297072139269296519176607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062762852359062025568809 2297072139269296519176607)
                      ·
                        rfl

theorem cell23_4473532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_4473532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473532 prefixEnd_4473532 := by exact prefixLift 4473532
  have htrace : WordTrace (prefixWord ++ tailWord_4473532) baseStart_4473532 baseEnd_4473532 := by
    simpa [prefixWord, tailWord_4473532, baseEnd_4473532] using wordTrace_append hprefix tailTrace_4473532
  have hstable : (prefixWord ++ tailWord_4473532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473532).length < 2 ^ (prefixWord ++ tailWord_4473532).sum := by decide
  have hdescent : baseEnd_4473532 < baseStart_4473532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473578 : List Nat := [3, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_4473578 : Nat := 118140960795 + 4473578 * 2 ^ 59
def prefixEnd_4473578 : Nat := 4983230072969 + 3 ^ 40 * 4473578 * 2
def baseEnd_4473578 : Nat := 2297095759379403339201395

theorem tailTrace_4473578 : CollatzResearch.WordTrace tailWord_4473578 prefixEnd_4473578 2297095759379403339201395 := by
  unfold tailWord_4473578
  simp only [CollatzResearch.WordTrace]
  refine ⟨40791198546749601785067347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108776529457998938093512925 40791198546749601785067347)
  ·
    refine ⟨61186797820124402677601021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40791198546749601785067347 61186797820124402677601021)
    ·
      refine ⟨22945049182546651004100383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61186797820124402677601021 22945049182546651004100383)
      ·
        refine ⟨34417573773819976506150575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22945049182546651004100383 34417573773819976506150575)
        ·
          refine ⟨51626360660729964759225863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34417573773819976506150575 51626360660729964759225863)
          ·
            refine ⟨77439540991094947138838795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51626360660729964759225863 77439540991094947138838795)
            ·
              refine ⟨116159311486642420708258193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77439540991094947138838795 116159311486642420708258193)
              ·
                refine ⟨87119483614981815531193645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116159311486642420708258193 87119483614981815531193645)
                ·
                  refine ⟨32669806355618180824197617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87119483614981815531193645 32669806355618180824197617)
                  ·
                    refine ⟨24502354766713635618148213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32669806355618180824197617 24502354766713635618148213)
                    ·
                      refine ⟨2297095759379403339201395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24502354766713635618148213 2297095759379403339201395)
                      ·
                        rfl

theorem cell23_4473578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_4473578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473578 prefixEnd_4473578 := by exact prefixLift 4473578
  have htrace : WordTrace (prefixWord ++ tailWord_4473578) baseStart_4473578 baseEnd_4473578 := by
    simpa [prefixWord, tailWord_4473578, baseEnd_4473578] using wordTrace_append hprefix tailTrace_4473578
  have hstable : (prefixWord ++ tailWord_4473578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473578).length < 2 ^ (prefixWord ++ tailWord_4473578).sum := by decide
  have hdescent : baseEnd_4473578 < baseStart_4473578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473602 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 2, 5]
def baseStart_4473602 : Nat := 118140960795 + 4473602 * 2 ^ 59
def prefixEnd_4473602 : Nat := 4983230072969 + 3 ^ 40 * 4473602 * 2
def baseEnd_4473602 : Nat := 765702694305037081767095

theorem tailTrace_4473602 : CollatzResearch.WordTrace tailWord_4473602 prefixEnd_4473602 765702694305037081767095 := by
  unfold tailWord_4473602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40791417384727864809785765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108777113025940972826095373 40791417384727864809785765)
  ·
    refine ⟨7648390759636474651834831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40791417384727864809785765 7648390759636474651834831)
    ·
      refine ⟨11472586139454711977752247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648390759636474651834831 11472586139454711977752247)
      ·
        refine ⟨17208879209182067966628371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11472586139454711977752247 17208879209182067966628371)
        ·
          refine ⟨25813318813773101949942557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17208879209182067966628371 25813318813773101949942557)
          ·
            refine ⟨9679994555164913231228459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25813318813773101949942557 9679994555164913231228459)
            ·
              refine ⟨14519991832747369846842689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9679994555164913231228459 14519991832747369846842689)
              ·
                refine ⟨10889993874560527385132017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14519991832747369846842689 10889993874560527385132017)
                ·
                  refine ⟨8167495405920395538849013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10889993874560527385132017 8167495405920395538849013)
                  ·
                    refine ⟨765702694305037081767095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8167495405920395538849013 765702694305037081767095)
                    ·
                      rfl

theorem cell23_4473602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_4473602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473602 prefixEnd_4473602 := by exact prefixLift 4473602
  have htrace : WordTrace (prefixWord ++ tailWord_4473602) baseStart_4473602 baseEnd_4473602 := by
    simpa [prefixWord, tailWord_4473602, baseEnd_4473602] using wordTrace_append hprefix tailTrace_4473602
  have hstable : (prefixWord ++ tailWord_4473602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473602).length < 2 ^ (prefixWord ++ tailWord_4473602).sum := by decide
  have hdescent : baseEnd_4473602 < baseStart_4473602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473605 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_4473605 : Nat := 118140960795 + 4473605 * 2 ^ 59
def prefixEnd_4473605 : Nat := 4983230072969 + 3 ^ 40 * 4473605 * 2
def baseEnd_4473605 : Nat := 2297109623357074733563771

theorem tailTrace_4473605 : CollatzResearch.WordTrace tailWord_4473605 prefixEnd_4473605 2297109623357074733563771 := by
  unfold tailWord_4473605
  simp only [CollatzResearch.WordTrace]
  refine ⟨163165778957900590751502269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108777185971933727167668179 163165778957900590751502269)
  ·
    refine ⟨61187167109212721531813351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163165778957900590751502269 61187167109212721531813351)
    ·
      refine ⟨91780750663819082297720027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61187167109212721531813351 91780750663819082297720027)
      ·
        refine ⟨137671125995728623446580041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91780750663819082297720027 137671125995728623446580041)
        ·
          refine ⟨103253344496796467584935031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137671125995728623446580041 103253344496796467584935031)
          ·
            refine ⟨154880016745194701377402547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103253344496796467584935031 154880016745194701377402547)
            ·
              refine ⟨232320025117792052066103821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154880016745194701377402547 232320025117792052066103821)
              ·
                refine ⟨87120009419172019524788933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232320025117792052066103821 87120009419172019524788933)
                ·
                  refine ⟨16335001766094753660897925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 87120009419172019524788933 16335001766094753660897925)
                  ·
                    refine ⟨3062812831142766311418361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16335001766094753660897925 3062812831142766311418361)
                    ·
                      refine ⟨2297109623357074733563771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062812831142766311418361 2297109623357074733563771)
                      ·
                        rfl

theorem cell23_4473605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_4473605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473605 prefixEnd_4473605 := by exact prefixLift 4473605
  have htrace : WordTrace (prefixWord ++ tailWord_4473605) baseStart_4473605 baseEnd_4473605 := by
    simpa [prefixWord, tailWord_4473605, baseEnd_4473605] using wordTrace_append hprefix tailTrace_4473605
  have hstable : (prefixWord ++ tailWord_4473605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473605).length < 2 ^ (prefixWord ++ tailWord_4473605).sum := by decide
  have hdescent : baseEnd_4473605 < baseStart_4473605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473672 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_4473672 : Nat := 118140960795 + 4473672 * 2 ^ 59
def prefixEnd_4473672 : Nat := 4983230072969 + 3 ^ 40 * 4473672 * 2
def baseEnd_4473672 : Nat := 2297144026560925971425963

theorem tailTrace_4473672 : CollatzResearch.WordTrace tailWord_4473672 prefixEnd_4473672 2297144026560925971425963 := by
  unfold tailWord_4473672
  simp only [CollatzResearch.WordTrace]
  refine ⟨81584111324328930597095635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108778815099105240796127513 81584111324328930597095635)
  ·
    refine ⟨122376166986493395895643453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81584111324328930597095635 122376166986493395895643453)
    ·
      refine ⟨45891062619935023460866295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122376166986493395895643453 45891062619935023460866295)
      ·
        refine ⟨68836593929902535191299443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45891062619935023460866295 68836593929902535191299443)
        ·
          refine ⟨103254890894853802786949165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68836593929902535191299443 103254890894853802786949165)
          ·
            refine ⟨38720584085570176045105937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103254890894853802786949165 38720584085570176045105937)
            ·
              refine ⟨29040438064177632033829453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38720584085570176045105937 29040438064177632033829453)
              ·
                refine ⟨10890164274066612012686045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29040438064177632033829453 10890164274066612012686045)
                ·
                  refine ⟨4083811602774979504757267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10890164274066612012686045 4083811602774979504757267)
                  ·
                    refine ⟨6125717404162469257135901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4083811602774979504757267 6125717404162469257135901)
                    ·
                      refine ⟨2297144026560925971425963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125717404162469257135901 2297144026560925971425963)
                      ·
                        rfl

theorem cell23_4473672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_4473672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473672 prefixEnd_4473672 := by exact prefixLift 4473672
  have htrace : WordTrace (prefixWord ++ tailWord_4473672) baseStart_4473672 baseEnd_4473672 := by
    simpa [prefixWord, tailWord_4473672, baseEnd_4473672] using wordTrace_append hprefix tailTrace_4473672
  have hstable : (prefixWord ++ tailWord_4473672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473672).length < 2 ^ (prefixWord ++ tailWord_4473672).sum := by decide
  have hdescent : baseEnd_4473672 < baseStart_4473672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473682 : List Nat := [3, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_4473682 : Nat := 118140960795 + 4473682 * 2 ^ 59
def prefixEnd_4473682 : Nat := 4983230072969 + 3 ^ 40 * 4473682 * 2
def baseEnd_4473682 : Nat := 2297149161367470932300917

theorem tailTrace_4473682 : CollatzResearch.WordTrace tailWord_4473682 prefixEnd_4473682 2297149161367470932300917 := by
  unfold tailWord_4473682
  simp only [CollatzResearch.WordTrace]
  refine ⟨40792146844655408225513825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108779058252414421934703533 40792146844655408225513825)
  ·
    refine ⟨30594110133491556169135369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40792146844655408225513825 30594110133491556169135369)
    ·
      refine ⟨22945582600118667126851527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30594110133491556169135369 22945582600118667126851527)
      ·
        refine ⟨34418373900178000690277291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22945582600118667126851527 34418373900178000690277291)
        ·
          refine ⟨51627560850267001035415937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34418373900178000690277291 51627560850267001035415937)
          ·
            refine ⟨38720670637700250776561953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51627560850267001035415937 38720670637700250776561953)
            ·
              refine ⟨29040502978275188082421465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38720670637700250776561953 29040502978275188082421465)
              ·
                refine ⟨21780377233706391061816099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29040502978275188082421465 21780377233706391061816099)
                ·
                  refine ⟨32670565850559586592724149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21780377233706391061816099 32670565850559586592724149)
                  ·
                    refine ⟨3062865548489961243067889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32670565850559586592724149 3062865548489961243067889)
                    ·
                      refine ⟨2297149161367470932300917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062865548489961243067889 2297149161367470932300917)
                      ·
                        rfl

theorem cell23_4473682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_4473682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473682 prefixEnd_4473682 := by exact prefixLift 4473682
  have htrace : WordTrace (prefixWord ++ tailWord_4473682) baseStart_4473682 baseEnd_4473682 := by
    simpa [prefixWord, tailWord_4473682, baseEnd_4473682] using wordTrace_append hprefix tailTrace_4473682
  have hstable : (prefixWord ++ tailWord_4473682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473682).length < 2 ^ (prefixWord ++ tailWord_4473682).sum := by decide
  have hdescent : baseEnd_4473682 < baseStart_4473682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473692 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4473692 : Nat := 118140960795 + 4473692 * 2 ^ 59
def prefixEnd_4473692 : Nat := 4983230072969 + 3 ^ 40 * 4473692 * 2
def baseEnd_4473692 : Nat := 765718098724671964391957

theorem tailTrace_4473692 : CollatzResearch.WordTrace tailWord_4473692 prefixEnd_4473692 765718098724671964391957 := by
  unfold tailWord_4473692
  simp only [CollatzResearch.WordTrace]
  refine ⟨81584476054292702304959665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108779301405723603073279553 81584476054292702304959665)
  ·
    refine ⟨61188357040719526728719749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81584476054292702304959665 61188357040719526728719749)
    ·
      refine ⟨11472816945134911261634953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61188357040719526728719749 11472816945134911261634953)
      ·
        refine ⟨8604612708851183446226215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11472816945134911261634953 8604612708851183446226215)
        ·
          refine ⟨12906919063276775169339323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604612708851183446226215 12906919063276775169339323)
          ·
            refine ⟨19360378594915162754008985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12906919063276775169339323 19360378594915162754008985)
            ·
              refine ⟨14520283946186372065506739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19360378594915162754008985 14520283946186372065506739)
              ·
                refine ⟨21780425919279558098260109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14520283946186372065506739 21780425919279558098260109)
                ·
                  refine ⟨8167659719729834286847541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21780425919279558098260109 8167659719729834286847541)
                  ·
                    refine ⟨765718098724671964391957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8167659719729834286847541 765718098724671964391957)
                    ·
                      rfl

theorem cell23_4473692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4473692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473692 prefixEnd_4473692 := by exact prefixLift 4473692
  have htrace : WordTrace (prefixWord ++ tailWord_4473692) baseStart_4473692 baseEnd_4473692 := by
    simpa [prefixWord, tailWord_4473692, baseEnd_4473692] using wordTrace_append hprefix tailTrace_4473692
  have hstable : (prefixWord ++ tailWord_4473692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473692).length < 2 ^ (prefixWord ++ tailWord_4473692).sum := by decide
  have hdescent : baseEnd_4473692 < baseStart_4473692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473695 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4]
def baseStart_4473695 : Nat := 118140960795 + 4473695 * 2 ^ 59
def prefixEnd_4473695 : Nat := 4983230072969 + 3 ^ 40 * 4473695 * 2
def baseEnd_4473695 : Nat := 2297155836615979381438357

theorem tailTrace_4473695 : CollatzResearch.WordTrace tailWord_4473695 prefixEnd_4473695 2297155836615979381438357 := by
  unfold tailWord_4473695
  simp only [CollatzResearch.WordTrace]
  refine ⟨163169061527574536122278539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108779374351716357414852359 163169061527574536122278539)
  ·
    refine ⟨244753592291361804183417809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163169061527574536122278539 244753592291361804183417809)
    ·
      refine ⟨183565194218521353137563357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244753592291361804183417809 183565194218521353137563357)
      ·
        refine ⟨68836947831945507426586259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183565194218521353137563357 68836947831945507426586259)
        ·
          refine ⟨103255421747918261139879389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68836947831945507426586259 103255421747918261139879389)
          ·
            refine ⟨38720783155469347927454771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103255421747918261139879389 38720783155469347927454771)
            ·
              refine ⟨58081174733204021891182157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38720783155469347927454771 58081174733204021891182157)
              ·
                refine ⟨21780440524951508209193309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58081174733204021891182157 21780440524951508209193309)
                ·
                  refine ⟨8167665196856815578447491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21780440524951508209193309 8167665196856815578447491)
                  ·
                    refine ⟨12251497795285223367671237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8167665196856815578447491 12251497795285223367671237)
                    ·
                      refine ⟨2297155836615979381438357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12251497795285223367671237 2297155836615979381438357)
                      ·
                        rfl

theorem cell23_4473695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_4473695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473695 prefixEnd_4473695 := by exact prefixLift 4473695
  have htrace : WordTrace (prefixWord ++ tailWord_4473695) baseStart_4473695 baseEnd_4473695 := by
    simpa [prefixWord, tailWord_4473695, baseEnd_4473695] using wordTrace_append hprefix tailTrace_4473695
  have hstable : (prefixWord ++ tailWord_4473695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473695).length < 2 ^ (prefixWord ++ tailWord_4473695).sum := by decide
  have hdescent : baseEnd_4473695 < baseStart_4473695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473699 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 2, 3, 2]
def baseStart_4473699 : Nat := 118140960795 + 4473699 * 2 ^ 59
def prefixEnd_4473699 : Nat := 4983230072969 + 3 ^ 40 * 4473699 * 2
def baseEnd_4473699 : Nat := 2297157890538597365788339

theorem tailTrace_4473699 : CollatzResearch.WordTrace tailWord_4473699 prefixEnd_4473699 2297157890538597365788339 := by
  unfold tailWord_4473699
  simp only [CollatzResearch.WordTrace]
  refine ⟨163169207419560044805424151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108779471613040029870282767 163169207419560044805424151)
  ·
    refine ⟨244753811129340067208136227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163169207419560044805424151 244753811129340067208136227)
    ·
      refine ⟨367130716694010100812204341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244753811129340067208136227 367130716694010100812204341)
      ·
        refine ⟨34418504690063446951144157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 367130716694010100812204341 34418504690063446951144157)
        ·
          refine ⟨12906939258773792606679059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34418504690063446951144157 12906939258773792606679059)
          ·
            refine ⟨19360408888160688910018589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12906939258773792606679059 19360408888160688910018589)
            ·
              refine ⟨7260153333060258341256971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19360408888160688910018589 7260153333060258341256971)
              ·
                refine ⟨10890229999590387511885457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7260153333060258341256971 10890229999590387511885457)
                ·
                  refine ⟨8167672499692790633914093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10890229999590387511885457 8167672499692790633914093)
                  ·
                    refine ⟨3062877187384796487717785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8167672499692790633914093 3062877187384796487717785)
                    ·
                      refine ⟨2297157890538597365788339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062877187384796487717785 2297157890538597365788339)
                      ·
                        rfl

theorem cell23_4473699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_4473699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473699 prefixEnd_4473699 := by exact prefixLift 4473699
  have htrace : WordTrace (prefixWord ++ tailWord_4473699) baseStart_4473699 baseEnd_4473699 := by
    simpa [prefixWord, tailWord_4473699, baseEnd_4473699] using wordTrace_append hprefix tailTrace_4473699
  have hstable : (prefixWord ++ tailWord_4473699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473699).length < 2 ^ (prefixWord ++ tailWord_4473699).sum := by decide
  have hdescent : baseEnd_4473699 < baseStart_4473699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473725 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4473725 : Nat := 118140960795 + 4473725 * 2 ^ 59
def prefixEnd_4473725 : Nat := 4983230072969 + 3 ^ 40 * 4473725 * 2
def baseEnd_4473725 : Nat := 2297171241035614264063219

theorem tailTrace_4473725 : CollatzResearch.WordTrace tailWord_4473725 prefixEnd_4473725 2297171241035614264063219 := by
  unfold tailWord_4473725
  simp only [CollatzResearch.WordTrace]
  refine ⟨163170155717465851245870629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108780103811643900830580419 163170155717465851245870629)
  ·
    refine ⟨30594404197024847108600743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163170155717465851245870629 30594404197024847108600743)
    ·
      refine ⟨45891606295537270662901115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30594404197024847108600743 45891606295537270662901115)
      ·
        refine ⟨68837409443305905994351673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45891606295537270662901115 68837409443305905994351673)
        ·
          refine ⟨51628057082479429495763755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68837409443305905994351673 51628057082479429495763755)
          ·
            refine ⟨77442085623719144243645633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51628057082479429495763755 77442085623719144243645633)
            ·
              refine ⟨58081564217789358182734225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77442085623719144243645633 58081564217789358182734225)
              ·
                refine ⟨43561173163342018637050669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58081564217789358182734225 43561173163342018637050669)
                ·
                  refine ⟨16335439936253256988894001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43561173163342018637050669 16335439936253256988894001)
                  ·
                    refine ⟨12251579952189942741670501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16335439936253256988894001 12251579952189942741670501)
                    ·
                      refine ⟨2297171241035614264063219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12251579952189942741670501 2297171241035614264063219)
                      ·
                        rfl

theorem cell23_4473725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4473725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473725 prefixEnd_4473725 := by exact prefixLift 4473725
  have htrace : WordTrace (prefixWord ++ tailWord_4473725) baseStart_4473725 baseEnd_4473725 := by
    simpa [prefixWord, tailWord_4473725, baseEnd_4473725] using wordTrace_append hprefix tailTrace_4473725
  have hstable : (prefixWord ++ tailWord_4473725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473725).length < 2 ^ (prefixWord ++ tailWord_4473725).sum := by decide
  have hdescent : baseEnd_4473725 < baseStart_4473725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473746 : List Nat := [3, 2, 3, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4473746 : Nat := 118140960795 + 4473746 * 2 ^ 59
def prefixEnd_4473746 : Nat := 4983230072969 + 3 ^ 40 * 4473746 * 2
def baseEnd_4473746 : Nat := 2297182024129358681900623

theorem tailTrace_4473746 : CollatzResearch.WordTrace tailWord_4473746 prefixEnd_4473746 2297182024129358681900623 := by
  unfold tailWord_4473746
  simp only [CollatzResearch.WordTrace]
  refine ⟨40792730412597442958096273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108780614433593181221590061 40792730412597442958096273)
  ·
    refine ⟨30594547809448082218572205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40792730412597442958096273 30594547809448082218572205)
    ·
      refine ⟨11472955428543030831964577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30594547809448082218572205 11472955428543030831964577)
      ·
        refine ⟨8604716571407273123973433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11472955428543030831964577 8604716571407273123973433)
        ·
          refine ⟨6453537428555454842980075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8604716571407273123973433 6453537428555454842980075)
          ·
            refine ⟨9680306142833182264470113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453537428555454842980075 9680306142833182264470113)
            ·
              refine ⟨7260229607124886698352585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9680306142833182264470113 7260229607124886698352585)
              ·
                refine ⟨5445172205343665023764439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7260229607124886698352585 5445172205343665023764439)
                ·
                  refine ⟨8167758308015497535646659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445172205343665023764439 8167758308015497535646659)
                  ·
                    refine ⟨12251637462023246303469989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8167758308015497535646659 12251637462023246303469989)
                    ·
                      refine ⟨2297182024129358681900623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12251637462023246303469989 2297182024129358681900623)
                      ·
                        rfl

theorem cell23_4473746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4473746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473746 prefixEnd_4473746 := by exact prefixLift 4473746
  have htrace : WordTrace (prefixWord ++ tailWord_4473746) baseStart_4473746 baseEnd_4473746 := by
    simpa [prefixWord, tailWord_4473746, baseEnd_4473746] using wordTrace_append hprefix tailTrace_4473746
  have hstable : (prefixWord ++ tailWord_4473746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473746).length < 2 ^ (prefixWord ++ tailWord_4473746).sum := by decide
  have hdescent : baseEnd_4473746 < baseStart_4473746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473749 : List Nat := [1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_4473749 : Nat := 118140960795 + 4473749 * 2 ^ 59
def prefixEnd_4473749 : Nat := 4983230072969 + 3 ^ 40 * 4473749 * 2
def baseEnd_4473749 : Nat := 2297183564571322170163109

theorem tailTrace_4473749 : CollatzResearch.WordTrace tailWord_4473749 prefixEnd_4473749 2297183564571322170163109 := by
  unfold tailWord_4473749
  simp only [CollatzResearch.WordTrace]
  refine ⟨163171031069378903344744301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108780687379585935563162867 163171031069378903344744301)
  ·
    refine ⟨61189136651017088754279113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163171031069378903344744301 61189136651017088754279113)
    ·
      refine ⟨45891852488262816565709335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61189136651017088754279113 45891852488262816565709335)
      ·
        refine ⟨68837778732394224848564003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45891852488262816565709335 68837778732394224848564003)
        ·
          refine ⟨103256668098591337272846005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68837778732394224848564003 103256668098591337272846005)
          ·
            refine ⟨9680312634242937869329313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 103256668098591337272846005 9680312634242937869329313)
            ·
              refine ⟨7260234475682203401996985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9680312634242937869329313 7260234475682203401996985)
              ·
                refine ⟨5445175856761652551497739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7260234475682203401996985 5445175856761652551497739)
                ·
                  refine ⟨8167763785142478827246609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445175856761652551497739 8167763785142478827246609)
                  ·
                    refine ⟨6125822838856859120434957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8167763785142478827246609 6125822838856859120434957)
                    ·
                      refine ⟨2297183564571322170163109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125822838856859120434957 2297183564571322170163109)
                      ·
                        rfl

theorem cell23_4473749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_4473749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473749 prefixEnd_4473749 := by exact prefixLift 4473749
  have htrace : WordTrace (prefixWord ++ tailWord_4473749) baseStart_4473749 baseEnd_4473749 := by
    simpa [prefixWord, tailWord_4473749, baseEnd_4473749] using wordTrace_append hprefix tailTrace_4473749
  have hstable : (prefixWord ++ tailWord_4473749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473749).length < 2 ^ (prefixWord ++ tailWord_4473749).sum := by decide
  have hdescent : baseEnd_4473749 < baseStart_4473749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473780 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4473780 : Nat := 118140960795 + 4473780 * 2 ^ 59
def prefixEnd_4473780 : Nat := 4983230072969 + 3 ^ 40 * 4473780 * 2
def baseEnd_4473780 : Nat := 2297199482471611548875467

theorem tailTrace_4473780 : CollatzResearch.WordTrace tailWord_4473780 prefixEnd_4473780 2297199482471611548875467 := by
  unfold tailWord_4473780
  simp only [CollatzResearch.WordTrace]
  refine ⟨81586080866133297819561397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108781441154844397092748529 81586080866133297819561397)
  ·
    refine ⟨7648695081199996670583881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 81586080866133297819561397 7648695081199996670583881)
    ·
      refine ⟨5736521310899997502937911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7648695081199996670583881 5736521310899997502937911)
      ·
        refine ⟨8604781966349996254406867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736521310899997502937911 8604781966349996254406867)
        ·
          refine ⟨12907172949524994381610301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8604781966349996254406867 12907172949524994381610301)
          ·
            refine ⟨4840189856071872893103863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12907172949524994381610301 4840189856071872893103863)
            ·
              refine ⟨7260284784107809339655795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840189856071872893103863 7260284784107809339655795)
              ·
                refine ⟨10890427176161714009483693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7260284784107809339655795 10890427176161714009483693)
                ·
                  refine ⟨4083910191060642753556385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10890427176161714009483693 4083910191060642753556385)
                  ·
                    refine ⟨3062932643295482065167289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4083910191060642753556385 3062932643295482065167289)
                    ·
                      refine ⟨2297199482471611548875467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062932643295482065167289 2297199482471611548875467)
                      ·
                        rfl

theorem cell23_4473780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4473780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473780 prefixEnd_4473780 := by exact prefixLift 4473780
  have htrace : WordTrace (prefixWord ++ tailWord_4473780) baseStart_4473780 baseEnd_4473780 := by
    simpa [prefixWord, tailWord_4473780, baseEnd_4473780] using wordTrace_append hprefix tailTrace_4473780
  have hstable : (prefixWord ++ tailWord_4473780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473780).length < 2 ^ (prefixWord ++ tailWord_4473780).sum := by decide
  have hdescent : baseEnd_4473780 < baseStart_4473780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473806 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_4473806 : Nat := 118140960795 + 4473806 * 2 ^ 59
def prefixEnd_4473806 : Nat := 4983230072969 + 3 ^ 40 * 4473806 * 2
def baseEnd_4473806 : Nat := 2297212832968628447150347

theorem tailTrace_4473806 : CollatzResearch.WordTrace tailWord_4473806 prefixEnd_4473806 2297212832968628447150347 := by
  unfold tailWord_4473806
  simp only [CollatzResearch.WordTrace]
  refine ⟨20396638753771550259946159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108782073353448268053046181 20396638753771550259946159)
  ·
    refine ⟨30594958130657325389919239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20396638753771550259946159 30594958130657325389919239)
    ·
      refine ⟨45892437195985988084878859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30594958130657325389919239 45892437195985988084878859)
      ·
        refine ⟨68838655793978982127318289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45892437195985988084878859 68838655793978982127318289)
        ·
          refine ⟨51628991845484236595488717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68838655793978982127318289 51628991845484236595488717)
          ·
            refine ⟨19360871942056588723308269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51628991845484236595488717 19360871942056588723308269)
            ·
              refine ⟨7260326978271220771240601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19360871942056588723308269 7260326978271220771240601)
              ·
                refine ⟨5445245233703415578430451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7260326978271220771240601 5445245233703415578430451)
                ·
                  refine ⟨8167867850555123367645677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445245233703415578430451 8167867850555123367645677)
                  ·
                    refine ⟨3062950443958171262867129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8167867850555123367645677 3062950443958171262867129)
                    ·
                      refine ⟨2297212832968628447150347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062950443958171262867129 2297212832968628447150347)
                      ·
                        rfl

theorem cell23_4473806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_4473806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473806 prefixEnd_4473806 := by exact prefixLift 4473806
  have htrace : WordTrace (prefixWord ++ tailWord_4473806) baseStart_4473806 baseEnd_4473806 := by
    simpa [prefixWord, tailWord_4473806, baseEnd_4473806] using wordTrace_append hprefix tailTrace_4473806
  have hstable : (prefixWord ++ tailWord_4473806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473806).length < 2 ^ (prefixWord ++ tailWord_4473806).sum := by decide
  have hdescent : baseEnd_4473806 < baseStart_4473806 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473815 : List Nat := [1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4]
def baseStart_4473815 : Nat := 118140960795 + 4473815 * 2 ^ 59
def prefixEnd_4473815 : Nat := 4983230072969 + 3 ^ 40 * 4473815 * 2
def baseEnd_4473815 : Nat := 2297217454294518911937805

theorem tailTrace_4473815 : CollatzResearch.WordTrace tailWord_4473815 prefixEnd_4473815 2297217454294518911937805 := by
  unfold tailWord_4473815
  simp only [CollatzResearch.WordTrace]
  refine ⟨163173438287139796616646899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108782292191426531077764599 163173438287139796616646899)
  ·
    refine ⟨244760157430709694924970349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163173438287139796616646899 244760157430709694924970349)
    ·
      refine ⟨91785059036516135596863881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244760157430709694924970349 91785059036516135596863881)
      ·
        refine ⟨68838794277387101697647911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91785059036516135596863881 68838794277387101697647911)
        ·
          refine ⟨103258191416080652546471867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68838794277387101697647911 103258191416080652546471867)
          ·
            refine ⟨154887287124120978819707801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103258191416080652546471867 154887287124120978819707801)
            ·
              refine ⟨116165465343090734114780851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154887287124120978819707801 116165465343090734114780851)
              ·
                refine ⟨174248198014636101172171277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 116165465343090734114780851 174248198014636101172171277)
                ·
                  refine ⟨65343074255488537939564229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 174248198014636101172171277 65343074255488537939564229)
                  ·
                    refine ⟨12251826422904100863668293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 65343074255488537939564229 12251826422904100863668293)
                    ·
                      refine ⟨2297217454294518911937805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12251826422904100863668293 2297217454294518911937805)
                      ·
                        rfl

theorem cell23_4473815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_4473815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473815 prefixEnd_4473815 := by exact prefixLift 4473815
  have htrace : WordTrace (prefixWord ++ tailWord_4473815) baseStart_4473815 baseEnd_4473815 := by
    simpa [prefixWord, tailWord_4473815, baseEnd_4473815] using wordTrace_append hprefix tailTrace_4473815
  have hstable : (prefixWord ++ tailWord_4473815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473815).length < 2 ^ (prefixWord ++ tailWord_4473815).sum := by decide
  have hdescent : baseEnd_4473815 < baseStart_4473815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473823 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 1, 3, 2]
def baseStart_4473823 : Nat := 118140960795 + 4473823 * 2 ^ 59
def prefixEnd_4473823 : Nat := 4983230072969 + 3 ^ 40 * 4473823 * 2
def baseEnd_4473823 : Nat := 2297221562139754880637769

theorem tailTrace_4473823 : CollatzResearch.WordTrace tailWord_4473823 prefixEnd_4473823 2297221562139754880637769 := by
  unfold tailWord_4473823
  simp only [CollatzResearch.WordTrace]
  refine ⟨163173730071110813982938123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108782486714073875988625415 163173730071110813982938123)
  ·
    refine ⟨244760595106666220974407185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163173730071110813982938123 244760595106666220974407185)
    ·
      refine ⟨183570446329999665730805389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244760595106666220974407185 183570446329999665730805389)
      ·
        refine ⟨68838917373749874649052021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183570446329999665730805389 68838917373749874649052021)
        ·
          refine ⟨6453648503789050748348627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68838917373749874649052021 6453648503789050748348627)
          ·
            refine ⟨9680472755683576122522941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6453648503789050748348627 9680472755683576122522941)
            ·
              refine ⟨3630177283381341045946103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9680472755683576122522941 3630177283381341045946103)
              ·
                refine ⟨5445265925072011568919155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630177283381341045946103 5445265925072011568919155)
                ·
                  refine ⟨8167898887608017353378733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445265925072011568919155 8167898887608017353378733)
                  ·
                    refine ⟨3062962082853006507517025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8167898887608017353378733 3062962082853006507517025)
                    ·
                      refine ⟨2297221562139754880637769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062962082853006507517025 2297221562139754880637769)
                      ·
                        rfl

theorem cell23_4473823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_4473823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473823 prefixEnd_4473823 := by exact prefixLift 4473823
  have htrace : WordTrace (prefixWord ++ tailWord_4473823) baseStart_4473823 baseEnd_4473823 := by
    simpa [prefixWord, tailWord_4473823, baseEnd_4473823] using wordTrace_append hprefix tailTrace_4473823
  have hstable : (prefixWord ++ tailWord_4473823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473823).length < 2 ^ (prefixWord ++ tailWord_4473823).sum := by decide
  have hdescent : baseEnd_4473823 < baseStart_4473823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473852 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_4473852 : Nat := 118140960795 + 4473852 * 2 ^ 59
def prefixEnd_4473852 : Nat := 4983230072969 + 3 ^ 40 * 4473852 * 2
def baseEnd_4473852 : Nat := 2297236453078735267175135

theorem tailTrace_4473852 : CollatzResearch.WordTrace tailWord_4473852 prefixEnd_4473852 2297236453078735267175135 := by
  unfold tailWord_4473852
  simp only [CollatzResearch.WordTrace]
  refine ⟨81587393894002875967871905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108783191858670501290495873 81587393894002875967871905)
  ·
    refine ⟨61190545420502156975903929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81587393894002875967871905 61190545420502156975903929)
    ·
      refine ⟨45892909065376617731927947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61190545420502156975903929 45892909065376617731927947)
      ·
        refine ⟨68839363598064926597891921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45892909065376617731927947 68839363598064926597891921)
        ·
          refine ⟨51629522698548694948418941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68839363598064926597891921 51629522698548694948418941)
          ·
            refine ⟨19361071011955760605657103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51629522698548694948418941 19361071011955760605657103)
            ·
              refine ⟨29041606517933640908485655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19361071011955760605657103 29041606517933640908485655)
              ·
                refine ⟨43562409776900461362728483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29041606517933640908485655 43562409776900461362728483)
                ·
                  refine ⟨65343614665350692044092725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43562409776900461362728483 65343614665350692044092725)
                  ·
                    refine ⟨6125963874876627379133693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65343614665350692044092725 6125963874876627379133693)
                    ·
                      refine ⟨2297236453078735267175135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6125963874876627379133693 2297236453078735267175135)
                      ·
                        rfl

theorem cell23_4473852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_4473852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473852 prefixEnd_4473852 := by exact prefixLift 4473852
  have htrace : WordTrace (prefixWord ++ tailWord_4473852) baseStart_4473852 baseEnd_4473852 := by
    simpa [prefixWord, tailWord_4473852, baseEnd_4473852] using wordTrace_append hprefix tailTrace_4473852
  have hstable : (prefixWord ++ tailWord_4473852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473852).length < 2 ^ (prefixWord ++ tailWord_4473852).sum := by decide
  have hdescent : baseEnd_4473852 < baseStart_4473852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473865 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 7]
def baseStart_4473865 : Nat := 118140960795 + 4473865 * 2 ^ 59
def prefixEnd_4473865 : Nat := 4983230072969 + 3 ^ 40 * 4473865 * 2
def baseEnd_4473865 : Nat := 2297243128327243716312575

theorem tailTrace_4473865 : CollatzResearch.WordTrace tailWord_4473865 prefixEnd_4473865 2297243128327243716312575 := by
  unfold tailWord_4473865
  simp only [CollatzResearch.WordTrace]
  refine ⟨163175261936958655155967049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108783507957972436770644699 163175261936958655155967049)
  ·
    refine ⟨122381446452718991366975287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163175261936958655155967049 122381446452718991366975287)
    ·
      refine ⟨183572169679078487050462931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122381446452718991366975287 183572169679078487050462931)
      ·
        refine ⟨275358254518617730575694397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183572169679078487050462931 275358254518617730575694397)
        ·
          refine ⟨103259345444481648965885399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275358254518617730575694397 103259345444481648965885399)
          ·
            refine ⟨154889018166722473448828099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103259345444481648965885399 154889018166722473448828099)
            ·
              refine ⟨232333527250083710173242149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154889018166722473448828099 232333527250083710173242149)
              ·
                refine ⟨43562536359390695657482903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 232333527250083710173242149 43562536359390695657482903)
                ·
                  refine ⟨65343804539086043486224355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43562536359390695657482903 65343804539086043486224355)
                  ·
                    refine ⟨98015706808629065229336533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 65343804539086043486224355 98015706808629065229336533)
                    ·
                      refine ⟨2297243128327243716312575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 98015706808629065229336533 2297243128327243716312575)
                      ·
                        rfl

theorem cell23_4473865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_4473865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473865 prefixEnd_4473865 := by exact prefixLift 4473865
  have htrace : WordTrace (prefixWord ++ tailWord_4473865) baseStart_4473865 baseEnd_4473865 := by
    simpa [prefixWord, tailWord_4473865, baseEnd_4473865] using wordTrace_append hprefix tailTrace_4473865
  have hstable : (prefixWord ++ tailWord_4473865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473865).length < 2 ^ (prefixWord ++ tailWord_4473865).sum := by decide
  have hdescent : baseEnd_4473865 < baseStart_4473865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473874 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_4473874 : Nat := 118140960795 + 4473874 * 2 ^ 59
def prefixEnd_4473874 : Nat := 4983230072969 + 3 ^ 40 * 4473874 * 2
def baseEnd_4473874 : Nat := 2297247749653134181100035

theorem tailTrace_4473874 : CollatzResearch.WordTrace tailWord_4473874 prefixEnd_4473874 2297247749653134181100035 := by
  unfold tailWord_4473874
  simp only [CollatzResearch.WordTrace]
  refine ⟨40793897548481512423261169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108783726795950699795363117 40793897548481512423261169)
  ·
    refine ⟨30595423161361134317445877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40793897548481512423261169 30595423161361134317445877)
    ·
      refine ⟨2868320921377606342260551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30595423161361134317445877 2868320921377606342260551)
      ·
        refine ⟨4302481382066409513390827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868320921377606342260551 4302481382066409513390827)
        ·
          refine ⟨6453722073099614270086241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302481382066409513390827 6453722073099614270086241)
          ·
            refine ⟨4840291554824710702564681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6453722073099614270086241 4840291554824710702564681)
            ·
              refine ⟨3630218666118533026923511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840291554824710702564681 3630218666118533026923511)
              ·
                refine ⟨5445327999177799540385267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630218666118533026923511 5445327999177799540385267)
                ·
                  refine ⟨8167991998766699310577901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445327999177799540385267 8167991998766699310577901)
                  ·
                    refine ⟨3062996999537512241466713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8167991998766699310577901 3062996999537512241466713)
                    ·
                      refine ⟨2297247749653134181100035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3062996999537512241466713 2297247749653134181100035)
                      ·
                        rfl

theorem cell23_4473874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_4473874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473874 prefixEnd_4473874 := by exact prefixLift 4473874
  have htrace : WordTrace (prefixWord ++ tailWord_4473874) baseStart_4473874 baseEnd_4473874 := by
    simpa [prefixWord, tailWord_4473874, baseEnd_4473874] using wordTrace_append hprefix tailTrace_4473874
  have hstable : (prefixWord ++ tailWord_4473874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473874).length < 2 ^ (prefixWord ++ tailWord_4473874).sum := by decide
  have hdescent : baseEnd_4473874 < baseStart_4473874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473915 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 12]
def baseStart_4473915 : Nat := 118140960795 + 4473915 * 2 ^ 59
def prefixEnd_4473915 : Nat := 4983230072969 + 3 ^ 40 * 4473915 * 2
def baseEnd_4473915 : Nat := 255252089151107613409705

theorem tailTrace_4473915 : CollatzResearch.WordTrace tailWord_4473915 prefixEnd_4473915 255252089151107613409705 := by
  unfold tailWord_4473915
  simp only [CollatzResearch.WordTrace]
  refine ⟨163177085586777513695287199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108784723724518342463524799 163177085586777513695287199)
  ·
    refine ⟨244765628380166270542930799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163177085586777513695287199 244765628380166270542930799)
    ·
      refine ⟨367148442570249405814396199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244765628380166270542930799 367148442570249405814396199)
      ·
        refine ⟨550722663855374108721594299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367148442570249405814396199 550722663855374108721594299)
        ·
          refine ⟨826083995783061163082391449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550722663855374108721594299 826083995783061163082391449)
          ·
            refine ⟨619562996837295872311793587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 826083995783061163082391449 619562996837295872311793587)
            ·
              refine ⟨929344495255943808467690381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619562996837295872311793587 929344495255943808467690381)
              ·
                refine ⟨348504185720978928175383893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 929344495255943808467690381 348504185720978928175383893)
                ·
                  refine ⟨255252089151107613409705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 348504185720978928175383893 255252089151107613409705)
                  ·
                    rfl

theorem cell23_4473915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 12].length) (baseStart_4473915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473915 prefixEnd_4473915 := by exact prefixLift 4473915
  have htrace : WordTrace (prefixWord ++ tailWord_4473915) baseStart_4473915 baseEnd_4473915 := by
    simpa [prefixWord, tailWord_4473915, baseEnd_4473915] using wordTrace_append hprefix tailTrace_4473915
  have hstable : (prefixWord ++ tailWord_4473915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473915).length < 2 ^ (prefixWord ++ tailWord_4473915).sum := by decide
  have hdescent : baseEnd_4473915 < baseStart_4473915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473926 : List Nat := [6, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4473926 : Nat := 118140960795 + 4473926 * 2 ^ 59
def prefixEnd_4473926 : Nat := 4983230072969 + 3 ^ 40 * 4473926 * 2
def baseEnd_4473926 : Nat := 2297274450647167977649795

theorem tailTrace_4473926 : CollatzResearch.WordTrace tailWord_4473926 prefixEnd_4473926 2297274450647167977649795 := by
  unfold tailWord_4473926
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099296462179301955435551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108784991193158441715958421 5099296462179301955435551)
  ·
    refine ⟨7648944693268952933153327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5099296462179301955435551 7648944693268952933153327)
    ·
      refine ⟨11473417039903429399729991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7648944693268952933153327 11473417039903429399729991)
      ·
        refine ⟨17210125559855144099594987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11473417039903429399729991 17210125559855144099594987)
        ·
          refine ⟨25815188339782716149392481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17210125559855144099594987 25815188339782716149392481)
          ·
            refine ⟨19361391254837037112044361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25815188339782716149392481 19361391254837037112044361)
            ·
              refine ⟨14521043441127777834033271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19361391254837037112044361 14521043441127777834033271)
              ·
                refine ⟨21781565161691666751049907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14521043441127777834033271 21781565161691666751049907)
                ·
                  refine ⟨32672347742537500126574861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21781565161691666751049907 32672347742537500126574861)
                  ·
                    refine ⟨12252130403451562547465573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32672347742537500126574861 12252130403451562547465573)
                    ·
                      refine ⟨2297274450647167977649795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12252130403451562547465573 2297274450647167977649795)
                      ·
                        rfl

theorem cell23_4473926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4473926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473926 prefixEnd_4473926 := by exact prefixLift 4473926
  have htrace : WordTrace (prefixWord ++ tailWord_4473926) baseStart_4473926 baseEnd_4473926 := by
    simpa [prefixWord, tailWord_4473926, baseEnd_4473926] using wordTrace_append hprefix tailTrace_4473926
  have hstable : (prefixWord ++ tailWord_4473926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473926).length < 2 ^ (prefixWord ++ tailWord_4473926).sum := by decide
  have hdescent : baseEnd_4473926 < baseStart_4473926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473966 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 6]
def baseStart_4473966 : Nat := 118140960795 + 4473966 * 2 ^ 59
def prefixEnd_4473966 : Nat := 4983230072969 + 3 ^ 40 * 4473966 * 2
def baseEnd_4473966 : Nat := 255254998874816424572179

theorem tailTrace_4473966 : CollatzResearch.WordTrace tailWord_4473966 prefixEnd_4473966 255254998874816424572179 := by
  unfold tailWord_4473966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20397368213699093675674219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108785963806395166270262501 20397368213699093675674219)
  ·
    refine ⟨30596052320548640513511329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20397368213699093675674219 30596052320548640513511329)
    ·
      refine ⟨22947039240411480385133497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30596052320548640513511329 22947039240411480385133497)
      ·
        refine ⟨17210279430308610288850123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22947039240411480385133497 17210279430308610288850123)
        ·
          refine ⟨25815419145462915433275185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17210279430308610288850123 25815419145462915433275185)
          ·
            refine ⟨19361564359097186574956389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25815419145462915433275185 19361564359097186574956389)
            ·
              refine ⟨3630293317330722482804323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19361564359097186574956389 3630293317330722482804323)
              ·
                refine ⟨5445439975996083724206485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630293317330722482804323 5445439975996083724206485)
                ·
                  refine ⟨255254998874816424572179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5445439975996083724206485 255254998874816424572179)
                  ·
                    rfl

theorem cell23_4473966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_4473966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473966 prefixEnd_4473966 := by exact prefixLift 4473966
  have htrace : WordTrace (prefixWord ++ tailWord_4473966) baseStart_4473966 baseEnd_4473966 := by
    simpa [prefixWord, tailWord_4473966, baseEnd_4473966] using wordTrace_append hprefix tailTrace_4473966
  have hstable : (prefixWord ++ tailWord_4473966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473966).length < 2 ^ (prefixWord ++ tailWord_4473966).sum := by decide
  have hdescent : baseEnd_4473966 < baseStart_4473966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4473969 : List Nat := [1, 2, 2, 2, 1, 1, 2, 4, 1, 5, 2]
def baseStart_4473969 : Nat := 118140960795 + 4473969 * 2 ^ 59
def prefixEnd_4473969 : Nat := 4983230072969 + 3 ^ 40 * 4473969 * 2
def baseEnd_4473969 : Nat := 2297296530315311309412097

theorem tailTrace_4473969 : CollatzResearch.WordTrace tailWord_4473969 prefixEnd_4473969 2297296530315311309412097 := by
  unfold tailWord_4473969
  simp only [CollatzResearch.WordTrace]
  refine ⟨163179055128581880917752961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108786036752387920611835307 163179055128581880917752961)
  ·
    refine ⟨122384291346436410688314721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163179055128581880917752961 122384291346436410688314721)
    ·
      refine ⟨91788218509827308016236041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122384291346436410688314721 91788218509827308016236041)
      ·
        refine ⟨68841163882370481012177031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91788218509827308016236041 68841163882370481012177031)
        ·
          refine ⟨103261745823555721518265547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68841163882370481012177031 103261745823555721518265547)
          ·
            refine ⟨154892618735333582277398321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103261745823555721518265547 154892618735333582277398321)
            ·
              refine ⟨116169464051500186708048741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154892618735333582277398321 116169464051500186708048741)
              ·
                refine ⟨21781774509656285007759139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 116169464051500186708048741 21781774509656285007759139)
                ·
                  refine ⟨32672661764484427511638709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21781774509656285007759139 32672661764484427511638709)
                  ·
                    refine ⟨3063062040420415079216129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32672661764484427511638709 3063062040420415079216129)
                    ·
                      refine ⟨2297296530315311309412097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063062040420415079216129 2297296530315311309412097)
                      ·
                        rfl

theorem cell23_4473969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_4473969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4473969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4473969 prefixEnd_4473969 := by exact prefixLift 4473969
  have htrace : WordTrace (prefixWord ++ tailWord_4473969) baseStart_4473969 baseEnd_4473969 := by
    simpa [prefixWord, tailWord_4473969, baseEnd_4473969] using wordTrace_append hprefix tailTrace_4473969
  have hstable : (prefixWord ++ tailWord_4473969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4473969).length < 2 ^ (prefixWord ++ tailWord_4473969).sum := by decide
  have hdescent : baseEnd_4473969 < baseStart_4473969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4473969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474010 : List Nat := [3, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4474010 : Nat := 118140960795 + 4474010 * 2 ^ 59
def prefixEnd_4474010 : Nat := 4983230072969 + 3 ^ 40 * 4474010 * 2
def baseEnd_4474010 : Nat := 2297317583022145648999409

theorem tailTrace_4474010 : CollatzResearch.WordTrace tailWord_4474010 prefixEnd_4474010 2297317583022145648999409 := by
  unfold tailWord_4474010
  simp only [CollatzResearch.WordTrace]
  refine ⟨40795137630358336229998871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108787033680955563279996989 40795137630358336229998871)
  ·
    refine ⟨61192706445537504344998307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40795137630358336229998871 61192706445537504344998307)
    ·
      refine ⟨91789059668306256517497461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61192706445537504344998307 91789059668306256517497461)
      ·
        refine ⟨8605224343903711548515387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91789059668306256517497461 8605224343903711548515387)
        ·
          refine ⟨12907836515855567322773081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605224343903711548515387 12907836515855567322773081)
          ·
            refine ⟨9680877386891675492079811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12907836515855567322773081 9680877386891675492079811)
            ·
              refine ⟨14521316080337513238119717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9680877386891675492079811 14521316080337513238119717)
              ·
                refine ⟨2722746765063283732147447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14521316080337513238119717 2722746765063283732147447)
                ·
                  refine ⟨4084120147594925598221171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722746765063283732147447 4084120147594925598221171)
                  ·
                    refine ⟨6126180221392388397331757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4084120147594925598221171 6126180221392388397331757)
                    ·
                      refine ⟨2297317583022145648999409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6126180221392388397331757 2297317583022145648999409)
                      ·
                        rfl

theorem cell23_4474010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4474010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474010 prefixEnd_4474010 := by exact prefixLift 4474010
  have htrace : WordTrace (prefixWord ++ tailWord_4474010) baseStart_4474010 baseEnd_4474010 := by
    simpa [prefixWord, tailWord_4474010, baseEnd_4474010] using wordTrace_append hprefix tailTrace_4474010
  have hstable : (prefixWord ++ tailWord_4474010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474010).length < 2 ^ (prefixWord ++ tailWord_4474010).sum := by decide
  have hdescent : baseEnd_4474010 < baseStart_4474010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474026 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4474026 : Nat := 118140960795 + 4474026 * 2 ^ 59
def prefixEnd_4474026 : Nat := 4983230072969 + 3 ^ 40 * 4474026 * 2
def baseEnd_4474026 : Nat := 765775266237539195466445

theorem tailTrace_4474026 : CollatzResearch.WordTrace tailWord_4474026 prefixEnd_4474026 765775266237539195466445 := by
  unfold tailWord_4474026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40795283522343844913144483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108787422726250253101718621 40795283522343844913144483)
  ·
    refine ⟨61192925283515767369716725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40795283522343844913144483 61192925283515767369716725)
    ·
      refine ⟨5736836745329603190910943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 61192925283515767369716725 5736836745329603190910943)
      ·
        refine ⟨8605255117994404786366415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5736836745329603190910943 8605255117994404786366415)
        ·
          refine ⟨12907882676991607179549623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605255117994404786366415 12907882676991607179549623)
          ·
            refine ⟨19361824015487410769324435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12907882676991607179549623 19361824015487410769324435)
            ·
              refine ⟨29042736023231116153986653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19361824015487410769324435 29042736023231116153986653)
              ·
                refine ⟨10891026008711668557744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29042736023231116153986653 10891026008711668557744995)
                ·
                  refine ⟨16336539013067502836617493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10891026008711668557744995 16336539013067502836617493)
                  ·
                    refine ⟨765775266237539195466445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16336539013067502836617493 765775266237539195466445)
                    ·
                      rfl

theorem cell23_4474026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4474026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474026 prefixEnd_4474026 := by exact prefixLift 4474026
  have htrace : WordTrace (prefixWord ++ tailWord_4474026) baseStart_4474026 baseEnd_4474026 := by
    simpa [prefixWord, tailWord_4474026, baseEnd_4474026] using wordTrace_append hprefix tailTrace_4474026
  have hstable : (prefixWord ++ tailWord_4474026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474026).length < 2 ^ (prefixWord ++ tailWord_4474026).sum := by decide
  have hdescent : baseEnd_4474026 < baseStart_4474026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474033 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 5, 2, 2]
def baseStart_4474033 : Nat := 118140960795 + 4474033 * 2 ^ 59
def prefixEnd_4474033 : Nat := 4983230072969 + 3 ^ 40 * 4474033 * 2
def baseEnd_4474033 : Nat := 2297329393077199059011803

theorem tailTrace_4474033 : CollatzResearch.WordTrace tailWord_4474033 prefixEnd_4474033 2297329393077199059011803 := by
  unfold tailWord_4474033
  simp only [CollatzResearch.WordTrace]
  refine ⟨163181389400350019848082753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108787592933566679898721835 163181389400350019848082753)
  ·
    refine ⟨122386042050262514886062065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163181389400350019848082753 122386042050262514886062065)
    ·
      refine ⟨91789531537696886164546549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122386042050262514886062065 91789531537696886164546549)
      ·
        refine ⟨8605268581659083077926239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91789531537696886164546549 8605268581659083077926239)
        ·
          refine ⟨12907902872488624616889359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605268581659083077926239 12907902872488624616889359)
          ·
            refine ⟨19361854308732936925334039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12907902872488624616889359 19361854308732936925334039)
            ·
              refine ⟨29042781463099405388001059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19361854308732936925334039 29042781463099405388001059)
              ·
                refine ⟨43564172194649108082001589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29042781463099405388001059 43564172194649108082001589)
                ·
                  refine ⟨4084141143248353882687649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43564172194649108082001589 4084141143248353882687649)
                  ·
                    refine ⟨3063105857436265412015737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084141143248353882687649 3063105857436265412015737)
                    ·
                      refine ⟨2297329393077199059011803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063105857436265412015737 2297329393077199059011803)
                      ·
                        rfl

theorem cell23_4474033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_4474033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474033 prefixEnd_4474033 := by exact prefixLift 4474033
  have htrace : WordTrace (prefixWord ++ tailWord_4474033) baseStart_4474033 baseEnd_4474033 := by
    simpa [prefixWord, tailWord_4474033, baseEnd_4474033] using wordTrace_append hprefix tailTrace_4474033
  have hstable : (prefixWord ++ tailWord_4474033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474033).length < 2 ^ (prefixWord ++ tailWord_4474033).sum := by decide
  have hdescent : baseEnd_4474033 < baseStart_4474033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474039 : List Nat := [1, 1, 3, 1, 4, 1, 5, 7]
def baseStart_4474039 : Nat := 118140960795 + 4474039 * 2 ^ 59
def prefixEnd_4474039 : Nat := 4983230072969 + 3 ^ 40 * 4474039 * 2
def baseEnd_4474039 : Nat := 85086387924486149464325

theorem tailTrace_4474039 : CollatzResearch.WordTrace tailWord_4474039 prefixEnd_4474039 85086387924486149464325 := by
  unfold tailWord_4474039
  simp only [CollatzResearch.WordTrace]
  refine ⟨163181608238328282872801171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108787738825552188581867447 163181608238328282872801171)
  ·
    refine ⟨244772412357492424309201757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163181608238328282872801171 244772412357492424309201757)
    ·
      refine ⟨91789654634059659115950659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244772412357492424309201757 91789654634059659115950659)
      ·
        refine ⟨137684481951089488673925989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91789654634059659115950659 137684481951089488673925989)
        ·
          refine ⟨25815840365829279126361123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 137684481951089488673925989 25815840365829279126361123)
          ·
            refine ⟨38723760548743918689541685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25815840365829279126361123 38723760548743918689541685)
            ·
              refine ⟨3630352551444742377144533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38723760548743918689541685 3630352551444742377144533)
              ·
                refine ⟨85086387924486149464325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3630352551444742377144533 85086387924486149464325)
                ·
                  rfl

theorem cell23_4474039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 7].length) (baseStart_4474039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474039 prefixEnd_4474039 := by exact prefixLift 4474039
  have htrace : WordTrace (prefixWord ++ tailWord_4474039) baseStart_4474039 baseEnd_4474039 := by
    simpa [prefixWord, tailWord_4474039, baseEnd_4474039] using wordTrace_append hprefix tailTrace_4474039
  have hstable : (prefixWord ++ tailWord_4474039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474039).length < 2 ^ (prefixWord ++ tailWord_4474039).sum := by decide
  have hdescent : baseEnd_4474039 < baseStart_4474039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474046 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_4474046 : Nat := 118140960795 + 4474046 * 2 ^ 59
def prefixEnd_4474046 : Nat := 4983230072969 + 3 ^ 40 * 4474046 * 2
def baseEnd_4474046 : Nat := 2297336068325707508149243

theorem tailTrace_4474046 : CollatzResearch.WordTrace tailWord_4474046 prefixEnd_4474046 2297336068325707508149243 := by
  unfold tailWord_4474046
  simp only [CollatzResearch.WordTrace]
  refine ⟨20397732943662865383538249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108787909032868615378870661 20397732943662865383538249)
  ·
    refine ⟨15298299707747149037653687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20397732943662865383538249 15298299707747149037653687)
    ·
      refine ⟨22947449561620723556480531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298299707747149037653687 22947449561620723556480531)
      ·
        refine ⟨34421174342431085334720797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22947449561620723556480531 34421174342431085334720797)
        ·
          refine ⟨12907940378411657000520299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34421174342431085334720797 12907940378411657000520299)
          ·
            refine ⟨19361910567617485500780449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12907940378411657000520299 19361910567617485500780449)
            ·
              refine ⟨14521432925713114125585337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19361910567617485500780449 14521432925713114125585337)
              ·
                refine ⟨10891074694284835594189003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14521432925713114125585337 10891074694284835594189003)
                ·
                  refine ⟨16336612041427253391283505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10891074694284835594189003 16336612041427253391283505)
                  ·
                    refine ⟨12252459031070440043462629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16336612041427253391283505 12252459031070440043462629)
                    ·
                      refine ⟨2297336068325707508149243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12252459031070440043462629 2297336068325707508149243)
                      ·
                        rfl

theorem cell23_4474046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_4474046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474046 prefixEnd_4474046 := by exact prefixLift 4474046
  have htrace : WordTrace (prefixWord ++ tailWord_4474046) baseStart_4474046 baseEnd_4474046 := by
    simpa [prefixWord, tailWord_4474046, baseEnd_4474046] using wordTrace_append hprefix tailTrace_4474046
  have hstable : (prefixWord ++ tailWord_4474046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474046).length < 2 ^ (prefixWord ++ tailWord_4474046).sum := by decide
  have hdescent : baseEnd_4474046 < baseStart_4474046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474106 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_4474106 : Nat := 118140960795 + 4474106 * 2 ^ 59
def prefixEnd_4474106 : Nat := 4983230072969 + 3 ^ 40 * 4474106 * 2
def baseEnd_4474106 : Nat := 2297366877164977273398967

theorem tailTrace_4474106 : CollatzResearch.WordTrace tailWord_4474106 prefixEnd_4474106 2297366877164977273398967 := by
  unfold tailWord_4474106
  simp only [CollatzResearch.WordTrace]
  refine ⟨40796012982271388328872543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108789367952723702210326781 40796012982271388328872543)
  ·
    refine ⟨61194019473407082493308815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40796012982271388328872543 61194019473407082493308815)
    ·
      refine ⟨91791029210110623739963223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61194019473407082493308815 91791029210110623739963223)
      ·
        refine ⟨137686543815165935609944835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91791029210110623739963223 137686543815165935609944835)
        ·
          refine ⟨206529815722748903414917253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137686543815165935609944835 206529815722748903414917253)
          ·
            refine ⟨38724340448015419390296985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206529815722748903414917253 38724340448015419390296985)
            ·
              refine ⟨29043255336011564542722739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38724340448015419390296985 29043255336011564542722739)
              ·
                refine ⟨43564883004017346814084109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29043255336011564542722739 43564883004017346814084109)
                ·
                  refine ⟨16336831126506505055281541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43564883004017346814084109 16336831126506505055281541)
                  ·
                    refine ⟨3063155836219969697865289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16336831126506505055281541 3063155836219969697865289)
                    ·
                      refine ⟨2297366877164977273398967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063155836219969697865289 2297366877164977273398967)
                      ·
                        rfl

theorem cell23_4474106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_4474106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474106 prefixEnd_4474106 := by exact prefixLift 4474106
  have htrace : WordTrace (prefixWord ++ tailWord_4474106) baseStart_4474106 baseEnd_4474106 := by
    simpa [prefixWord, tailWord_4474106, baseEnd_4474106] using wordTrace_append hprefix tailTrace_4474106
  have hstable : (prefixWord ++ tailWord_4474106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474106).length < 2 ^ (prefixWord ++ tailWord_4474106).sum := by decide
  have hdescent : baseEnd_4474106 < baseStart_4474106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474109 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_4474109 : Nat := 118140960795 + 4474109 * 2 ^ 59
def prefixEnd_4474109 : Nat := 4983230072969 + 3 ^ 40 * 4474109 * 2
def baseEnd_4474109 : Nat := 2297368417606940761661453

theorem tailTrace_4474109 : CollatzResearch.WordTrace tailWord_4474109 prefixEnd_4474109 2297368417606940761661453 := by
  unfold tailWord_4474109
  simp only [CollatzResearch.WordTrace]
  refine ⟨163184161348074684827849381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108789440898716456551899587 163184161348074684827849381)
  ·
    refine ⟨30597030252764003405221759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163184161348074684827849381 30597030252764003405221759)
    ·
      refine ⟨45895545379146005107832639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30597030252764003405221759 45895545379146005107832639)
      ·
        refine ⟨68843318068719007661748959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45895545379146005107832639 68843318068719007661748959)
        ·
          refine ⟨103264977103078511492623439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68843318068719007661748959 103264977103078511492623439)
          ·
            refine ⟨154897465654617767238935159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103264977103078511492623439 154897465654617767238935159)
            ·
              refine ⟨232346198481926650858402739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154897465654617767238935159 232346198481926650858402739)
              ·
                refine ⟨348519297722889976287604109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232346198481926650858402739 348519297722889976287604109)
                ·
                  refine ⟨130694736646083741107851541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 348519297722889976287604109 130694736646083741107851541)
                  ·
                    refine ⟨6126315780285175364430541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 130694736646083741107851541 6126315780285175364430541)
                    ·
                      refine ⟨2297368417606940761661453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6126315780285175364430541 2297368417606940761661453)
                      ·
                        rfl

theorem cell23_4474109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_4474109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474109 prefixEnd_4474109 := by exact prefixLift 4474109
  have htrace : WordTrace (prefixWord ++ tailWord_4474109) baseStart_4474109 baseEnd_4474109 := by
    simpa [prefixWord, tailWord_4474109, baseEnd_4474109] using wordTrace_append hprefix tailTrace_4474109
  have hstable : (prefixWord ++ tailWord_4474109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474109).length < 2 ^ (prefixWord ++ tailWord_4474109).sum := by decide
  have hdescent : baseEnd_4474109 < baseStart_4474109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474110 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_4474110 : Nat := 118140960795 + 4474110 * 2 ^ 59
def prefixEnd_4474110 : Nat := 4983230072969 + 3 ^ 40 * 4474110 * 2
def baseEnd_4474110 : Nat := 2297368931087595257748949

theorem tailTrace_4474110 : CollatzResearch.WordTrace tailWord_4474110 prefixEnd_4474110 2297368931087595257748949 := by
  unfold tailWord_4474110
  simp only [CollatzResearch.WordTrace]
  refine ⟨20398024727633882749829473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108789465214047374665757189 20398024727633882749829473)
  ·
    refine ⟨15298518545725412062372105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20398024727633882749829473 15298518545725412062372105)
    ·
      refine ⟨11473888909294059046779079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15298518545725412062372105 11473888909294059046779079)
      ·
        refine ⟨17210833363941088570168619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11473888909294059046779079 17210833363941088570168619)
        ·
          refine ⟨25816250045911632855252929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17210833363941088570168619 25816250045911632855252929)
          ·
            refine ⟨19362187534433724641439697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25816250045911632855252929 19362187534433724641439697)
            ·
              refine ⟨14521640650825293481079773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19362187534433724641439697 14521640650825293481079773)
              ·
                refine ⟨5445615244059485055404915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14521640650825293481079773 5445615244059485055404915)
                ·
                  refine ⟨8168422866089227583107373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445615244059485055404915 8168422866089227583107373)
                  ·
                    refine ⟨3063158574783460343665265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8168422866089227583107373 3063158574783460343665265)
                    ·
                      refine ⟨2297368931087595257748949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063158574783460343665265 2297368931087595257748949)
                      ·
                        rfl

theorem cell23_4474110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_4474110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474110 prefixEnd_4474110 := by exact prefixLift 4474110
  have htrace : WordTrace (prefixWord ++ tailWord_4474110) baseStart_4474110 baseEnd_4474110 := by
    simpa [prefixWord, tailWord_4474110, baseEnd_4474110] using wordTrace_append hprefix tailTrace_4474110
  have hstable : (prefixWord ++ tailWord_4474110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474110).length < 2 ^ (prefixWord ++ tailWord_4474110).sum := by decide
  have hdescent : baseEnd_4474110 < baseStart_4474110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474123 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 4, 2, 2]
def baseStart_4474123 : Nat := 118140960795 + 4474123 * 2 ^ 59
def prefixEnd_4474123 : Nat := 4983230072969 + 3 ^ 40 * 4474123 * 2
def baseEnd_4474123 : Nat := 2297375606336103706886389

theorem tailTrace_4474123 : CollatzResearch.WordTrace tailWord_4474123 prefixEnd_4474123 2297375606336103706886389 := by
  unfold tailWord_4474123
  simp only [CollatzResearch.WordTrace]
  refine ⟨163184671970023965218859023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108789781313349310145906015 163184671970023965218859023)
  ·
    refine ⟨244777007955035947828288535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163184671970023965218859023 244777007955035947828288535)
    ·
      refine ⟨367165511932553921742432803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244777007955035947828288535 367165511932553921742432803)
      ·
        refine ⟨550748267898830882613649205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367165511932553921742432803 550748267898830882613649205)
        ·
          refine ⟨51632650115515395245029613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 550748267898830882613649205 51632650115515395245029613)
          ·
            refine ⟨19362243793318273216886105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51632650115515395245029613 19362243793318273216886105)
            ·
              refine ⟨14521682844988704912664579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19362243793318273216886105 14521682844988704912664579)
              ·
                refine ⟨21782524267483057368996869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14521682844988704912664579 21782524267483057368996869)
                ·
                  refine ⟨4084223300153073256686913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21782524267483057368996869 4084223300153073256686913)
                  ·
                    refine ⟨3063167475114804942515185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084223300153073256686913 3063167475114804942515185)
                    ·
                      refine ⟨2297375606336103706886389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063167475114804942515185 2297375606336103706886389)
                      ·
                        rfl

theorem cell23_4474123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 2, 2].length) (baseStart_4474123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474123 prefixEnd_4474123 := by exact prefixLift 4474123
  have htrace : WordTrace (prefixWord ++ tailWord_4474123) baseStart_4474123 baseEnd_4474123 := by
    simpa [prefixWord, tailWord_4474123, baseEnd_4474123] using wordTrace_append hprefix tailTrace_4474123
  have hstable : (prefixWord ++ tailWord_4474123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474123).length < 2 ^ (prefixWord ++ tailWord_4474123).sum := by decide
  have hdescent : baseEnd_4474123 < baseStart_4474123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474139 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3]
def baseStart_4474139 : Nat := 118140960795 + 4474139 * 2 ^ 59
def prefixEnd_4474139 : Nat := 4983230072969 + 3 ^ 40 * 4474139 * 2
def baseEnd_4474139 : Nat := 2297383822026575644286315

theorem tailTrace_4474139 : CollatzResearch.WordTrace tailWord_4474139 prefixEnd_4474139 2297383822026575644286315 := by
  unfold tailWord_4474139
  simp only [CollatzResearch.WordTrace]
  refine ⟨163185255537965999951441471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108790170358643999967627647 163185255537965999951441471)
  ·
    refine ⟨244777883306948999927162207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163185255537965999951441471 244777883306948999927162207)
    ·
      refine ⟨367166824960423499890743311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244777883306948999927162207 367166824960423499890743311)
      ·
        refine ⟨550750237440635249836114967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367166824960423499890743311 550750237440635249836114967)
        ·
          refine ⟨826125356160952874754172451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550750237440635249836114967 826125356160952874754172451)
          ·
            refine ⟨1239188034241429312131258677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826125356160952874754172451 1239188034241429312131258677)
            ·
              refine ⟨116173878210133998012305501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1239188034241429312131258677 116173878210133998012305501)
              ·
                refine ⟨43565204328800249254614563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 116173878210133998012305501 43565204328800249254614563)
                ·
                  refine ⟨65347806493200373881921845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43565204328800249254614563 65347806493200373881921845)
                  ·
                    refine ⟨6126356858737535051430173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65347806493200373881921845 6126356858737535051430173)
                    ·
                      refine ⟨2297383822026575644286315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6126356858737535051430173 2297383822026575644286315)
                      ·
                        rfl

theorem cell23_4474139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 5, 3].length) (baseStart_4474139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474139 prefixEnd_4474139 := by exact prefixLift 4474139
  have htrace : WordTrace (prefixWord ++ tailWord_4474139) baseStart_4474139 baseEnd_4474139 := by
    simpa [prefixWord, tailWord_4474139, baseEnd_4474139] using wordTrace_append hprefix tailTrace_4474139
  have hstable : (prefixWord ++ tailWord_4474139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474139).length < 2 ^ (prefixWord ++ tailWord_4474139).sum := by decide
  have hdescent : baseEnd_4474139 < baseStart_4474139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474179 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4]
def baseStart_4474179 : Nat := 118140960795 + 4474179 * 2 ^ 59
def prefixEnd_4474179 : Nat := 4983230072969 + 3 ^ 40 * 4474179 * 2
def baseEnd_4474179 : Nat := 2297404361252755487786131

theorem tailTrace_4474179 : CollatzResearch.WordTrace tailWord_4474179 prefixEnd_4474179 2297404361252755487786131 := by
  unfold tailWord_4474179
  simp only [CollatzResearch.WordTrace]
  refine ⟨163186714457821086782897591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108791142971880724521931727 163186714457821086782897591)
  ·
    refine ⟨244780071686731630174346387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163186714457821086782897591 244780071686731630174346387)
    ·
      refine ⟨367170107530097445261519581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244780071686731630174346387 367170107530097445261519581)
      ·
        refine ⟨137688790323786541973069843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367170107530097445261519581 137688790323786541973069843)
        ·
          refine ⟨206533185485679812959604765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137688790323786541973069843 206533185485679812959604765)
          ·
            refine ⟨77449944557129929859851787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 206533185485679812959604765 77449944557129929859851787)
            ·
              refine ⟨116174916835694894789777681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77449944557129929859851787 116174916835694894789777681)
              ·
                refine ⟨87131187626771171092333261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116174916835694894789777681 87131187626771171092333261)
                ·
                  refine ⟨32674195360039189159624973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87131187626771171092333261 32674195360039189159624973)
                  ·
                    refine ⟨12252823260014695934859365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32674195360039189159624973 12252823260014695934859365)
                    ·
                      refine ⟨2297404361252755487786131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12252823260014695934859365 2297404361252755487786131)
                      ·
                        rfl

theorem cell23_4474179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_4474179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474179 prefixEnd_4474179 := by exact prefixLift 4474179
  have htrace : WordTrace (prefixWord ++ tailWord_4474179) baseStart_4474179 baseEnd_4474179 := by
    simpa [prefixWord, tailWord_4474179, baseEnd_4474179] using wordTrace_append hprefix tailTrace_4474179
  have hstable : (prefixWord ++ tailWord_4474179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474179).length < 2 ^ (prefixWord ++ tailWord_4474179).sum := by decide
  have hdescent : baseEnd_4474179 < baseStart_4474179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474180 : List Nat := [2, 3, 4, 1, 1, 2, 1, 4, 5]
def baseStart_4474180 : Nat := 118140960795 + 4474180 * 2 ^ 59
def prefixEnd_4474180 : Nat := 4983230072969 + 3 ^ 40 * 4474180 * 2
def baseEnd_4474180 : Nat := 255267208303712220430403

theorem tailTrace_4474180 : CollatzResearch.WordTrace tailWord_4474180 prefixEnd_4474180 255267208303712220430403 := by
  unfold tailWord_4474180
  simp only [CollatzResearch.WordTrace]
  refine ⟨81593375465408731976841997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108791167287211642635789329 81593375465408731976841997)
  ·
    refine ⟨30597515799528274491315749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81593375465408731976841997 30597515799528274491315749)
    ·
      refine ⟨5737034212411551467121703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30597515799528274491315749 5737034212411551467121703)
      ·
        refine ⟨8605551318617327200682555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737034212411551467121703 8605551318617327200682555)
        ·
          refine ⟨12908326977925990801023833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8605551318617327200682555 12908326977925990801023833)
          ·
            refine ⟨9681245233444493100767875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12908326977925990801023833 9681245233444493100767875)
            ·
              refine ⟨14521867850166739651151813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9681245233444493100767875 14521867850166739651151813)
              ·
                refine ⟨2722850221906263684590965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14521867850166739651151813 2722850221906263684590965)
                ·
                  refine ⟨255267208303712220430403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2722850221906263684590965 255267208303712220430403)
                  ·
                    rfl

theorem cell23_4474180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 5].length) (baseStart_4474180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474180 prefixEnd_4474180 := by exact prefixLift 4474180
  have htrace : WordTrace (prefixWord ++ tailWord_4474180) baseStart_4474180 baseEnd_4474180 := by
    simpa [prefixWord, tailWord_4474180, baseEnd_4474180] using wordTrace_append hprefix tailTrace_4474180
  have hstable : (prefixWord ++ tailWord_4474180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474180).length < 2 ^ (prefixWord ++ tailWord_4474180).sum := by decide
  have hdescent : baseEnd_4474180 < baseStart_4474180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474196 : List Nat := [2, 4, 1, 1, 2, 1, 2, 2, 1, 3, 4]
def baseStart_4474196 : Nat := 118140960795 + 4474196 * 2 ^ 59
def prefixEnd_4474196 : Nat := 4983230072969 + 3 ^ 40 * 4474196 * 2
def baseEnd_4474196 : Nat := 2297413090423881921273553

theorem tailTrace_4474196 : CollatzResearch.WordTrace tailWord_4474196 prefixEnd_4474196 2297413090423881921273553 := by
  unfold tailWord_4474196
  simp only [CollatzResearch.WordTrace]
  refine ⟨81593667249379749343133221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108791556332506332457510961 81593667249379749343133221)
  ·
    refine ⟨15298812609258703001837479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81593667249379749343133221 15298812609258703001837479)
    ·
      refine ⟨22948218913888054502756219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15298812609258703001837479 22948218913888054502756219)
      ·
        refine ⟨34422328370832081754134329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22948218913888054502756219 34422328370832081754134329)
        ·
          refine ⟨25816746278124061315600747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34422328370832081754134329 25816746278124061315600747)
          ·
            refine ⟨38725119417186091973401121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25816746278124061315600747 38725119417186091973401121)
            ·
              refine ⟨29043839562889568980050841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38725119417186091973401121 29043839562889568980050841)
              ·
                refine ⟨21782879672167176735038131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29043839562889568980050841 21782879672167176735038131)
                ·
                  refine ⟨32674319508250765102557197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21782879672167176735038131 32674319508250765102557197)
                  ·
                    refine ⟨12252869815594036913458949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32674319508250765102557197 12252869815594036913458949)
                    ·
                      refine ⟨2297413090423881921273553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12252869815594036913458949 2297413090423881921273553)
                      ·
                        rfl

theorem cell23_4474196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_4474196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474196 prefixEnd_4474196 := by exact prefixLift 4474196
  have htrace : WordTrace (prefixWord ++ tailWord_4474196) baseStart_4474196 baseEnd_4474196 := by
    simpa [prefixWord, tailWord_4474196, baseEnd_4474196] using wordTrace_append hprefix tailTrace_4474196
  have hstable : (prefixWord ++ tailWord_4474196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474196).length < 2 ^ (prefixWord ++ tailWord_4474196).sum := by decide
  have hdescent : baseEnd_4474196 < baseStart_4474196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474209 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_4474209 : Nat := 118140960795 + 4474209 * 2 ^ 59
def prefixEnd_4474209 : Nat := 4983230072969 + 3 ^ 40 * 4474209 * 2
def baseEnd_4474209 : Nat := 2297419765672390370410993

theorem tailTrace_4474209 : CollatzResearch.WordTrace tailWord_4474209 prefixEnd_4474209 2297419765672390370410993 := by
  unfold tailWord_4474209
  simp only [CollatzResearch.WordTrace]
  refine ⟨163187808647712401906489681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108791872431808267937659787 163187808647712401906489681)
  ·
    refine ⟨122390856485784301429867261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163187808647712401906489681 122390856485784301429867261)
    ·
      refine ⟨45896571182169113036200223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122390856485784301429867261 45896571182169113036200223)
      ·
        refine ⟨68844856773253669554300335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45896571182169113036200223 68844856773253669554300335)
        ·
          refine ⟨103267285159880504331450503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68844856773253669554300335 103267285159880504331450503)
          ·
            refine ⟨154900927739820756497175755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103267285159880504331450503 154900927739820756497175755)
            ·
              refine ⟨232351391609731134745763633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154900927739820756497175755 232351391609731134745763633)
              ·
                refine ⟨174263543707298351059322725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232351391609731134745763633 174263543707298351059322725)
                ·
                  refine ⟨32674414445118440823623011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174263543707298351059322725 32674414445118440823623011)
                  ·
                    refine ⟨49011621667677661235434517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32674414445118440823623011 49011621667677661235434517)
                    ·
                      refine ⟨2297419765672390370410993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49011621667677661235434517 2297419765672390370410993)
                      ·
                        rfl

theorem cell23_4474209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_4474209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474209 prefixEnd_4474209 := by exact prefixLift 4474209
  have htrace : WordTrace (prefixWord ++ tailWord_4474209) baseStart_4474209 baseEnd_4474209 := by
    simpa [prefixWord, tailWord_4474209, baseEnd_4474209] using wordTrace_append hprefix tailTrace_4474209
  have hstable : (prefixWord ++ tailWord_4474209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474209).length < 2 ^ (prefixWord ++ tailWord_4474209).sum := by decide
  have hdescent : baseEnd_4474209 < baseStart_4474209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474297 : List Nat := [1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4474297 : Nat := 118140960795 + 4474297 * 2 ^ 59
def prefixEnd_4474297 : Nat := 4983230072969 + 3 ^ 40 * 4474297 * 2
def baseEnd_4474297 : Nat := 2297464951969986026110589

theorem tailTrace_4474297 : CollatzResearch.WordTrace tailWord_4474297 prefixEnd_4474297 2297464951969986026110589 := by
  unfold tailWord_4474297
  simp only [CollatzResearch.WordTrace]
  refine ⟨163191018271393592935693145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108794012180929061957128763 163191018271393592935693145)
  ·
    refine ⟨122393263703545194701769859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163191018271393592935693145 122393263703545194701769859)
    ·
      refine ⟨183589895555317792052654789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122393263703545194701769859 183589895555317792052654789)
      ·
        refine ⟨34423105416622086009872773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183589895555317792052654789 34423105416622086009872773)
        ·
          refine ⟨6454332265616641126851145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34423105416622086009872773 6454332265616641126851145)
          ·
            refine ⟨4840749199212480845138359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6454332265616641126851145 4840749199212480845138359)
            ·
              refine ⟨7261123798818721267707539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840749199212480845138359 7261123798818721267707539)
              ·
                refine ⟨10891685698228081901561309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7261123798818721267707539 10891685698228081901561309)
                ·
                  refine ⟨4084382136835530713085491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10891685698228081901561309 4084382136835530713085491)
                  ·
                    refine ⟨6126573205253296069628237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4084382136835530713085491 6126573205253296069628237)
                    ·
                      refine ⟨2297464951969986026110589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6126573205253296069628237 2297464951969986026110589)
                      ·
                        rfl

theorem cell23_4474297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4474297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474297 prefixEnd_4474297 := by exact prefixLift 4474297
  have htrace : WordTrace (prefixWord ++ tailWord_4474297) baseStart_4474297 baseEnd_4474297 := by
    simpa [prefixWord, tailWord_4474297, baseEnd_4474297] using wordTrace_append hprefix tailTrace_4474297
  have hstable : (prefixWord ++ tailWord_4474297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474297).length < 2 ^ (prefixWord ++ tailWord_4474297).sum := by decide
  have hdescent : baseEnd_4474297 < baseStart_4474297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474333 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_4474333 : Nat := 118140960795 + 4474333 * 2 ^ 59
def prefixEnd_4474333 : Nat := 4983230072969 + 3 ^ 40 * 4474333 * 2
def baseEnd_4474333 : Nat := 2297483437273547885260423

theorem tailTrace_4474333 : CollatzResearch.WordTrace tailWord_4474333 prefixEnd_4474333 2297483437273547885260423 := by
  unfold tailWord_4474333
  simp only [CollatzResearch.WordTrace]
  refine ⟨163192331299263171084003653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108794887532842114056002435 163192331299263171084003653)
  ·
    refine ⟨30598562118611844578250685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163192331299263171084003653 30598562118611844578250685)
    ·
      refine ⟨11474460794479441716844007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30598562118611844578250685 11474460794479441716844007)
      ·
        refine ⟨17211691191719162575266011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11474460794479441716844007 17211691191719162575266011)
        ·
          refine ⟨25817536787578743862899017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17211691191719162575266011 25817536787578743862899017)
          ·
            refine ⟨19363152590684057897174263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25817536787578743862899017 19363152590684057897174263)
            ·
              refine ⟨29044728886026086845761395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19363152590684057897174263 29044728886026086845761395)
              ·
                refine ⟨43567093329039130268642093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29044728886026086845761395 43567093329039130268642093)
                ·
                  refine ⟨16337659998389673850740785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43567093329039130268642093 16337659998389673850740785)
                  ·
                    refine ⟨12253244998792255388055589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16337659998389673850740785 12253244998792255388055589)
                    ·
                      refine ⟨2297483437273547885260423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12253244998792255388055589 2297483437273547885260423)
                      ·
                        rfl

theorem cell23_4474333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_4474333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474333 prefixEnd_4474333 := by exact prefixLift 4474333
  have htrace : WordTrace (prefixWord ++ tailWord_4474333) baseStart_4474333 baseEnd_4474333 := by
    simpa [prefixWord, tailWord_4474333, baseEnd_4474333] using wordTrace_append hprefix tailTrace_4474333
  have hstable : (prefixWord ++ tailWord_4474333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474333).length < 2 ^ (prefixWord ++ tailWord_4474333).sum := by decide
  have hdescent : baseEnd_4474333 < baseStart_4474333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474388 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4474388 : Nat := 118140960795 + 4474388 * 2 ^ 59
def prefixEnd_4474388 : Nat := 4983230072969 + 3 ^ 40 * 4474388 * 2
def baseEnd_4474388 : Nat := 2297511678709545170072671

theorem tailTrace_4474388 : CollatzResearch.WordTrace tailWord_4474388 prefixEnd_4474388 2297511678709545170072671 := by
  unfold tailWord_4474388
  simp only [CollatzResearch.WordTrace]
  refine ⟨81597168657031957738627909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108796224876042610318170545 81597168657031957738627909)
  ·
    refine ⟨15299469123193492075992733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81597168657031957738627909 15299469123193492075992733)
    ·
      refine ⟨5737300921197559528497275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15299469123193492075992733 5737300921197559528497275)
      ·
        refine ⟨8605951381796339292745913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737300921197559528497275 8605951381796339292745913)
        ·
          refine ⟨6454463536347254469559435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8605951381796339292745913 6454463536347254469559435)
          ·
            refine ⟨9681695304520881704339153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6454463536347254469559435 9681695304520881704339153)
            ·
              refine ⟨7261271478390661278254365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9681695304520881704339153 7261271478390661278254365)
              ·
                refine ⟨2722976804396497979345387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7261271478390661278254365 2722976804396497979345387)
                ·
                  refine ⟨4084465206594746969018081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2722976804396497979345387 4084465206594746969018081)
                  ·
                    refine ⟨3063348904946060226763561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084465206594746969018081 3063348904946060226763561)
                    ·
                      refine ⟨2297511678709545170072671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063348904946060226763561 2297511678709545170072671)
                      ·
                        rfl

theorem cell23_4474388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4474388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474388 prefixEnd_4474388 := by exact prefixLift 4474388
  have htrace : WordTrace (prefixWord ++ tailWord_4474388) baseStart_4474388 baseEnd_4474388 := by
    simpa [prefixWord, tailWord_4474388, baseEnd_4474388] using wordTrace_append hprefix tailTrace_4474388
  have hstable : (prefixWord ++ tailWord_4474388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474388).length < 2 ^ (prefixWord ++ tailWord_4474388).sum := by decide
  have hdescent : baseEnd_4474388 < baseStart_4474388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474397 : List Nat := [1, 4, 2, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_4474397 : Nat := 118140960795 + 4474397 * 2 ^ 59
def prefixEnd_4474397 : Nat := 4983230072969 + 3 ^ 40 * 4474397 * 2
def baseEnd_4474397 : Nat := 2297516300035435634860129

theorem tailTrace_4474397 : CollatzResearch.WordTrace tailWord_4474397 prefixEnd_4474397 2297516300035435634860129 := by
  unfold tailWord_4474397
  simp only [CollatzResearch.WordTrace]
  refine ⟨163194665571031310014333445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108796443714020873342888963 163194665571031310014333445)
  ·
    refine ⟨30598999794568370627687521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163194665571031310014333445 30598999794568370627687521)
    ·
      refine ⟨22949249845926277970765641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30598999794568370627687521 22949249845926277970765641)
      ·
        refine ⟨17211937384444708478074231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22949249845926277970765641 17211937384444708478074231)
        ·
          refine ⟨25817906076667062717111347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17211937384444708478074231 25817906076667062717111347)
          ·
            refine ⟨38726859115000594075667021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25817906076667062717111347 38726859115000594075667021)
            ·
              refine ⟨14522572168125222778375133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38726859115000594075667021 14522572168125222778375133)
              ·
                refine ⟨5445964563046958541890675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14522572168125222778375133 5445964563046958541890675)
                ·
                  refine ⟨8168946844570437812836013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5445964563046958541890675 8168946844570437812836013)
                  ·
                    refine ⟨3063355066713914179813505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8168946844570437812836013 3063355066713914179813505)
                    ·
                      refine ⟨2297516300035435634860129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063355066713914179813505 2297516300035435634860129)
                      ·
                        rfl

theorem cell23_4474397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_4474397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474397 prefixEnd_4474397 := by exact prefixLift 4474397
  have htrace : WordTrace (prefixWord ++ tailWord_4474397) baseStart_4474397 baseEnd_4474397 := by
    simpa [prefixWord, tailWord_4474397, baseEnd_4474397] using wordTrace_append hprefix tailTrace_4474397
  have hstable : (prefixWord ++ tailWord_4474397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474397).length < 2 ^ (prefixWord ++ tailWord_4474397).sum := by decide
  have hdescent : baseEnd_4474397 < baseStart_4474397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474398 : List Nat := [4, 3, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4474398 : Nat := 118140960795 + 4474398 * 2 ^ 59
def prefixEnd_4474398 : Nat := 4983230072969 + 3 ^ 40 * 4474398 * 2
def baseEnd_4474398 : Nat := 765838937838696710315875

theorem tailTrace_4474398 : CollatzResearch.WordTrace tailWord_4474398 prefixEnd_4474398 765838937838696710315875 := by
  unfold tailWord_4474398
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399337755503460898139981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108796468029351791456746565 20399337755503460898139981)
  ·
    refine ⟨7649751658313797836802493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20399337755503460898139981 7649751658313797836802493)
    ·
      refine ⟨2868656871867674188800935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7649751658313797836802493 2868656871867674188800935)
      ·
        refine ⟨4302985307801511283201403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2868656871867674188800935 4302985307801511283201403)
        ·
          refine ⟨6454477961702266924802105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4302985307801511283201403 6454477961702266924802105)
          ·
            refine ⟨4840858471276700193601579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6454477961702266924802105 4840858471276700193601579)
            ·
              refine ⟨7261287706915050290402369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4840858471276700193601579 7261287706915050290402369)
              ·
                refine ⟨5445965780186287717801777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7261287706915050290402369 5445965780186287717801777)
                ·
                  refine ⟨4084474335139715788351333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5445965780186287717801777 4084474335139715788351333)
                  ·
                    refine ⟨765838937838696710315875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084474335139715788351333 765838937838696710315875)
                    ·
                      rfl

theorem cell23_4474398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4474398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474398 prefixEnd_4474398 := by exact prefixLift 4474398
  have htrace : WordTrace (prefixWord ++ tailWord_4474398) baseStart_4474398 baseEnd_4474398 := by
    simpa [prefixWord, tailWord_4474398, baseEnd_4474398] using wordTrace_append hprefix tailTrace_4474398
  have hstable : (prefixWord ++ tailWord_4474398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474398).length < 2 ^ (prefixWord ++ tailWord_4474398).sum := by decide
  have hdescent : baseEnd_4474398 < baseStart_4474398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474423 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4]
def baseStart_4474423 : Nat := 118140960795 + 4474423 * 2 ^ 59
def prefixEnd_4474423 : Nat := 4983230072969 + 3 ^ 40 * 4474423 * 2
def baseEnd_4474423 : Nat := 2297529650532452533135009

theorem tailTrace_4474423 : CollatzResearch.WordTrace tailWord_4474423 prefixEnd_4474423 2297529650532452533135009 := by
  unfold tailWord_4474423
  simp only [CollatzResearch.WordTrace]
  refine ⟨163195613868937116454779923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108797075912624744303186615 163195613868937116454779923)
  ·
    refine ⟨244793420803405674682169885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163195613868937116454779923 244793420803405674682169885)
    ·
      refine ⟨91797532801277128005813707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244793420803405674682169885 91797532801277128005813707)
      ·
        refine ⟨137696299201915692008720561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91797532801277128005813707 137696299201915692008720561)
        ·
          refine ⟨103272224401436769006540421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137696299201915692008720561 103272224401436769006540421)
          ·
            refine ⟨19363542075269394188726329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103272224401436769006540421 19363542075269394188726329)
            ·
              refine ⟨14522656556452045641544747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19363542075269394188726329 14522656556452045641544747)
              ·
                refine ⟨21783984834678068462317121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14522656556452045641544747 21783984834678068462317121)
                ·
                  refine ⟨16337988626008551346737841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21783984834678068462317121 16337988626008551346737841)
                  ·
                    refine ⟨12253491469506413510053381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16337988626008551346737841 12253491469506413510053381)
                    ·
                      refine ⟨2297529650532452533135009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12253491469506413510053381 2297529650532452533135009)
                      ·
                        rfl

theorem cell23_4474423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 2, 4].length) (baseStart_4474423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474423 prefixEnd_4474423 := by exact prefixLift 4474423
  have htrace : WordTrace (prefixWord ++ tailWord_4474423) baseStart_4474423 baseEnd_4474423 := by
    simpa [prefixWord, tailWord_4474423, baseEnd_4474423] using wordTrace_append hprefix tailTrace_4474423
  have hstable : (prefixWord ++ tailWord_4474423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474423).length < 2 ^ (prefixWord ++ tailWord_4474423).sum := by decide
  have hdescent : baseEnd_4474423 < baseStart_4474423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474433 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 7]
def baseStart_4474433 : Nat := 118140960795 + 4474433 * 2 ^ 59
def prefixEnd_4474433 : Nat := 4983230072969 + 3 ^ 40 * 4474433 * 2
def baseEnd_4474433 : Nat := 255281642815444166001107

theorem tailTrace_4474433 : CollatzResearch.WordTrace tailWord_4474433 prefixEnd_4474433 255281642815444166001107 := by
  unfold tailWord_4474433
  simp only [CollatzResearch.WordTrace]
  refine ⟨163195978598900888162643953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108797319065933925441762635 163195978598900888162643953)
  ·
    refine ⟨122396983949175666121982965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163195978598900888162643953 122396983949175666121982965)
    ·
      refine ⟨11474717245235218698935903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 122396983949175666121982965 11474717245235218698935903)
      ·
        refine ⟨17212075867852828048403855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11474717245235218698935903 17212075867852828048403855)
        ·
          refine ⟨25818113801779242072605783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17212075867852828048403855 25818113801779242072605783)
          ·
            refine ⟨38727170702668863108908675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25818113801779242072605783 38727170702668863108908675)
            ·
              refine ⟨58090756054003294663363013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38727170702668863108908675 58090756054003294663363013)
              ·
                refine ⟨10892016760125617749380565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58090756054003294663363013 10892016760125617749380565)
                ·
                  refine ⟨255281642815444166001107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10892016760125617749380565 255281642815444166001107)
                  ·
                    rfl

theorem cell23_4474433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 7].length) (baseStart_4474433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474433 prefixEnd_4474433 := by exact prefixLift 4474433
  have htrace : WordTrace (prefixWord ++ tailWord_4474433) baseStart_4474433 baseEnd_4474433 := by
    simpa [prefixWord, tailWord_4474433, baseEnd_4474433] using wordTrace_append hprefix tailTrace_4474433
  have hstable : (prefixWord ++ tailWord_4474433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474433).length < 2 ^ (prefixWord ++ tailWord_4474433).sum := by decide
  have hdescent : baseEnd_4474433 < baseStart_4474433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474467 : List Nat := [1, 1, 1, 5, 1, 4, 3, 2, 5]
def baseStart_4474467 : Nat := 118140960795 + 4474467 * 2 ^ 59
def prefixEnd_4474467 : Nat := 4983230072969 + 3 ^ 40 * 4474467 * 2
def baseEnd_4474467 : Nat := 255283582631250040109423

theorem tailTrace_4474467 : CollatzResearch.WordTrace tailWord_4474467 prefixEnd_4474467 255283582631250040109423 := by
  unfold tailWord_4474467
  simp only [CollatzResearch.WordTrace]
  refine ⟨163197218680777711969381655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108798145787185141312921103 163197218680777711969381655)
  ·
    refine ⟨244795828021166567954072483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163197218680777711969381655 244795828021166567954072483)
    ·
      refine ⟨367193742031749851931108725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244795828021166567954072483 367193742031749851931108725)
      ·
        refine ⟨34424413315476548618541443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 367193742031749851931108725 34424413315476548618541443)
        ·
          refine ⟨51636619973214822927812165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34424413315476548618541443 51636619973214822927812165)
          ·
            refine ⟨9681866244977779298964781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51636619973214822927812165 9681866244977779298964781)
            ·
              refine ⟨3630699841866667237111793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9681866244977779298964781 3630699841866667237111793)
              ·
                refine ⟨2723024881400000427833845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3630699841866667237111793 2723024881400000427833845)
                ·
                  refine ⟨255283582631250040109423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2723024881400000427833845 255283582631250040109423)
                  ·
                    rfl

theorem cell23_4474467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 2, 5].length) (baseStart_4474467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474467 prefixEnd_4474467 := by exact prefixLift 4474467
  have htrace : WordTrace (prefixWord ++ tailWord_4474467) baseStart_4474467 baseEnd_4474467 := by
    simpa [prefixWord, tailWord_4474467, baseEnd_4474467] using wordTrace_append hprefix tailTrace_4474467
  have hstable : (prefixWord ++ tailWord_4474467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474467).length < 2 ^ (prefixWord ++ tailWord_4474467).sum := by decide
  have hdescent : baseEnd_4474467 < baseStart_4474467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474478 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_4474478 : Nat := 118140960795 + 4474478 * 2 ^ 59
def prefixEnd_4474478 : Nat := 4983230072969 + 3 ^ 40 * 4474478 * 2
def baseEnd_4474478 : Nat := 2297557891968449817947257

theorem tailTrace_4474478 : CollatzResearch.WordTrace tailWord_4474478 prefixEnd_4474478 2297557891968449817947257 := by
  unfold tailWord_4474478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20399702485467232606004011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108798413255825240565354725 20399702485467232606004011)
  ·
    refine ⟨30599553728200848909006017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20399702485467232606004011 30599553728200848909006017)
    ·
      refine ⟨22949665296150636681754513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30599553728200848909006017 22949665296150636681754513)
      ·
        refine ⟨17212248972112977511315885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22949665296150636681754513 17212248972112977511315885)
        ·
          refine ⟨6454593364542366566743457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17212248972112977511315885 6454593364542366566743457)
          ·
            refine ⟨4840945023406774925057593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6454593364542366566743457 4840945023406774925057593)
            ·
              refine ⟨3630708767555081193793195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4840945023406774925057593 3630708767555081193793195)
              ·
                refine ⟨5446063151332621790689793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630708767555081193793195 5446063151332621790689793)
                ·
                  refine ⟨4084547363499466343017345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5446063151332621790689793 4084547363499466343017345)
                  ·
                    refine ⟨3063410522624599757263009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084547363499466343017345 3063410522624599757263009)
                    ·
                      refine ⟨2297557891968449817947257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063410522624599757263009 2297557891968449817947257)
                      ·
                        rfl

theorem cell23_4474478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_4474478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474478 prefixEnd_4474478 := by exact prefixLift 4474478
  have htrace : WordTrace (prefixWord ++ tailWord_4474478) baseStart_4474478 baseEnd_4474478 := by
    simpa [prefixWord, tailWord_4474478, baseEnd_4474478] using wordTrace_append hprefix tailTrace_4474478
  have hstable : (prefixWord ++ tailWord_4474478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474478).length < 2 ^ (prefixWord ++ tailWord_4474478).sum := by decide
  have hdescent : baseEnd_4474478 < baseStart_4474478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474584 : List Nat := [2, 1, 2, 2, 3, 1, 1, 6, 1, 1, 3]
def baseStart_4474584 : Nat := 118140960795 + 4474584 * 2 ^ 59
def prefixEnd_4474584 : Nat := 4983230072969 + 3 ^ 40 * 4474584 * 2
def baseEnd_4474584 : Nat := 2297612320917826403221769

theorem tailTrace_4474584 : CollatzResearch.WordTrace tailWord_4474584 prefixEnd_4474584 2297612320917826403221769 := by
  unfold tailWord_4474584
  simp only [CollatzResearch.WordTrace]
  refine ⟨81600743010676920475695403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108800990680902560634260537 81600743010676920475695403)
  ·
    refine ⟨122401114516015380713543105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81600743010676920475695403 122401114516015380713543105)
    ·
      refine ⟨91800835887011535535157329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122401114516015380713543105 91800835887011535535157329)
      ·
        refine ⟨68850626915258651651367997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91800835887011535535157329 68850626915258651651367997)
        ·
          refine ⟨25818985093221994369262999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68850626915258651651367997 25818985093221994369262999)
          ·
            refine ⟨38728477639832991553894499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25818985093221994369262999 38728477639832991553894499)
            ·
              refine ⟨58092716459749487330841749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38728477639832991553894499 58092716459749487330841749)
              ·
                refine ⟨2723096084050757218633207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58092716459749487330841749 2723096084050757218633207)
                ·
                  refine ⟨4084644126076135827949811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723096084050757218633207 4084644126076135827949811)
                  ·
                    refine ⟨6126966189114203741924717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4084644126076135827949811 6126966189114203741924717)
                    ·
                      refine ⟨2297612320917826403221769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6126966189114203741924717 2297612320917826403221769)
                      ·
                        rfl

theorem cell23_4474584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_4474584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474584 prefixEnd_4474584 := by exact prefixLift 4474584
  have htrace : WordTrace (prefixWord ++ tailWord_4474584) baseStart_4474584 baseEnd_4474584 := by
    simpa [prefixWord, tailWord_4474584, baseEnd_4474584] using wordTrace_append hprefix tailTrace_4474584
  have hstable : (prefixWord ++ tailWord_4474584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474584).length < 2 ^ (prefixWord ++ tailWord_4474584).sum := by decide
  have hdescent : baseEnd_4474584 < baseStart_4474584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474607 : List Nat := [1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 4]
def baseStart_4474607 : Nat := 118140960795 + 4474607 * 2 ^ 59
def prefixEnd_4474607 : Nat := 4983230072969 + 3 ^ 40 * 4474607 * 2
def baseEnd_4474607 : Nat := 2297624130972879813234163

theorem tailTrace_4474607 : CollatzResearch.WordTrace tailWord_4474607 prefixEnd_4474607 2297624130972879813234163 := by
  unfold tailWord_4474607
  simp only [CollatzResearch.WordTrace]
  refine ⟨163202324900270515879478075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108801549933513677252985383 163202324900270515879478075)
  ·
    refine ⟨244803487350405773819217113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163202324900270515879478075 244803487350405773819217113)
    ·
      refine ⟨183602615512804330364412835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244803487350405773819217113 183602615512804330364412835)
      ·
        refine ⟨275403923269206495546619253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183602615512804330364412835 275403923269206495546619253)
        ·
          refine ⟨25819117806488108957495555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 275403923269206495546619253 25819117806488108957495555)
          ·
            refine ⟨38728676709732163436243333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25819117806488108957495555 38728676709732163436243333)
            ·
              refine ⟨7261626883074780644295625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38728676709732163436243333 7261626883074780644295625)
              ·
                refine ⟨5446220162306085483221719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7261626883074780644295625 5446220162306085483221719)
                ·
                  refine ⟨8169330243459128224832579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446220162306085483221719 8169330243459128224832579)
                  ·
                    refine ⟨12253995365188692337248869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8169330243459128224832579 12253995365188692337248869)
                    ·
                      refine ⟨2297624130972879813234163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12253995365188692337248869 2297624130972879813234163)
                      ·
                        rfl

theorem cell23_4474607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 1, 4].length) (baseStart_4474607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474607 prefixEnd_4474607 := by exact prefixLift 4474607
  have htrace : WordTrace (prefixWord ++ tailWord_4474607) baseStart_4474607 baseEnd_4474607 := by
    simpa [prefixWord, tailWord_4474607, baseEnd_4474607] using wordTrace_append hprefix tailTrace_4474607
  have hstable : (prefixWord ++ tailWord_4474607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474607).length < 2 ^ (prefixWord ++ tailWord_4474607).sum := by decide
  have hdescent : baseEnd_4474607 < baseStart_4474607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474610 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4474610 : Nat := 118140960795 + 4474610 * 2 ^ 59
def prefixEnd_4474610 : Nat := 4983230072969 + 3 ^ 40 * 4474610 * 2
def baseEnd_4474610 : Nat := 2297625671414843301496649

theorem tailTrace_4474610 : CollatzResearch.WordTrace tailWord_4474610 prefixEnd_4474610 2297625671414843301496649 := by
  unfold tailWord_4474610
  simp only [CollatzResearch.WordTrace]
  refine ⟨40800608579814911847959321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108801622879506431594558189 40800608579814911847959321)
  ·
    refine ⟨30600456434861183885969491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40800608579814911847959321 30600456434861183885969491)
    ·
      refine ⟨45900684652291775828954237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30600456434861183885969491 45900684652291775828954237)
      ·
        refine ⟨17212756744609415935857839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45900684652291775828954237 17212756744609415935857839)
        ·
          refine ⟨25819135116914123903786759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17212756744609415935857839 25819135116914123903786759)
          ·
            refine ⟨38728702675371185855680139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25819135116914123903786759 38728702675371185855680139)
            ·
              refine ⟨58093054013056778783520209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38728702675371185855680139 58093054013056778783520209)
              ·
                refine ⟨43569790509792584087640157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58093054013056778783520209 43569790509792584087640157)
                ·
                  refine ⟨16338671441172219032865059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43569790509792584087640157 16338671441172219032865059)
                  ·
                    refine ⟨24508007161758328549297589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16338671441172219032865059 24508007161758328549297589)
                    ·
                      refine ⟨2297625671414843301496649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24508007161758328549297589 2297625671414843301496649)
                      ·
                        rfl

theorem cell23_4474610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4474610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474610 prefixEnd_4474610 := by exact prefixLift 4474610
  have htrace : WordTrace (prefixWord ++ tailWord_4474610) baseStart_4474610 baseEnd_4474610 := by
    simpa [prefixWord, tailWord_4474610, baseEnd_4474610] using wordTrace_append hprefix tailTrace_4474610
  have hstable : (prefixWord ++ tailWord_4474610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474610).length < 2 ^ (prefixWord ++ tailWord_4474610).sum := by decide
  have hdescent : baseEnd_4474610 < baseStart_4474610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474620 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_4474620 : Nat := 118140960795 + 4474620 * 2 ^ 59
def prefixEnd_4474620 : Nat := 4983230072969 + 3 ^ 40 * 4474620 * 2
def baseEnd_4474620 : Nat := 2297630806221388262371603

theorem tailTrace_4474620 : CollatzResearch.WordTrace tailWord_4474620 prefixEnd_4474620 2297630806221388262371603 := by
  unfold tailWord_4474620
  simp only [CollatzResearch.WordTrace]
  refine ⟨81601399524611709549850657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108801866032815612733134209 81601399524611709549850657)
  ·
    refine ⟨61201049643458782162387993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81601399524611709549850657 61201049643458782162387993)
    ·
      refine ⟨45900787232594086621790995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61201049643458782162387993 45900787232594086621790995)
      ·
        refine ⟨68851180848891129932686493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45900787232594086621790995 68851180848891129932686493)
        ·
          refine ⟨25819192818334173724757435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68851180848891129932686493 25819192818334173724757435)
          ·
            refine ⟨38728789227501260587136153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25819192818334173724757435 38728789227501260587136153)
            ·
              refine ⟨29046591920625945440352115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38728789227501260587136153 29046591920625945440352115)
              ·
                refine ⟨43569887880938918160528173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29046591920625945440352115 43569887880938918160528173)
                ·
                  refine ⟨16338707955352094310198065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43569887880938918160528173 16338707955352094310198065)
                  ·
                    refine ⟨12254030966514070732648549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16338707955352094310198065 12254030966514070732648549)
                    ·
                      refine ⟨2297630806221388262371603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12254030966514070732648549 2297630806221388262371603)
                      ·
                        rfl

theorem cell23_4474620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_4474620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474620 prefixEnd_4474620 := by exact prefixLift 4474620
  have htrace : WordTrace (prefixWord ++ tailWord_4474620) baseStart_4474620 baseEnd_4474620 := by
    simpa [prefixWord, tailWord_4474620, baseEnd_4474620] using wordTrace_append hprefix tailTrace_4474620
  have hstable : (prefixWord ++ tailWord_4474620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474620).length < 2 ^ (prefixWord ++ tailWord_4474620).sum := by decide
  have hdescent : baseEnd_4474620 < baseStart_4474620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474627 : List Nat := [1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 3]
def baseStart_4474627 : Nat := 118140960795 + 4474627 * 2 ^ 59
def prefixEnd_4474627 : Nat := 4983230072969 + 3 ^ 40 * 4474627 * 2
def baseEnd_4474627 : Nat := 2297634400585969734984071

theorem tailTrace_4474627 : CollatzResearch.WordTrace tailWord_4474627 prefixEnd_4474627 2297634400585969734984071 := by
  unfold tailWord_4474627
  simp only [CollatzResearch.WordTrace]
  refine ⟨163203054360198059295206135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108802036240132039530137423 163203054360198059295206135)
  ·
    refine ⟨244804581540297088942809203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163203054360198059295206135 244804581540297088942809203)
    ·
      refine ⟨367206872310445633414213805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244804581540297088942809203 367206872310445633414213805)
      ·
        refine ⟨137702577116417112530330177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367206872310445633414213805 137702577116417112530330177)
        ·
          refine ⟨103276932837312834397747633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137702577116417112530330177 103276932837312834397747633)
          ·
            refine ⟨77457699627984625798310725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103276932837312834397747633 77457699627984625798310725)
            ·
              refine ⟨14523318680247117337183261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77457699627984625798310725 14523318680247117337183261)
              ·
                refine ⟨5446244505092669001443723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14523318680247117337183261 5446244505092669001443723)
                ·
                  refine ⟨8169366757639003502165585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446244505092669001443723 8169366757639003502165585)
                  ·
                    refine ⟨6127025068229252626624189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8169366757639003502165585 6127025068229252626624189)
                    ·
                      refine ⟨2297634400585969734984071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6127025068229252626624189 2297634400585969734984071)
                      ·
                        rfl

theorem cell23_4474627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 2, 3].length) (baseStart_4474627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474627 prefixEnd_4474627 := by exact prefixLift 4474627
  have htrace : WordTrace (prefixWord ++ tailWord_4474627) baseStart_4474627 baseEnd_4474627 := by
    simpa [prefixWord, tailWord_4474627, baseEnd_4474627] using wordTrace_append hprefix tailTrace_4474627
  have hstable : (prefixWord ++ tailWord_4474627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474627).length < 2 ^ (prefixWord ++ tailWord_4474627).sum := by decide
  have hdescent : baseEnd_4474627 < baseStart_4474627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474678 : List Nat := [5, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4474678 : Nat := 118140960795 + 4474678 * 2 ^ 59
def prefixEnd_4474678 : Nat := 4983230072969 + 3 ^ 40 * 4474678 * 2
def baseEnd_4474678 : Nat := 2297660588099349035446337

theorem tailTrace_4474678 : CollatzResearch.WordTrace tailWord_4474678 prefixEnd_4474678 2297660588099349035446337 := by
  unfold tailWord_4474678
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200307155188330937832043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108803276322008863336875125 10200307155188330937832043)
  ·
    refine ⟨15300460732782496406748065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200307155188330937832043 15300460732782496406748065)
    ·
      refine ⟨11475345549586872305061049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15300460732782496406748065 11475345549586872305061049)
      ·
        refine ⟨8606509162190154228795787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11475345549586872305061049 8606509162190154228795787)
        ·
          refine ⟨12909763743285231343193681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8606509162190154228795787 12909763743285231343193681)
          ·
            refine ⟨9682322807463923507395261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12909763743285231343193681 9682322807463923507395261)
            ·
              refine ⟨3630871052798971315273223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9682322807463923507395261 3630871052798971315273223)
              ·
                refine ⟨5446306579198456972909835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3630871052798971315273223 5446306579198456972909835)
                ·
                  refine ⟨8169459868797685459364753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446306579198456972909835 8169459868797685459364753)
                  ·
                    refine ⟨6127094901598264094523565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8169459868797685459364753 6127094901598264094523565)
                    ·
                      refine ⟨2297660588099349035446337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6127094901598264094523565 2297660588099349035446337)
                      ·
                        rfl

theorem cell23_4474678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4474678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474678 prefixEnd_4474678 := by exact prefixLift 4474678
  have htrace : WordTrace (prefixWord ++ tailWord_4474678) baseStart_4474678 baseEnd_4474678 := by
    simpa [prefixWord, tailWord_4474678, baseEnd_4474678] using wordTrace_append hprefix tailTrace_4474678
  have hstable : (prefixWord ++ tailWord_4474678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474678).length < 2 ^ (prefixWord ++ tailWord_4474678).sum := by decide
  have hdescent : baseEnd_4474678 < baseStart_4474678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474684 : List Nat := [2, 2, 2, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_4474684 : Nat := 118140960795 + 4474684 * 2 ^ 59
def prefixEnd_4474684 : Nat := 4983230072969 + 3 ^ 40 * 4474684 * 2
def baseEnd_4474684 : Nat := 2297663668983276011971309

theorem tailTrace_4474684 : CollatzResearch.WordTrace tailWord_4474684 prefixEnd_4474684 2297663668983276011971309 := by
  unfold tailWord_4474684
  simp only [CollatzResearch.WordTrace]
  refine ⟨81602566660495779015015553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108803422213994372020020737 81602566660495779015015553)
  ·
    refine ⟨61201924995371834261261665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81602566660495779015015553 61201924995371834261261665)
    ·
      refine ⟨45901443746528875695946249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61201924995371834261261665 45901443746528875695946249)
      ·
        refine ⟨34426082809896656771959687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45901443746528875695946249 34426082809896656771959687)
        ·
          refine ⟨51639124214844985157939531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34426082809896656771959687 51639124214844985157939531)
          ·
            refine ⟨77458686322267477736909297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51639124214844985157939531 77458686322267477736909297)
            ·
              refine ⟨58094014741700608302681973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 77458686322267477736909297 58094014741700608302681973)
              ·
                refine ⟨5446313882034432028376435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58094014741700608302681973 5446313882034432028376435)
                ·
                  refine ⟨8169470823051648042564653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446313882034432028376435 8169470823051648042564653)
                  ·
                    refine ⟨3063551558644368015961745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8169470823051648042564653 3063551558644368015961745)
                    ·
                      refine ⟨2297663668983276011971309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063551558644368015961745 2297663668983276011971309)
                      ·
                        rfl

theorem cell23_4474684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_4474684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474684 prefixEnd_4474684 := by exact prefixLift 4474684
  have htrace : WordTrace (prefixWord ++ tailWord_4474684) baseStart_4474684 baseEnd_4474684 := by
    simpa [prefixWord, tailWord_4474684, baseEnd_4474684] using wordTrace_append hprefix tailTrace_4474684
  have hstable : (prefixWord ++ tailWord_4474684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474684).length < 2 ^ (prefixWord ++ tailWord_4474684).sum := by decide
  have hdescent : baseEnd_4474684 < baseStart_4474684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474694 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_4474694 : Nat := 118140960795 + 4474694 * 2 ^ 59
def prefixEnd_4474694 : Nat := 4983230072969 + 3 ^ 40 * 4474694 * 2
def baseEnd_4474694 : Nat := 765889601263273657615421

theorem tailTrace_4474694 : CollatzResearch.WordTrace tailWord_4474694 prefixEnd_4474694 765889601263273657615421 := by
  unfold tailWord_4474694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100171814092354054309223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 108803665367303553158596757 5100171814092354054309223)
  ·
    refine ⟨7650257721138531081463835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5100171814092354054309223 7650257721138531081463835)
    ·
      refine ⟨11475386581707796622195753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650257721138531081463835 11475386581707796622195753)
      ·
        refine ⟨8606539936280847466646815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11475386581707796622195753 8606539936280847466646815)
        ·
          refine ⟨12909809904421271199970223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8606539936280847466646815 12909809904421271199970223)
          ·
            refine ⟨19364714856631906799955335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12909809904421271199970223 19364714856631906799955335)
            ·
              refine ⟨29047072284947860199933003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19364714856631906799955335 29047072284947860199933003)
              ·
                refine ⟨43570608427421790299899505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29047072284947860199933003 43570608427421790299899505)
                ·
                  refine ⟨32677956320566342724924629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43570608427421790299899505 32677956320566342724924629)
                  ·
                    refine ⟨765889601263273657615421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32677956320566342724924629 765889601263273657615421)
                    ·
                      rfl

theorem cell23_4474694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_4474694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474694 prefixEnd_4474694 := by exact prefixLift 4474694
  have htrace : WordTrace (prefixWord ++ tailWord_4474694) baseStart_4474694 baseEnd_4474694 := by
    simpa [prefixWord, tailWord_4474694, baseEnd_4474694] using wordTrace_append hprefix tailTrace_4474694
  have hstable : (prefixWord ++ tailWord_4474694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474694).length < 2 ^ (prefixWord ++ tailWord_4474694).sum := by decide
  have hdescent : baseEnd_4474694 < baseStart_4474694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474697 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 3, 4, 2]
def baseStart_4474697 : Nat := 118140960795 + 4474697 * 2 ^ 59
def prefixEnd_4474697 : Nat := 4983230072969 + 3 ^ 40 * 4474697 * 2
def baseEnd_4474697 : Nat := 2297670344231784461108749

theorem tailTrace_4474697 : CollatzResearch.WordTrace tailWord_4474697 prefixEnd_4474697 2297670344231784461108749 := by
  unfold tailWord_4474697
  simp only [CollatzResearch.WordTrace]
  refine ⟨163205607469944461250254345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108803738313296307500169563 163205607469944461250254345)
  ·
    refine ⟨122404205602458345937690759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163205607469944461250254345 122404205602458345937690759)
    ·
      refine ⟨183606308403687518906536139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122404205602458345937690759 183606308403687518906536139)
      ·
        refine ⟨275409462605531278359804209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183606308403687518906536139 275409462605531278359804209)
        ·
          refine ⟨206557096954148458769853157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275409462605531278359804209 206557096954148458769853157)
          ·
            refine ⟨38729455678902836019347467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206557096954148458769853157 38729455678902836019347467)
            ·
              refine ⟨58094183518354254029021201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38729455678902836019347467 58094183518354254029021201)
              ·
                refine ⟨43570637638765690521765901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58094183518354254029021201 43570637638765690521765901)
                ·
                  refine ⟨16338989114537133945662213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43570637638765690521765901 16338989114537133945662213)
                  ·
                    refine ⟨3063560458975712614811665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16338989114537133945662213 3063560458975712614811665)
                    ·
                      refine ⟨2297670344231784461108749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063560458975712614811665 2297670344231784461108749)
                      ·
                        rfl

theorem cell23_4474697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 4, 2].length) (baseStart_4474697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474697 prefixEnd_4474697 := by exact prefixLift 4474697
  have htrace : WordTrace (prefixWord ++ tailWord_4474697) baseStart_4474697 baseEnd_4474697 := by
    simpa [prefixWord, tailWord_4474697, baseEnd_4474697] using wordTrace_append hprefix tailTrace_4474697
  have hstable : (prefixWord ++ tailWord_4474697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474697).length < 2 ^ (prefixWord ++ tailWord_4474697).sum := by decide
  have hdescent : baseEnd_4474697 < baseStart_4474697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474701 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 3, 3, 2]
def baseStart_4474701 : Nat := 118140960795 + 4474701 * 2 ^ 59
def prefixEnd_4474701 : Nat := 4983230072969 + 3 ^ 40 * 4474701 * 2
def baseEnd_4474701 : Nat := 2297672398154402445458731

theorem tailTrace_4474701 : CollatzResearch.WordTrace tailWord_4474701 prefixEnd_4474701 2297672398154402445458731 := by
  unfold tailWord_4474701
  simp only [CollatzResearch.WordTrace]
  refine ⟨163205753361929969933399957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108803835574619979955599971 163205753361929969933399957)
  ·
    refine ⟨7650269688840467340628123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 163205753361929969933399957 7650269688840467340628123)
    ·
      refine ⟨11475404533260701010942185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650269688840467340628123 11475404533260701010942185)
      ·
        refine ⟨8606553399945525758206639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11475404533260701010942185 8606553399945525758206639)
        ·
          refine ⟨12909830099918288637309959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8606553399945525758206639 12909830099918288637309959)
          ·
            refine ⟨19364745149877432955964939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12909830099918288637309959 19364745149877432955964939)
            ·
              refine ⟨29047117724816149433947409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19364745149877432955964939 29047117724816149433947409)
              ·
                refine ⟨21785338293612112075460557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29047117724816149433947409 21785338293612112075460557)
                ·
                  refine ⟨8169501860104542028297709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21785338293612112075460557 8169501860104542028297709)
                  ·
                    refine ⟨3063563197539203260611641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8169501860104542028297709 3063563197539203260611641)
                    ·
                      refine ⟨2297672398154402445458731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063563197539203260611641 2297672398154402445458731)
                      ·
                        rfl

theorem cell23_4474701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_4474701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474701 prefixEnd_4474701 := by exact prefixLift 4474701
  have htrace : WordTrace (prefixWord ++ tailWord_4474701) baseStart_4474701 baseEnd_4474701 := by
    simpa [prefixWord, tailWord_4474701, baseEnd_4474701] using wordTrace_append hprefix tailTrace_4474701
  have hstable : (prefixWord ++ tailWord_4474701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474701).length < 2 ^ (prefixWord ++ tailWord_4474701).sum := by decide
  have hdescent : baseEnd_4474701 < baseStart_4474701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474714 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_4474714 : Nat := 118140960795 + 4474714 * 2 ^ 59
def prefixEnd_4474714 : Nat := 4983230072969 + 3 ^ 40 * 4474714 * 2
def baseEnd_4474714 : Nat := 2297679073402910894596171

theorem tailTrace_4474714 : CollatzResearch.WordTrace tailWord_4474714 prefixEnd_4474714 2297679073402910894596171 := by
  unfold tailWord_4474714
  simp only [CollatzResearch.WordTrace]
  refine ⟨40801556877720718288405799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108804151673921915435748797 40801556877720718288405799)
  ·
    refine ⟨61202335316581077432608699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40801556877720718288405799 61202335316581077432608699)
    ·
      refine ⟨91803502974871616148913049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61202335316581077432608699 91803502974871616148913049)
      ·
        refine ⟨68852627231153712111684787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91803502974871616148913049 68852627231153712111684787)
        ·
          refine ⟨103278940846730568167527181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68852627231153712111684787 103278940846730568167527181)
          ·
            refine ⟨38729602817523963062822693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103278940846730568167527181 38729602817523963062822693)
            ·
              refine ⟨7261800528285743074279255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38729602817523963062822693 7261800528285743074279255)
              ·
                refine ⟨10892700792428614611418883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7261800528285743074279255 10892700792428614611418883)
                ·
                  refine ⟨16339051188642921917128325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10892700792428614611418883 16339051188642921917128325)
                  ·
                    refine ⟨3063572097870547859461561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16339051188642921917128325 3063572097870547859461561)
                    ·
                      refine ⟨2297679073402910894596171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063572097870547859461561 2297679073402910894596171)
                      ·
                        rfl

theorem cell23_4474714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_4474714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474714 prefixEnd_4474714 := by exact prefixLift 4474714
  have htrace : WordTrace (prefixWord ++ tailWord_4474714) baseStart_4474714 baseEnd_4474714 := by
    simpa [prefixWord, tailWord_4474714, baseEnd_4474714] using wordTrace_append hprefix tailTrace_4474714
  have hstable : (prefixWord ++ tailWord_4474714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474714).length < 2 ^ (prefixWord ++ tailWord_4474714).sum := by decide
  have hdescent : baseEnd_4474714 < baseStart_4474714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474720 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 9]
def baseStart_4474720 : Nat := 118140960795 + 4474720 * 2 ^ 59
def prefixEnd_4474720 : Nat := 4983230072969 + 3 ^ 40 * 4474720 * 2
def baseEnd_4474720 : Nat := 255298017142981985680127

theorem tailTrace_4474720 : CollatzResearch.WordTrace tailWord_4474720 prefixEnd_4474720 255298017142981985680127 := by
  unfold tailWord_4474720
  simp only [CollatzResearch.WordTrace]
  refine ⟨81603223174430568089170807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108804297565907424118894409 81603223174430568089170807)
  ·
    refine ⟨122404834761645852133756211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81603223174430568089170807 122404834761645852133756211)
    ·
      refine ⟨183607252142468778200634317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122404834761645852133756211 183607252142468778200634317)
      ·
        refine ⟨68852719553425791825237869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183607252142468778200634317 68852719553425791825237869)
        ·
          refine ⟨25819769832534671934464201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68852719553425791825237869 25819769832534671934464201)
          ·
            refine ⟨19364827374401003950848151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25819769832534671934464201 19364827374401003950848151)
            ·
              refine ⟨29047241061601505926272227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19364827374401003950848151 29047241061601505926272227)
              ·
                refine ⟨43570861592402258889408341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29047241061601505926272227 43570861592402258889408341)
                ·
                  refine ⟨255298017142981985680127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 43570861592402258889408341 255298017142981985680127)
                  ·
                    rfl

theorem cell23_4474720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 9].length) (baseStart_4474720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474720 prefixEnd_4474720 := by exact prefixLift 4474720
  have htrace : WordTrace (prefixWord ++ tailWord_4474720) baseStart_4474720 baseEnd_4474720 := by
    simpa [prefixWord, tailWord_4474720, baseEnd_4474720] using wordTrace_append hprefix tailTrace_4474720
  have hstable : (prefixWord ++ tailWord_4474720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474720).length < 2 ^ (prefixWord ++ tailWord_4474720).sum := by decide
  have hdescent : baseEnd_4474720 < baseStart_4474720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474787 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4]
def baseStart_4474787 : Nat := 118140960795 + 4474787 * 2 ^ 59
def prefixEnd_4474787 : Nat := 4983230072969 + 3 ^ 40 * 4474787 * 2
def baseEnd_4474787 : Nat := 2297716557490689108983335

theorem tailTrace_4474787 : CollatzResearch.WordTrace tailWord_4474787 prefixEnd_4474787 2297716557490689108983335 := by
  unfold tailWord_4474787
  simp only [CollatzResearch.WordTrace]
  refine ⟨163208890039618406621030615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108805926693078937747353743 163208890039618406621030615)
  ·
    refine ⟨244813335059427609931545923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163208890039618406621030615 244813335059427609931545923)
    ·
      refine ⟨367220002589141414897318885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244813335059427609931545923 367220002589141414897318885)
      ·
        refine ⟨68853750485464015293247291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 367220002589141414897318885 68853750485464015293247291)
        ·
          refine ⟨103280625728196022939870937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68853750485464015293247291 103280625728196022939870937)
          ·
            refine ⟨77460469296147017204903203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103280625728196022939870937 77460469296147017204903203)
            ·
              refine ⟨116190703944220525807354805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 77460469296147017204903203 116190703944220525807354805)
              ·
                refine ⟨10892878494770674294439513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116190703944220525807354805 10892878494770674294439513)
                ·
                  refine ⟨8169658871078005720829635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10892878494770674294439513 8169658871078005720829635)
                  ·
                    refine ⟨12254488306617008581244453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8169658871078005720829635 12254488306617008581244453)
                    ·
                      refine ⟨2297716557490689108983335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12254488306617008581244453 2297716557490689108983335)
                      ·
                        rfl

theorem cell23_4474787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_4474787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474787 prefixEnd_4474787 := by exact prefixLift 4474787
  have htrace : WordTrace (prefixWord ++ tailWord_4474787) baseStart_4474787 baseEnd_4474787 := by
    simpa [prefixWord, tailWord_4474787, baseEnd_4474787] using wordTrace_append hprefix tailTrace_4474787
  have hstable : (prefixWord ++ tailWord_4474787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474787).length < 2 ^ (prefixWord ++ tailWord_4474787).sum := by decide
  have hdescent : baseEnd_4474787 < baseStart_4474787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474827 : List Nat := [1, 1, 1, 1, 3, 4, 3, 3, 6]
def baseStart_4474827 : Nat := 118140960795 + 4474827 * 2 ^ 59
def prefixEnd_4474827 : Nat := 4983230072969 + 3 ^ 40 * 4474827 * 2
def baseEnd_4474827 : Nat := 255304121857429883609239

theorem tailTrace_4474827 : CollatzResearch.WordTrace tailWord_4474827 prefixEnd_4474827 255304121857429883609239 := by
  unfold tailWord_4474827
  simp only [CollatzResearch.WordTrace]
  refine ⟨163210348959473493452486735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108806899306315662301657823 163210348959473493452486735)
  ·
    refine ⟨244815523439210240178730103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163210348959473493452486735 244815523439210240178730103)
    ·
      refine ⟨367223285158815360268095155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244815523439210240178730103 367223285158815360268095155)
      ·
        refine ⟨550834927738223040402142733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367223285158815360268095155 550834927738223040402142733)
        ·
          refine ⟨206563097901833640150803525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 550834927738223040402142733 206563097901833640150803525)
          ·
            refine ⟨38730580856593807528275661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206563097901833640150803525 38730580856593807528275661)
            ·
              refine ⟨14523967821222677823103373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38730580856593807528275661 14523967821222677823103373)
              ·
                refine ⟨5446487932958504183663765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14523967821222677823103373 5446487932958504183663765)
                ·
                  refine ⟨255304121857429883609239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5446487932958504183663765 255304121857429883609239)
                  ·
                    rfl

theorem cell23_4474827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 3, 6].length) (baseStart_4474827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474827 prefixEnd_4474827 := by exact prefixLift 4474827
  have htrace : WordTrace (prefixWord ++ tailWord_4474827) baseStart_4474827 baseEnd_4474827 := by
    simpa [prefixWord, tailWord_4474827, baseEnd_4474827] using wordTrace_append hprefix tailTrace_4474827
  have hstable : (prefixWord ++ tailWord_4474827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474827).length < 2 ^ (prefixWord ++ tailWord_4474827).sum := by decide
  have hdescent : baseEnd_4474827 < baseStart_4474827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474838 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_4474838 : Nat := 118140960795 + 4474838 * 2 ^ 59
def prefixEnd_4474838 : Nat := 4983230072969 + 3 ^ 40 * 4474838 * 2
def baseEnd_4474838 : Nat := 2297742745004068409445601

theorem tailTrace_4474838 : CollatzResearch.WordTrace tailWord_4474838 prefixEnd_4474838 2297742745004068409445601 := by
  unfold tailWord_4474838
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200671885152102645696073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108807166774955761554091445 10200671885152102645696073)
  ·
    refine ⟨7650503913864076984272055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10200671885152102645696073 7650503913864076984272055)
    ·
      refine ⟨11475755870796115476408083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7650503913864076984272055 11475755870796115476408083)
      ·
        refine ⟨17213633806194173214612125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11475755870796115476408083 17213633806194173214612125)
        ·
          refine ⟨6455112677322814955479547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17213633806194173214612125 6455112677322814955479547)
          ·
            refine ⟨9682669015984222433219321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455112677322814955479547 9682669015984222433219321)
            ·
              refine ⟨7262001761988166824914491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9682669015984222433219321 7262001761988166824914491)
              ·
                refine ⟨10893002642982250237371737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7262001761988166824914491 10893002642982250237371737)
                ·
                  refine ⟨8169751982236687678028803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10893002642982250237371737 8169751982236687678028803)
                  ·
                    refine ⟨12254627973355031517043205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8169751982236687678028803 12254627973355031517043205)
                    ·
                      refine ⟨2297742745004068409445601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12254627973355031517043205 2297742745004068409445601)
                      ·
                        rfl

theorem cell23_4474838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_4474838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474838 prefixEnd_4474838 := by exact prefixLift 4474838
  have htrace : WordTrace (prefixWord ++ tailWord_4474838) baseStart_4474838 baseEnd_4474838 := by
    simpa [prefixWord, tailWord_4474838, baseEnd_4474838] using wordTrace_append hprefix tailTrace_4474838
  have hstable : (prefixWord ++ tailWord_4474838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474838).length < 2 ^ (prefixWord ++ tailWord_4474838).sum := by decide
  have hdescent : baseEnd_4474838 < baseStart_4474838 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474841 : List Nat := [1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 3]
def baseStart_4474841 : Nat := 118140960795 + 4474841 * 2 ^ 59
def prefixEnd_4474841 : Nat := 4983230072969 + 3 ^ 40 * 4474841 * 2
def baseEnd_4474841 : Nat := 2297744285446031897708087

theorem tailTrace_4474841 : CollatzResearch.WordTrace tailWord_4474841 prefixEnd_4474841 2297744285446031897708087 := by
  unfold tailWord_4474841
  simp only [CollatzResearch.WordTrace]
  refine ⟨163210859581422773843496377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108807239720948515895664251 163210859581422773843496377)
  ·
    refine ⟨122408144686067080382622283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163210859581422773843496377 122408144686067080382622283)
    ·
      refine ⟨183612217029100620573933425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122408144686067080382622283 183612217029100620573933425)
      ·
        refine ⟨137709162771825465430450069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183612217029100620573933425 137709162771825465430450069)
        ·
          refine ⟨6455117004929318692052347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 137709162771825465430450069 6455117004929318692052347)
          ·
            refine ⟨9682675507393978038078521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455117004929318692052347 9682675507393978038078521)
            ·
              refine ⟨7262006630545483528558891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9682675507393978038078521 7262006630545483528558891)
              ·
                refine ⟨10893009945818225292838337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7262006630545483528558891 10893009945818225292838337)
                ·
                  refine ⟨8169757459363668969628753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10893009945818225292838337 8169757459363668969628753)
                  ·
                    refine ⟨6127318094522751727221565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8169757459363668969628753 6127318094522751727221565)
                    ·
                      refine ⟨2297744285446031897708087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6127318094522751727221565 2297744285446031897708087)
                      ·
                        rfl

theorem cell23_4474841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_4474841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474841 prefixEnd_4474841 := by exact prefixLift 4474841
  have htrace : WordTrace (prefixWord ++ tailWord_4474841) baseStart_4474841 baseEnd_4474841 := by
    simpa [prefixWord, tailWord_4474841, baseEnd_4474841] using wordTrace_append hprefix tailTrace_4474841
  have hstable : (prefixWord ++ tailWord_4474841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474841).length < 2 ^ (prefixWord ++ tailWord_4474841).sum := by decide
  have hdescent : baseEnd_4474841 < baseStart_4474841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474865 : List Nat := [1, 2, 2, 2, 5, 2, 2, 2, 1, 4]
def baseStart_4474865 : Nat := 118140960795 + 4474865 * 2 ^ 59
def prefixEnd_4474865 : Nat := 4983230072969 + 3 ^ 40 * 4474865 * 2
def baseEnd_4474865 : Nat := 765918869660579934602659

theorem tailTrace_4474865 : CollatzResearch.WordTrace tailWord_4474865 prefixEnd_4474865 765918869660579934602659 := by
  unfold tailWord_4474865
  simp only [CollatzResearch.WordTrace]
  refine ⟨163211734933335825942370049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108807823288890550628246699 163211734933335825942370049)
  ·
    refine ⟨122408801200001869456777537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163211734933335825942370049 122408801200001869456777537)
    ·
      refine ⟨91806600900001402092583153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122408801200001869456777537 91806600900001402092583153)
      ·
        refine ⟨68854950675001051569437365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91806600900001402092583153 68854950675001051569437365)
        ·
          refine ⟨6455151625781348584634753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68854950675001051569437365 6455151625781348584634753)
          ·
            refine ⟨4841363719336011438476065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6455151625781348584634753 4841363719336011438476065)
            ·
              refine ⟨3631022789502008578857049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4841363719336011438476065 3631022789502008578857049)
              ·
                refine ⟨2723267092126506434142787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3631022789502008578857049 2723267092126506434142787)
                ·
                  refine ⟨4084900638189759651214181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723267092126506434142787 4084900638189759651214181)
                  ·
                    refine ⟨765918869660579934602659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084900638189759651214181 765918869660579934602659)
                    ·
                      rfl

theorem cell23_4474865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2, 1, 4].length) (baseStart_4474865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474865 prefixEnd_4474865 := by exact prefixLift 4474865
  have htrace : WordTrace (prefixWord ++ tailWord_4474865) baseStart_4474865 baseEnd_4474865 := by
    simpa [prefixWord, tailWord_4474865, baseEnd_4474865] using wordTrace_append hprefix tailTrace_4474865
  have hstable : (prefixWord ++ tailWord_4474865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474865).length < 2 ^ (prefixWord ++ tailWord_4474865).sum := by decide
  have hdescent : baseEnd_4474865 < baseStart_4474865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474894 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4474894 : Nat := 118140960795 + 4474894 * 2 ^ 59
def prefixEnd_4474894 : Nat := 4983230072969 + 3 ^ 40 * 4474894 * 2
def baseEnd_4474894 : Nat := 2297771499920720190345343

theorem tailTrace_4474894 : CollatzResearch.WordTrace tailWord_4474894 prefixEnd_4474894 2297771499920720190345343 := by
  unfold tailWord_4474894
  simp only [CollatzResearch.WordTrace]
  refine ⟨20401599081278845486896967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108808528433487175930117157 20401599081278845486896967)
  ·
    refine ⟨30602398621918268230345451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20401599081278845486896967 30602398621918268230345451)
    ·
      refine ⟨45903597932877402345518177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30602398621918268230345451 45903597932877402345518177)
      ·
        refine ⟨34427698449658051759138633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45903597932877402345518177 34427698449658051759138633)
        ·
          refine ⟨25820773837243538819353975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34427698449658051759138633 25820773837243538819353975)
          ·
            refine ⟨38731160755865308229030963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25820773837243538819353975 38731160755865308229030963)
            ·
              refine ⟨58096741133797962343546445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38731160755865308229030963 58096741133797962343546445)
              ·
                refine ⟨21786277925174235878829917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58096741133797962343546445 21786277925174235878829917)
                ·
                  refine ⟨8169854221940338454561219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21786277925174235878829917 8169854221940338454561219)
                  ·
                    refine ⟨12254781332910507681841829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8169854221940338454561219 12254781332910507681841829)
                    ·
                      refine ⟨2297771499920720190345343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12254781332910507681841829 2297771499920720190345343)
                      ·
                        rfl

theorem cell23_4474894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4474894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474894 prefixEnd_4474894 := by exact prefixLift 4474894
  have htrace : WordTrace (prefixWord ++ tailWord_4474894) baseStart_4474894 baseEnd_4474894 := by
    simpa [prefixWord, tailWord_4474894, baseEnd_4474894] using wordTrace_append hprefix tailTrace_4474894
  have hstable : (prefixWord ++ tailWord_4474894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474894).length < 2 ^ (prefixWord ++ tailWord_4474894).sum := by decide
  have hdescent : baseEnd_4474894 < baseStart_4474894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474904 : List Nat := [2, 1, 2, 3, 2, 1, 2, 2, 4, 4]
def baseStart_4474904 : Nat := 118140960795 + 4474904 * 2 ^ 59
def prefixEnd_4474904 : Nat := 4983230072969 + 3 ^ 40 * 4474904 * 2
def baseEnd_4474904 : Nat := 765925544909088383740099

theorem tailTrace_4474904 : CollatzResearch.WordTrace tailWord_4474904 prefixEnd_4474904 765925544909088383740099 := by
  unfold tailWord_4474904
  simp only [CollatzResearch.WordTrace]
  refine ⟨81606578690097267801519883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108808771586796357068693177 81606578690097267801519883)
  ·
    refine ⟨122409868035145901702279825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81606578690097267801519883 122409868035145901702279825)
    ·
      refine ⟨91807401026359426276709869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 122409868035145901702279825 91807401026359426276709869)
      ·
        refine ⟨34427775384884784853766201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91807401026359426276709869 34427775384884784853766201)
        ·
          refine ⟨25820831538663588640324651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34427775384884784853766201 25820831538663588640324651)
          ·
            refine ⟨38731247307995382960486977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25820831538663588640324651 38731247307995382960486977)
            ·
              refine ⟨29048435480996537220365233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38731247307995382960486977 29048435480996537220365233)
              ·
                refine ⟨21786326610747402915273925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29048435480996537220365233 21786326610747402915273925)
                ·
                  refine ⟨4084936239515138046613861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21786326610747402915273925 4084936239515138046613861)
                  ·
                    refine ⟨765925544909088383740099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4084936239515138046613861 765925544909088383740099)
                    ·
                      rfl

theorem cell23_4474904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_4474904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474904 prefixEnd_4474904 := by exact prefixLift 4474904
  have htrace : WordTrace (prefixWord ++ tailWord_4474904) baseStart_4474904 baseEnd_4474904 := by
    simpa [prefixWord, tailWord_4474904, baseEnd_4474904] using wordTrace_append hprefix tailTrace_4474904
  have hstable : (prefixWord ++ tailWord_4474904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474904).length < 2 ^ (prefixWord ++ tailWord_4474904).sum := by decide
  have hdescent : baseEnd_4474904 < baseStart_4474904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474907 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4]
def baseStart_4474907 : Nat := 118140960795 + 4474907 * 2 ^ 59
def prefixEnd_4474907 : Nat := 4983230072969 + 3 ^ 40 * 4474907 * 2
def baseEnd_4474907 : Nat := 2297778175169228639482783

theorem tailTrace_4474907 : CollatzResearch.WordTrace tailWord_4474907 prefixEnd_4474907 2297778175169228639482783 := by
  unfold tailWord_4474907
  simp only [CollatzResearch.WordTrace]
  refine ⟨163213266799183667115398975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108808844532789111410265983 163213266799183667115398975)
  ·
    refine ⟨244819900198775500673098463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163213266799183667115398975 244819900198775500673098463)
    ·
      refine ⟨367229850298163251009647695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244819900198775500673098463 367229850298163251009647695)
      ·
        refine ⟨550844775447244876514471543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 367229850298163251009647695 550844775447244876514471543)
        ·
          refine ⟨826267163170867314771707315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 550844775447244876514471543 826267163170867314771707315)
          ·
            refine ⟨1239400744756300972157560973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 826267163170867314771707315 1239400744756300972157560973)
            ·
              refine ⟨464775279283612864559085365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1239400744756300972157560973 464775279283612864559085365)
              ·
                refine ⟨43572682432838706052414253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 464775279283612864559085365 43572682432838706052414253)
                ·
                  refine ⟨16339755912314514769655345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43572682432838706052414253 16339755912314514769655345)
                  ·
                    refine ⟨12254816934235886077241509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16339755912314514769655345 12254816934235886077241509)
                    ·
                      refine ⟨2297778175169228639482783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12254816934235886077241509 2297778175169228639482783)
                      ·
                        rfl

theorem cell23_4474907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 2, 4].length) (baseStart_4474907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474907 prefixEnd_4474907 := by exact prefixLift 4474907
  have htrace : WordTrace (prefixWord ++ tailWord_4474907) baseStart_4474907 baseEnd_4474907 := by
    simpa [prefixWord, tailWord_4474907, baseEnd_4474907] using wordTrace_append hprefix tailTrace_4474907
  have hstable : (prefixWord ++ tailWord_4474907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474907).length < 2 ^ (prefixWord ++ tailWord_4474907).sum := by decide
  have hdescent : baseEnd_4474907 < baseStart_4474907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474908 : List Nat := [2, 2, 3, 1, 3, 3, 2, 1, 1, 5]
def baseStart_4474908 : Nat := 118140960795 + 4474908 * 2 ^ 59
def prefixEnd_4474908 : Nat := 4983230072969 + 3 ^ 40 * 4474908 * 2
def baseEnd_4474908 : Nat := 765926229549961045190093

theorem tailTrace_4474908 : CollatzResearch.WordTrace tailWord_4474908 prefixEnd_4474908 765926229549961045190093 := by
  unfold tailWord_4474908
  simp only [CollatzResearch.WordTrace]
  refine ⟨81606651636090022143092689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108808868848120029524123585 81606651636090022143092689)
  ·
    refine ⟨61204988727067516607319517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81606651636090022143092689 61204988727067516607319517)
    ·
      refine ⟨22951870772650318727744819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61204988727067516607319517 22951870772650318727744819)
      ·
        refine ⟨34427806158975478091617229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22951870772650318727744819 34427806158975478091617229)
        ·
          refine ⟨12910427309615804284356461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34427806158975478091617229 12910427309615804284356461)
          ·
            refine ⟨4841410241105926606633673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12910427309615804284356461 4841410241105926606633673)
            ·
              refine ⟨3631057680829444954975255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4841410241105926606633673 3631057680829444954975255)
              ·
                refine ⟨5446586521244167432462883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631057680829444954975255 5446586521244167432462883)
                ·
                  refine ⟨8169879781866251148694325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446586521244167432462883 8169879781866251148694325)
                  ·
                    refine ⟨765926229549961045190093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8169879781866251148694325 765926229549961045190093)
                    ·
                      rfl

theorem cell23_4474908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_4474908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474908 prefixEnd_4474908 := by exact prefixLift 4474908
  have htrace : WordTrace (prefixWord ++ tailWord_4474908) baseStart_4474908 baseEnd_4474908 := by
    simpa [prefixWord, tailWord_4474908, baseEnd_4474908] using wordTrace_append hprefix tailTrace_4474908
  have hstable : (prefixWord ++ tailWord_4474908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474908).length < 2 ^ (prefixWord ++ tailWord_4474908).sum := by decide
  have hdescent : baseEnd_4474908 < baseStart_4474908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474911 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 5, 2, 2]
def baseStart_4474911 : Nat := 118140960795 + 4474911 * 2 ^ 59
def prefixEnd_4474911 : Nat := 4983230072969 + 3 ^ 40 * 4474911 * 2
def baseEnd_4474911 : Nat := 2297780229091846623832765

theorem tailTrace_4474911 : CollatzResearch.WordTrace tailWord_4474911 prefixEnd_4474911 2297780229091846623832765 := by
  unfold tailWord_4474911
  simp only [CollatzResearch.WordTrace]
  refine ⟨163213412691169175798544587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108808941794112783865696391 163213412691169175798544587)
  ·
    refine ⟨244820119036753763697816881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163213412691169175798544587 244820119036753763697816881)
    ·
      refine ⟨183615089277565322773362661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244820119036753763697816881 183615089277565322773362661)
      ·
        refine ⟨34427829239543498020005499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 183615089277565322773362661 34427829239543498020005499)
        ·
          refine ⟨51641743859315247030008249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34427829239543498020005499 51641743859315247030008249)
          ·
            refine ⟨38731307894486435272506187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51641743859315247030008249 38731307894486435272506187)
            ·
              refine ⟨58096961841729652908759281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38731307894486435272506187 58096961841729652908759281)
              ·
                refine ⟨43572721381297239681569461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58096961841729652908759281 43572721381297239681569461)
                ·
                  refine ⟨4084942629496616220147137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43572721381297239681569461 4084942629496616220147137)
                  ·
                    refine ⟨3063706972122462165110353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084942629496616220147137 3063706972122462165110353)
                    ·
                      refine ⟨2297780229091846623832765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063706972122462165110353 2297780229091846623832765)
                      ·
                        rfl

theorem cell23_4474911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_4474911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474911 prefixEnd_4474911 := by exact prefixLift 4474911
  have htrace : WordTrace (prefixWord ++ tailWord_4474911) baseStart_4474911 baseEnd_4474911 := by
    simpa [prefixWord, tailWord_4474911, baseEnd_4474911] using wordTrace_append hprefix tailTrace_4474911
  have hstable : (prefixWord ++ tailWord_4474911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474911).length < 2 ^ (prefixWord ++ tailWord_4474911).sum := by decide
  have hdescent : baseEnd_4474911 < baseStart_4474911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474914 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4474914 : Nat := 118140960795 + 4474914 * 2 ^ 59
def prefixEnd_4474914 : Nat := 4983230072969 + 3 ^ 40 * 4474914 * 2
def baseEnd_4474914 : Nat := 2297781769533810112095251

theorem tailTrace_4474914 : CollatzResearch.WordTrace tailWord_4474914 prefixEnd_4474914 2297781769533810112095251 := by
  unfold tailWord_4474914
  simp only [CollatzResearch.WordTrace]
  refine ⟨40803380527539576827725949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108809014740105538207269197 40803380527539576827725949)
  ·
    refine ⟨15301267697827341310397231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40803380527539576827725949 15301267697827341310397231)
    ·
      refine ⟨22951901546741011965595847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15301267697827341310397231 22951901546741011965595847)
      ·
        refine ⟨34427852320111517948393771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22951901546741011965595847 34427852320111517948393771)
        ·
          refine ⟨51641778480167276922590657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34427852320111517948393771 51641778480167276922590657)
          ·
            refine ⟨38731333860125457691942993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51641778480167276922590657 38731333860125457691942993)
            ·
              refine ⟨29048500395094093268957245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38731333860125457691942993 29048500395094093268957245)
              ·
                refine ⟨10893187648160284975858967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29048500395094093268957245 10893187648160284975858967)
                ·
                  refine ⟨16339781472240427463788451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10893187648160284975858967 16339781472240427463788451)
                  ·
                    refine ⟨24509672208360641195682677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16339781472240427463788451 24509672208360641195682677)
                    ·
                      refine ⟨2297781769533810112095251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24509672208360641195682677 2297781769533810112095251)
                      ·
                        rfl

theorem cell23_4474914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4474914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474914 prefixEnd_4474914 := by exact prefixLift 4474914
  have htrace : WordTrace (prefixWord ++ tailWord_4474914) baseStart_4474914 baseEnd_4474914 := by
    simpa [prefixWord, tailWord_4474914, baseEnd_4474914] using wordTrace_append hprefix tailTrace_4474914
  have hstable : (prefixWord ++ tailWord_4474914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474914).length < 2 ^ (prefixWord ++ tailWord_4474914).sum := by decide
  have hdescent : baseEnd_4474914 < baseStart_4474914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474917 : List Nat := [1, 3, 1, 2, 2, 4, 10]
def baseStart_4474917 : Nat := 118140960795 + 4474917 * 2 ^ 59
def prefixEnd_4474917 : Nat := 4983230072969 + 3 ^ 40 * 4474917 * 2
def baseEnd_4474917 : Nat := 28367695184886093831577

theorem tailTrace_4474917 : CollatzResearch.WordTrace tailWord_4474917 prefixEnd_4474917 28367695184886093831577 := by
  unfold tailWord_4474917
  simp only [CollatzResearch.WordTrace]
  refine ⟨163213631529147438823263005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108809087686098292548842003 163213631529147438823263005)
  ·
    refine ⟨61205111823430289558723627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163213631529147438823263005 61205111823430289558723627)
    ·
      refine ⟨91807667735145434338085441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61205111823430289558723627 91807667735145434338085441)
      ·
        refine ⟨68855750801359075753564081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 91807667735145434338085441 68855750801359075753564081)
        ·
          refine ⟨51641813101019306815173061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68855750801359075753564081 51641813101019306815173061)
          ·
            refine ⟨9682839956441120027844949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51641813101019306815173061 9682839956441120027844949)
            ·
              refine ⟨28367695184886093831577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9682839956441120027844949 28367695184886093831577)
              ·
                rfl

theorem cell23_4474917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 10].length) (baseStart_4474917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474917 prefixEnd_4474917 := by exact prefixLift 4474917
  have htrace : WordTrace (prefixWord ++ tailWord_4474917) baseStart_4474917 baseEnd_4474917 := by
    simpa [prefixWord, tailWord_4474917, baseEnd_4474917] using wordTrace_append hprefix tailTrace_4474917
  have hstable : (prefixWord ++ tailWord_4474917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474917).length < 2 ^ (prefixWord ++ tailWord_4474917).sum := by decide
  have hdescent : baseEnd_4474917 < baseStart_4474917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474928 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2]
def baseStart_4474928 : Nat := 118140960795 + 4474928 * 2 ^ 59
def prefixEnd_4474928 : Nat := 4983230072969 + 3 ^ 40 * 4474928 * 2
def baseEnd_4474928 : Nat := 2297788958262973057320187

theorem tailTrace_4474928 : CollatzResearch.WordTrace tailWord_4474928 prefixEnd_4474928 2297788958262973057320187 := by
  unfold tailWord_4474928
  simp only [CollatzResearch.WordTrace]
  refine ⟨81607016366053793850956719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108809355154738391801275625 81607016366053793850956719)
  ·
    refine ⟨122410524549080690776435079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81607016366053793850956719 122410524549080690776435079)
    ·
      refine ⟨183615786823621036164652619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122410524549080690776435079 183615786823621036164652619)
      ·
        refine ⟨275423680235431554246978929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183615786823621036164652619 275423680235431554246978929)
        ·
          refine ⟨206567760176573665685234197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275423680235431554246978929 206567760176573665685234197)
          ·
            refine ⟨9682863758276890578995353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 206567760176573665685234197 9682863758276890578995353)
            ·
              refine ⟨7262147818707667934246515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9682863758276890578995353 7262147818707667934246515)
              ·
                refine ⟨10893221728061501901369773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7262147818707667934246515 10893221728061501901369773)
                ·
                  refine ⟨4084958148023063213013665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10893221728061501901369773 4084958148023063213013665)
                  ·
                    refine ⟨3063718611017297409760249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4084958148023063213013665 3063718611017297409760249)
                    ·
                      refine ⟨2297788958262973057320187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063718611017297409760249 2297788958262973057320187)
                      ·
                        rfl

theorem cell23_4474928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 3, 2, 2].length) (baseStart_4474928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474928 prefixEnd_4474928 := by exact prefixLift 4474928
  have htrace : WordTrace (prefixWord ++ tailWord_4474928) baseStart_4474928 baseEnd_4474928 := by
    simpa [prefixWord, tailWord_4474928, baseEnd_4474928] using wordTrace_append hprefix tailTrace_4474928
  have hstable : (prefixWord ++ tailWord_4474928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474928).length < 2 ^ (prefixWord ++ tailWord_4474928).sum := by decide
  have hdescent : baseEnd_4474928 < baseStart_4474928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4474934 : List Nat := [5, 1, 2, 1, 1, 1, 2, 10]
def baseStart_4474934 : Nat := 118140960795 + 4474934 * 2 ^ 59
def prefixEnd_4474934 : Nat := 4983230072969 + 3 ^ 40 * 4474934 * 2
def baseEnd_4474934 : Nat := 85103408857292593846117

theorem tailTrace_4474934 : CollatzResearch.WordTrace tailWord_4474934 prefixEnd_4474934 85103408857292593846117 := by
  unfold tailWord_4474934
  simp only [CollatzResearch.WordTrace]
  refine ⟨10200890723130365670414491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 108809501046723900484421237 10200890723130365670414491)
  ·
    refine ⟨15301336084695548505621737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10200890723130365670414491 15301336084695548505621737)
    ·
      refine ⟨11476002063521661379216303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15301336084695548505621737 11476002063521661379216303)
      ·
        refine ⟨17214003095282492068824455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11476002063521661379216303 17214003095282492068824455)
        ·
          refine ⟨25821004642923738103236683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17214003095282492068824455 25821004642923738103236683)
          ·
            refine ⟨38731506964385607154855025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25821004642923738103236683 38731506964385607154855025)
            ·
              refine ⟨29048630223289205366141269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38731506964385607154855025 29048630223289205366141269)
              ·
                refine ⟨85103408857292593846117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29048630223289205366141269 85103408857292593846117)
                ·
                  rfl

theorem cell23_4474934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 10].length) (baseStart_4474934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4474934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4474934 prefixEnd_4474934 := by exact prefixLift 4474934
  have htrace : WordTrace (prefixWord ++ tailWord_4474934) baseStart_4474934 baseEnd_4474934 := by
    simpa [prefixWord, tailWord_4474934, baseEnd_4474934] using wordTrace_append hprefix tailTrace_4474934
  have hstable : (prefixWord ++ tailWord_4474934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4474934).length < 2 ^ (prefixWord ++ tailWord_4474934).sum := by decide
  have hdescent : baseEnd_4474934 < baseStart_4474934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4474934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475004 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_4475004 : Nat := 118140960795 + 4475004 * 2 ^ 59
def prefixEnd_4475004 : Nat := 4983230072969 + 3 ^ 40 * 4475004 * 2
def baseEnd_4475004 : Nat := 2297827982792714759969837

theorem tailTrace_4475004 : CollatzResearch.WordTrace tailWord_4475004 prefixEnd_4475004 2297827982792714759969837 := by
  unfold tailWord_4475004
  simp only [CollatzResearch.WordTrace]
  refine ⟨81608402339916126340840033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108811203119888168454453377 81608402339916126340840033)
  ·
    refine ⟨61206301754937094755630025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81608402339916126340840033 61206301754937094755630025)
    ·
      refine ⟨45904726316202821066722519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61206301754937094755630025 45904726316202821066722519)
      ·
        refine ⟨68857089474304231600083779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45904726316202821066722519 68857089474304231600083779)
        ·
          refine ⟨103285634211456347400125669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68857089474304231600083779 103285634211456347400125669)
          ·
            refine ⟨19366056414648065137523563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 103285634211456347400125669 19366056414648065137523563)
            ·
              refine ⟨29049084621972097706285345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19366056414648065137523563 29049084621972097706285345)
              ·
                refine ⟨21786813466479073279714009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29049084621972097706285345 21786813466479073279714009)
                ·
                  refine ⟨16340110099859304959785507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21786813466479073279714009 16340110099859304959785507)
                  ·
                    refine ⟨24510165149788957439678261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16340110099859304959785507 24510165149788957439678261)
                    ·
                      refine ⟨2297827982792714759969837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24510165149788957439678261 2297827982792714759969837)
                      ·
                        rfl

theorem cell23_4475004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_4475004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475004 prefixEnd_4475004 := by exact prefixLift 4475004
  have htrace : WordTrace (prefixWord ++ tailWord_4475004) baseStart_4475004 baseEnd_4475004 := by
    simpa [prefixWord, tailWord_4475004, baseEnd_4475004] using wordTrace_append hprefix tailTrace_4475004
  have hstable : (prefixWord ++ tailWord_4475004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475004).length < 2 ^ (prefixWord ++ tailWord_4475004).sum := by decide
  have hdescent : baseEnd_4475004 < baseStart_4475004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475005 : List Nat := [1, 4, 1, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_4475005 : Nat := 118140960795 + 4475005 * 2 ^ 59
def prefixEnd_4475005 : Nat := 4983230072969 + 3 ^ 40 * 4475005 * 2
def baseEnd_4475005 : Nat := 2297828496273369256057333

theorem tailTrace_4475005 : CollatzResearch.WordTrace tailWord_4475005 prefixEnd_4475005 2297828496273369256057333 := by
  unfold tailWord_4475005
  simp only [CollatzResearch.WordTrace]
  refine ⟨163216841152828629852466469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108811227435219086568310979 163216841152828629852466469)
  ·
    refine ⟨30603157716155368097337463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163216841152828629852466469 30603157716155368097337463)
    ·
      refine ⟨45904736574233052146006195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30603157716155368097337463 45904736574233052146006195)
      ·
        refine ⟨68857104861349578219009293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45904736574233052146006195 68857104861349578219009293)
        ·
          refine ⟨25821414323006091832128485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68857104861349578219009293 25821414323006091832128485)
          ·
            refine ⟨4841515185563642218524091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25821414323006091832128485 4841515185563642218524091)
            ·
              refine ⟨7262272778345463327786137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4841515185563642218524091 7262272778345463327786137)
              ·
                refine ⟨5446704583759097495839603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7262272778345463327786137 5446704583759097495839603)
                ·
                  refine ⟨8170056875638646243759405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446704583759097495839603 8170056875638646243759405)
                  ·
                    refine ⟨3063771328364492341409777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8170056875638646243759405 3063771328364492341409777)
                    ·
                      refine ⟨2297828496273369256057333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063771328364492341409777 2297828496273369256057333)
                      ·
                        rfl

theorem cell23_4475005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_4475005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475005 prefixEnd_4475005 := by exact prefixLift 4475005
  have htrace : WordTrace (prefixWord ++ tailWord_4475005) baseStart_4475005 baseEnd_4475005 := by
    simpa [prefixWord, tailWord_4475005, baseEnd_4475005] using wordTrace_append hprefix tailTrace_4475005
  have hstable : (prefixWord ++ tailWord_4475005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475005).length < 2 ^ (prefixWord ++ tailWord_4475005).sum := by decide
  have hdescent : baseEnd_4475005 < baseStart_4475005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475018 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_4475018 : Nat := 118140960795 + 4475018 * 2 ^ 59
def prefixEnd_4475018 : Nat := 4983230072969 + 3 ^ 40 * 4475018 * 2
def baseEnd_4475018 : Nat := 2297835171521877705194773

theorem tailTrace_4475018 : CollatzResearch.WordTrace tailWord_4475018 prefixEnd_4475018 2297835171521877705194773 := by
  unfold tailWord_4475018
  simp only [CollatzResearch.WordTrace]
  refine ⟨40804328825445383268172427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108811543534521022048459805 40804328825445383268172427)
  ·
    refine ⟨61206493238168074902258641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40804328825445383268172427 61206493238168074902258641)
    ·
      refine ⟨45904869928626056176693981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61206493238168074902258641 45904869928626056176693981)
      ·
        refine ⟨17214326223234771066260243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45904869928626056176693981 17214326223234771066260243)
        ·
          refine ⟨25821489334852156599390365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17214326223234771066260243 25821489334852156599390365)
          ·
            refine ⟨9683058500569558724771387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25821489334852156599390365 9683058500569558724771387)
            ·
              refine ⟨14524587750854338087157081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9683058500569558724771387 14524587750854338087157081)
              ·
                refine ⟨10893440813140753565367811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14524587750854338087157081 10893440813140753565367811)
                ·
                  refine ⟨16340161219711130348051717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10893440813140753565367811 16340161219711130348051717)
                  ·
                    refine ⟨3063780228695836940259697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16340161219711130348051717 3063780228695836940259697)
                    ·
                      refine ⟨2297835171521877705194773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063780228695836940259697 2297835171521877705194773)
                      ·
                        rfl

theorem cell23_4475018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_4475018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475018 prefixEnd_4475018 := by exact prefixLift 4475018
  have htrace : WordTrace (prefixWord ++ tailWord_4475018) baseStart_4475018 baseEnd_4475018 := by
    simpa [prefixWord, tailWord_4475018, baseEnd_4475018] using wordTrace_append hprefix tailTrace_4475018
  have hstable : (prefixWord ++ tailWord_4475018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475018).length < 2 ^ (prefixWord ++ tailWord_4475018).sum := by decide
  have hdescent : baseEnd_4475018 < baseStart_4475018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475022 : List Nat := [4, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4475022 : Nat := 118140960795 + 4475022 * 2 ^ 59
def prefixEnd_4475022 : Nat := 4983230072969 + 3 ^ 40 * 4475022 * 2
def baseEnd_4475022 : Nat := 2297837225444495689544755

theorem tailTrace_4475022 : CollatzResearch.WordTrace tailWord_4475022 prefixEnd_4475022 2297837225444495689544755 := by
  unfold tailWord_4475022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20402182649220880219479415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108811640795844694503890213 20402182649220880219479415)
  ·
    refine ⟨30603273973831320329219123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20402182649220880219479415 30603273973831320329219123)
    ·
      refine ⟨45904910960746980493828685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30603273973831320329219123 45904910960746980493828685)
      ·
        refine ⟨17214341610280117685185757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45904910960746980493828685 17214341610280117685185757)
        ·
          refine ⟨6455378103855044131944659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17214341610280117685185757 6455378103855044131944659)
          ·
            refine ⟨9683067155782566197916989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455378103855044131944659 9683067155782566197916989)
            ·
              refine ⟨3631150183418462324218871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9683067155782566197916989 3631150183418462324218871)
              ·
                refine ⟨5446725275127693486328307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631150183418462324218871 5446725275127693486328307)
                ·
                  refine ⟨8170087912691540229492461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5446725275127693486328307 8170087912691540229492461)
                  ·
                    refine ⟨3063782967259327586059673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8170087912691540229492461 3063782967259327586059673)
                    ·
                      refine ⟨2297837225444495689544755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063782967259327586059673 2297837225444495689544755)
                      ·
                        rfl

theorem cell23_4475022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4475022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475022 prefixEnd_4475022 := by exact prefixLift 4475022
  have htrace : WordTrace (prefixWord ++ tailWord_4475022) baseStart_4475022 baseEnd_4475022 := by
    simpa [prefixWord, tailWord_4475022, baseEnd_4475022] using wordTrace_append hprefix tailTrace_4475022
  have hstable : (prefixWord ++ tailWord_4475022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475022).length < 2 ^ (prefixWord ++ tailWord_4475022).sum := by decide
  have hdescent : baseEnd_4475022 < baseStart_4475022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475104 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_4475104 : Nat := 118140960795 + 4475104 * 2 ^ 59
def prefixEnd_4475104 : Nat := 4983230072969 + 3 ^ 40 * 4475104 * 2
def baseEnd_4475104 : Nat := 2297879330858164368719377

theorem tailTrace_4475104 : CollatzResearch.WordTrace tailWord_4475104 prefixEnd_4475104 2297879330858164368719377 := by
  unfold tailWord_4475104
  simp only [CollatzResearch.WordTrace]
  refine ⟨81610225989734984880160183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108813634652979979840213577 81610225989734984880160183)
  ·
    refine ⟨122415338984602477320240275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81610225989734984880160183 122415338984602477320240275)
    ·
      refine ⟨183623008476903715980360413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122415338984602477320240275 183623008476903715980360413)
      ·
        refine ⟨68858628178838893492635155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183623008476903715980360413 68858628178838893492635155)
        ·
          refine ⟨103287942268258340238952733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68858628178838893492635155 103287942268258340238952733)
          ·
            refine ⟨38732978350596877589607275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103287942268258340238952733 38732978350596877589607275)
            ·
              refine ⟨58099467525895316384410913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38732978350596877589607275 58099467525895316384410913)
              ·
                refine ⟨43574600644421487288308185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58099467525895316384410913 43574600644421487288308185)
                ·
                  refine ⟨32680950483316115466231139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43574600644421487288308185 32680950483316115466231139)
                  ·
                    refine ⟨49021425724974173199346709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32680950483316115466231139 49021425724974173199346709)
                    ·
                      refine ⟨2297879330858164368719377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49021425724974173199346709 2297879330858164368719377)
                      ·
                        rfl

theorem cell23_4475104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_4475104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475104 prefixEnd_4475104 := by exact prefixLift 4475104
  have htrace : WordTrace (prefixWord ++ tailWord_4475104) baseStart_4475104 baseEnd_4475104 := by
    simpa [prefixWord, tailWord_4475104, baseEnd_4475104] using wordTrace_append hprefix tailTrace_4475104
  have hstable : (prefixWord ++ tailWord_4475104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475104).length < 2 ^ (prefixWord ++ tailWord_4475104).sum := by decide
  have hdescent : baseEnd_4475104 < baseStart_4475104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475191 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 6, 4]
def baseStart_4475191 : Nat := 118140960795 + 4475191 * 2 ^ 59
def prefixEnd_4475191 : Nat := 4983230072969 + 3 ^ 40 * 4475191 * 2
def baseEnd_4475191 : Nat := 765974667891701842777159

theorem tailTrace_4475191 : CollatzResearch.WordTrace tailWord_4475191 prefixEnd_4475191 765974667891701842777159 := by
  unfold tailWord_4475191
  simp only [CollatzResearch.WordTrace]
  refine ⟨163223625130154783618737427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108815750086769855745824951 163223625130154783618737427)
  ·
    refine ⟨244835437695232175428106141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163223625130154783618737427 244835437695232175428106141)
    ·
      refine ⟨91813289135712065785539803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 244835437695232175428106141 91813289135712065785539803)
      ·
        refine ⟨137719933703568098678309705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91813289135712065785539803 137719933703568098678309705)
        ·
          refine ⟨103289950277676074008732279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137719933703568098678309705 103289950277676074008732279)
          ·
            refine ⟨154934925416514111013098419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103289950277676074008732279 154934925416514111013098419)
            ·
              refine ⟨232402388124771166519647629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154934925416514111013098419 232402388124771166519647629)
              ·
                refine ⟨87150895546789187444867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 232402388124771166519647629 87150895546789187444867861)
                ·
                  refine ⟨4085198228755743161478181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 87150895546789187444867861 4085198228755743161478181)
                  ·
                    refine ⟨765974667891701842777159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085198228755743161478181 765974667891701842777159)
                    ·
                      rfl

theorem cell23_4475191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_4475191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475191 prefixEnd_4475191 := by exact prefixLift 4475191
  have htrace : WordTrace (prefixWord ++ tailWord_4475191) baseStart_4475191 baseEnd_4475191 := by
    simpa [prefixWord, tailWord_4475191, baseEnd_4475191] using wordTrace_append hprefix tailTrace_4475191
  have hstable : (prefixWord ++ tailWord_4475191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475191).length < 2 ^ (prefixWord ++ tailWord_4475191).sum := by decide
  have hdescent : baseEnd_4475191 < baseStart_4475191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475208 : List Nat := [2, 1, 3, 1, 1, 2, 3, 4, 2, 4]
def baseStart_4475208 : Nat := 118140960795 + 4475208 * 2 ^ 59
def prefixEnd_4475208 : Nat := 4983230072969 + 3 ^ 40 * 4475208 * 2
def baseEnd_4475208 : Nat := 765977577615410653939633

theorem tailTrace_4475208 : CollatzResearch.WordTrace tailWord_4475208 prefixEnd_4475208 765977577615410653939633 := by
  unfold tailWord_4475208
  simp only [CollatzResearch.WordTrace]
  refine ⟨81612122585546597761053139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108816163447395463681404185 81612122585546597761053139)
  ·
    refine ⟨122418183878319896641579709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81612122585546597761053139 122418183878319896641579709)
    ·
      refine ⟨45906818954369961240592391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122418183878319896641579709 45906818954369961240592391)
      ·
        refine ⟨68860228431554941860888587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45906818954369961240592391 68860228431554941860888587)
        ·
          refine ⟨103290342647332412791332881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68860228431554941860888587 103290342647332412791332881)
          ·
            refine ⟨77467756985499309593499661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 103290342647332412791332881 77467756985499309593499661)
            ·
              refine ⟨29050408869562241097562373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77467756985499309593499661 29050408869562241097562373)
              ·
                refine ⟨5446951663042920205792945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29050408869562241097562373 5446951663042920205792945)
                ·
                  refine ⟨4085213747282190154344709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5446951663042920205792945 4085213747282190154344709)
                  ·
                    refine ⟨765977577615410653939633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085213747282190154344709 765977577615410653939633)
                    ·
                      rfl

theorem cell23_4475208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_4475208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475208 prefixEnd_4475208 := by exact prefixLift 4475208
  have htrace : WordTrace (prefixWord ++ tailWord_4475208) baseStart_4475208 baseEnd_4475208 := by
    simpa [prefixWord, tailWord_4475208, baseEnd_4475208] using wordTrace_append hprefix tailTrace_4475208
  have hstable : (prefixWord ++ tailWord_4475208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475208).length < 2 ^ (prefixWord ++ tailWord_4475208).sum := by decide
  have hdescent : baseEnd_4475208 < baseStart_4475208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475218 : List Nat := [3, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_4475218 : Nat := 118140960795 + 4475218 * 2 ^ 59
def prefixEnd_4475218 : Nat := 4983230072969 + 3 ^ 40 * 4475218 * 2
def baseEnd_4475218 : Nat := 2297937867652776922693853

theorem tailTrace_4475218 : CollatzResearch.WordTrace tailWord_4475218 prefixEnd_4475218 2297937867652776922693853 := by
  unfold tailWord_4475218
  simp only [CollatzResearch.WordTrace]
  refine ⟨40806152475264241807492577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108816406600704644819980205 40806152475264241807492577)
  ·
    refine ⟨30604614356448181355619433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40806152475264241807492577 30604614356448181355619433)
    ·
      refine ⟨22953460767336136016714575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30604614356448181355619433 22953460767336136016714575)
      ·
        refine ⟨34430191151004204025071863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22953460767336136016714575 34430191151004204025071863)
        ·
          refine ⟨51645286726506306037607795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34430191151004204025071863 51645286726506306037607795)
          ·
            refine ⟨77467930089759459056411693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51645286726506306037607795 77467930089759459056411693)
            ·
              refine ⟨29050473783659797146154385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77467930089759459056411693 29050473783659797146154385)
              ·
                refine ⟨21787855337744847859615789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29050473783659797146154385 21787855337744847859615789)
                ·
                  refine ⟨8170445751654317947355921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21787855337744847859615789 8170445751654317947355921)
                  ·
                    refine ⟨6127834313740738460516941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8170445751654317947355921 6127834313740738460516941)
                    ·
                      refine ⟨2297937867652776922693853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6127834313740738460516941 2297937867652776922693853)
                      ·
                        rfl

theorem cell23_4475218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_4475218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475218 prefixEnd_4475218 := by exact prefixLift 4475218
  have htrace : WordTrace (prefixWord ++ tailWord_4475218) baseStart_4475218 baseEnd_4475218 := by
    simpa [prefixWord, tailWord_4475218, baseEnd_4475218] using wordTrace_append hprefix tailTrace_4475218
  have hstable : (prefixWord ++ tailWord_4475218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475218).length < 2 ^ (prefixWord ++ tailWord_4475218).sum := by decide
  have hdescent : baseEnd_4475218 < baseStart_4475218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475232 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2]
def baseStart_4475232 : Nat := 118140960795 + 4475232 * 2 ^ 59
def prefixEnd_4475232 : Nat := 4983230072969 + 3 ^ 40 * 4475232 * 2
def baseEnd_4475232 : Nat := 2297945056381939867918789

theorem tailTrace_4475232 : CollatzResearch.WordTrace tailWord_4475232 prefixEnd_4475232 2297945056381939867918789 := by
  unfold tailWord_4475232
  simp only [CollatzResearch.WordTrace]
  refine ⟨81612560261503123810489975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108816747015337498413986633 81612560261503123810489975)
  ·
    refine ⟨122418840392254685715734963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81612560261503123810489975 122418840392254685715734963)
    ·
      refine ⟨183628260588382028573602445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122418840392254685715734963 183628260588382028573602445)
      ·
        refine ⟨68860597720643260715100917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183628260588382028573602445 68860597720643260715100917)
        ·
          refine ⟨6455681036310305692040711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68860597720643260715100917 6455681036310305692040711)
          ·
            refine ⟨9683521554465458538061067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455681036310305692040711 9683521554465458538061067)
            ·
              refine ⟨14525282331698187807091601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9683521554465458538061067 14525282331698187807091601)
              ·
                refine ⟨10893961748773640855318701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14525282331698187807091601 10893961748773640855318701)
                ·
                  refine ⟨4085235655790115320744513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10893961748773640855318701 4085235655790115320744513)
                  ·
                    refine ⟨3063926741842586490558385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085235655790115320744513 3063926741842586490558385)
                    ·
                      refine ⟨2297945056381939867918789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063926741842586490558385 2297945056381939867918789)
                      ·
                        rfl

theorem cell23_4475232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_4475232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475232 prefixEnd_4475232 := by exact prefixLift 4475232
  have htrace : WordTrace (prefixWord ++ tailWord_4475232) baseStart_4475232 baseEnd_4475232 := by
    simpa [prefixWord, tailWord_4475232, baseEnd_4475232] using wordTrace_append hprefix tailTrace_4475232
  have hstable : (prefixWord ++ tailWord_4475232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475232).length < 2 ^ (prefixWord ++ tailWord_4475232).sum := by decide
  have hdescent : baseEnd_4475232 < baseStart_4475232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475248 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_4475248 : Nat := 118140960795 + 4475248 * 2 ^ 59
def prefixEnd_4475248 : Nat := 4983230072969 + 3 ^ 40 * 4475248 * 2
def baseEnd_4475248 : Nat := 2297953272072411805318715

theorem tailTrace_4475248 : CollatzResearch.WordTrace tailWord_4475248 prefixEnd_4475248 2297953272072411805318715 := by
  unfold tailWord_4475248
  simp only [CollatzResearch.WordTrace]
  refine ⟨81612852045474141176781199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108817136060632188235708265 81612852045474141176781199)
  ·
    refine ⟨122419278068211211765171799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81612852045474141176781199 122419278068211211765171799)
    ·
      refine ⟨183628917102316817647757699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122419278068211211765171799 183628917102316817647757699)
      ·
        refine ⟨275443375653475226471636549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183628917102316817647757699 275443375653475226471636549)
        ·
          refine ⟨51645632935026604963431853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 275443375653475226471636549 51645632935026604963431853)
          ·
            refine ⟨19367112350634976861286945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51645632935026604963431853 19367112350634976861286945)
            ·
              refine ⟨14525334262976232645965209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19367112350634976861286945 14525334262976232645965209)
              ·
                refine ⟨10894000697232174484473907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14525334262976232645965209 10894000697232174484473907)
                ·
                  refine ⟨16341001045848261726710861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10894000697232174484473907 16341001045848261726710861)
                  ·
                    refine ⟨6127875392193098147516573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16341001045848261726710861 6127875392193098147516573)
                    ·
                      refine ⟨2297953272072411805318715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6127875392193098147516573 2297953272072411805318715)
                      ·
                        rfl

theorem cell23_4475248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_4475248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475248 prefixEnd_4475248 := by exact prefixLift 4475248
  have htrace : WordTrace (prefixWord ++ tailWord_4475248) baseStart_4475248 baseEnd_4475248 := by
    simpa [prefixWord, tailWord_4475248, baseEnd_4475248] using wordTrace_append hprefix tailTrace_4475248
  have hstable : (prefixWord ++ tailWord_4475248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475248).length < 2 ^ (prefixWord ++ tailWord_4475248).sum := by decide
  have hdescent : baseEnd_4475248 < baseStart_4475248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475266 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4475266 : Nat := 118140960795 + 4475266 * 2 ^ 59
def prefixEnd_4475266 : Nat := 4983230072969 + 3 ^ 40 * 4475266 * 2
def baseEnd_4475266 : Nat := 2297962514724192734893633

theorem tailTrace_4475266 : CollatzResearch.WordTrace tailWord_4475266 prefixEnd_4475266 2297962514724192734893633 := by
  unfold tailWord_4475266
  simp only [CollatzResearch.WordTrace]
  refine ⟨40806590151220767856929413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108817573736588714285145101 40806590151220767856929413)
  ·
    refine ⟨7651235653353893973174265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40806590151220767856929413 7651235653353893973174265)
    ·
      refine ⟨5738426740015420479880699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7651235653353893973174265 5738426740015420479880699)
      ·
        refine ⟨8607640110023130719821049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738426740015420479880699 8607640110023130719821049)
        ·
          refine ⟨6455730082517348039865787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8607640110023130719821049 6455730082517348039865787)
          ·
            refine ⟨9683595123776022059798681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6455730082517348039865787 9683595123776022059798681)
            ·
              refine ⟨7262696342832016544849011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9683595123776022059798681 7262696342832016544849011)
              ·
                refine ⟨10894044514248024817273517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7262696342832016544849011 10894044514248024817273517)
                ·
                  refine ⟨4085266692843009306477569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10894044514248024817273517 4085266692843009306477569)
                  ·
                    refine ⟨3063950019632256979858177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085266692843009306477569 3063950019632256979858177)
                    ·
                      refine ⟨2297962514724192734893633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3063950019632256979858177 2297962514724192734893633)
                      ·
                        rfl

theorem cell23_4475266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4475266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475266 prefixEnd_4475266 := by exact prefixLift 4475266
  have htrace : WordTrace (prefixWord ++ tailWord_4475266) baseStart_4475266 baseEnd_4475266 := by
    simpa [prefixWord, tailWord_4475266, baseEnd_4475266] using wordTrace_append hprefix tailTrace_4475266
  have hstable : (prefixWord ++ tailWord_4475266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475266).length < 2 ^ (prefixWord ++ tailWord_4475266).sum := by decide
  have hdescent : baseEnd_4475266 < baseStart_4475266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475338 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_4475338 : Nat := 118140960795 + 4475338 * 2 ^ 59
def prefixEnd_4475338 : Nat := 4983230072969 + 3 ^ 40 * 4475338 * 2
def baseEnd_4475338 : Nat := 2297999485331316453193301

theorem tailTrace_4475338 : CollatzResearch.WordTrace tailWord_4475338 prefixEnd_4475338 2297999485331316453193301 := by
  unfold tailWord_4475338
  simp only [CollatzResearch.WordTrace]
  refine ⟨40807246665155556931084667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108819324440414818482892445 40807246665155556931084667)
  ·
    refine ⟨61210869997733335396627001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40807246665155556931084667 61210869997733335396627001)
    ·
      refine ⟨45908152498300001547470251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61210869997733335396627001 45908152498300001547470251)
      ·
        refine ⟨68862228747450002321205377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45908152498300001547470251 68862228747450002321205377)
        ·
          refine ⟨51646671560587501740904033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68862228747450002321205377 51646671560587501740904033)
          ·
            refine ⟨38735003670440626305678025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51646671560587501740904033 38735003670440626305678025)
            ·
              refine ⟨29051252752830469729258519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38735003670440626305678025 29051252752830469729258519)
              ·
                refine ⟨43576879129245704593887779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29051252752830469729258519 43576879129245704593887779)
                ·
                  refine ⟨65365318693868556890831669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 43576879129245704593887779 65365318693868556890831669)
                  ·
                    refine ⟨6127998627550177208515469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 65365318693868556890831669 6127998627550177208515469)
                    ·
                      refine ⟨2297999485331316453193301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6127998627550177208515469 2297999485331316453193301)
                      ·
                        rfl

theorem cell23_4475338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_4475338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475338 prefixEnd_4475338 := by exact prefixLift 4475338
  have htrace : WordTrace (prefixWord ++ tailWord_4475338) baseStart_4475338 baseEnd_4475338 := by
    simpa [prefixWord, tailWord_4475338, baseEnd_4475338] using wordTrace_append hprefix tailTrace_4475338
  have hstable : (prefixWord ++ tailWord_4475338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475338).length < 2 ^ (prefixWord ++ tailWord_4475338).sum := by decide
  have hdescent : baseEnd_4475338 < baseStart_4475338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475368 : List Nat := [2, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4475368 : Nat := 118140960795 + 4475368 * 2 ^ 59
def prefixEnd_4475368 : Nat := 4983230072969 + 3 ^ 40 * 4475368 * 2
def baseEnd_4475368 : Nat := 2298014889750951335818163

theorem tailTrace_4475368 : CollatzResearch.WordTrace tailWord_4475368 prefixEnd_4475368 2298014889750951335818163 := by
  unfold tailWord_4475368
  simp only [CollatzResearch.WordTrace]
  refine ⟨81615040425256771423965379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108820053900342361898620505 81615040425256771423965379)
  ·
    refine ⟨122422560637885157135948069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81615040425256771423965379 122422560637885157135948069)
    ·
      refine ⟨22954230119603466962990263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122422560637885157135948069 22954230119603466962990263)
      ·
        refine ⟨34431345179405200444485395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22954230119603466962990263 34431345179405200444485395)
        ·
          refine ⟨51647017769107800666728093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34431345179405200444485395 51647017769107800666728093)
          ·
            refine ⟨19367631663415425250023035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51647017769107800666728093 19367631663415425250023035)
            ·
              refine ⟨29051447495123137875034553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19367631663415425250023035 29051447495123137875034553)
              ·
                refine ⟨21788585621342353406275915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29051447495123137875034553 21788585621342353406275915)
                ·
                  refine ⟨32682878432013530109413873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21788585621342353406275915 32682878432013530109413873)
                  ·
                    refine ⟨24512158824010147582060405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32682878432013530109413873 24512158824010147582060405)
                    ·
                      refine ⟨2298014889750951335818163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24512158824010147582060405 2298014889750951335818163)
                      ·
                        rfl

theorem cell23_4475368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4475368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475368 prefixEnd_4475368 := by exact prefixLift 4475368
  have htrace : WordTrace (prefixWord ++ tailWord_4475368) baseStart_4475368 baseEnd_4475368 := by
    simpa [prefixWord, tailWord_4475368, baseEnd_4475368] using wordTrace_append hprefix tailTrace_4475368
  have hstable : (prefixWord ++ tailWord_4475368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475368).length < 2 ^ (prefixWord ++ tailWord_4475368).sum := by decide
  have hdescent : baseEnd_4475368 < baseStart_4475368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475395 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 2, 4, 2]
def baseStart_4475395 : Nat := 118140960795 + 4475395 * 2 ^ 59
def prefixEnd_4475395 : Nat := 4983230072969 + 3 ^ 40 * 4475395 * 2
def baseEnd_4475395 : Nat := 2298028753728622730180539

theorem tailTrace_4475395 : CollatzResearch.WordTrace tailWord_4475395 prefixEnd_4475395 2298028753728622730180539 := by
  unfold tailWord_4475395
  simp only [CollatzResearch.WordTrace]
  refine ⟨163231065621415726459163639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108820710414277150972775759 163231065621415726459163639)
  ·
    refine ⟨244846598432123589688745459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163231065621415726459163639 244846598432123589688745459)
    ·
      refine ⟨367269897648185384533118189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244846598432123589688745459 367269897648185384533118189)
      ·
        refine ⟨137726211618069519199919321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 367269897648185384533118189 137726211618069519199919321)
        ·
          refine ⟨103294658713552139399939491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137726211618069519199919321 103294658713552139399939491)
          ·
            refine ⟨154941988070328209099909237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103294658713552139399939491 154941988070328209099909237)
            ·
              refine ⟨14525811381593269603116491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 154941988070328209099909237 14525811381593269603116491)
              ·
                refine ⟨21788717072389904404674737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14525811381593269603116491 21788717072389904404674737)
                ·
                  refine ⟨16341537804292428303506053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21788717072389904404674737 16341537804292428303506053)
                  ·
                    refine ⟨3064038338304830306907385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16341537804292428303506053 3064038338304830306907385)
                    ·
                      refine ⟨2298028753728622730180539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064038338304830306907385 2298028753728622730180539)
                      ·
                        rfl

theorem cell23_4475395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 4, 2].length) (baseStart_4475395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475395 prefixEnd_4475395 := by exact prefixLift 4475395
  have htrace : WordTrace (prefixWord ++ tailWord_4475395) baseStart_4475395 baseEnd_4475395 := by
    simpa [prefixWord, tailWord_4475395, baseEnd_4475395] using wordTrace_append hprefix tailTrace_4475395
  have hstable : (prefixWord ++ tailWord_4475395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475395).length < 2 ^ (prefixWord ++ tailWord_4475395).sum := by decide
  have hdescent : baseEnd_4475395 < baseStart_4475395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475412 : List Nat := [2, 4, 3, 1, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4475412 : Nat := 118140960795 + 4475412 * 2 ^ 59
def prefixEnd_4475412 : Nat := 4983230072969 + 3 ^ 40 * 4475412 * 2
def baseEnd_4475412 : Nat := 2298037482899749163667961

theorem tailTrace_4475412 : CollatzResearch.WordTrace tailWord_4475412 prefixEnd_4475412 2298037482899749163667961 := by
  unfold tailWord_4475412
  simp only [CollatzResearch.WordTrace]
  refine ⟨81615842831177069181266245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108821123774902758908354993 81615842831177069181266245)
  ·
    refine ⟨15302970530845700471487421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 81615842831177069181266245 15302970530845700471487421)
    ·
      refine ⟨5738613949067137676807783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15302970530845700471487421 5738613949067137676807783)
      ·
        refine ⟨8607920923600706515211675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738613949067137676807783 8607920923600706515211675)
        ·
          refine ⟨12911881385401059772817513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8607920923600706515211675 12911881385401059772817513)
          ·
            refine ⟨9683911039050794829613135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12911881385401059772817513 9683911039050794829613135)
            ·
              refine ⟨14525866558576192244419703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9683911039050794829613135 14525866558576192244419703)
              ·
                refine ⟨21788799837864288366629555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14525866558576192244419703 21788799837864288366629555)
                ·
                  refine ⟨32683199756796432549944333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21788799837864288366629555 32683199756796432549944333)
                  ·
                    refine ⟨12256199908798662206229125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32683199756796432549944333 12256199908798662206229125)
                    ·
                      refine ⟨2298037482899749163667961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12256199908798662206229125 2298037482899749163667961)
                      ·
                        rfl

theorem cell23_4475412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4475412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475412 prefixEnd_4475412 := by exact prefixLift 4475412
  have htrace : WordTrace (prefixWord ++ tailWord_4475412) baseStart_4475412 baseEnd_4475412 := by
    simpa [prefixWord, tailWord_4475412, baseEnd_4475412] using wordTrace_append hprefix tailTrace_4475412
  have hstable : (prefixWord ++ tailWord_4475412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475412).length < 2 ^ (prefixWord ++ tailWord_4475412).sum := by decide
  have hdescent : baseEnd_4475412 < baseStart_4475412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475452 : List Nat := [2, 2, 2, 2, 3, 2, 3, 1, 6]
def baseStart_4475452 : Nat := 118140960795 + 4475452 * 2 ^ 59
def prefixEnd_4475452 : Nat := 4983230072969 + 3 ^ 40 * 4475452 * 2
def baseEnd_4475452 : Nat := 255339780236214334129753

theorem tailTrace_4475452 : CollatzResearch.WordTrace tailWord_4475452 prefixEnd_4475452 255339780236214334129753 := by
  unfold tailWord_4475452
  simp only [CollatzResearch.WordTrace]
  refine ⟨81616572291104612596994305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108822096388139483462659073 81616572291104612596994305)
  ·
    refine ⟨61212429218328459447745729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81616572291104612596994305 61212429218328459447745729)
    ·
      refine ⟨45909321913746344585809297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61212429218328459447745729 45909321913746344585809297)
      ·
        refine ⟨34431991435309758439356973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45909321913746344585809297 34431991435309758439356973)
        ·
          refine ⟨12911996788241159414758865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34431991435309758439356973 12911996788241159414758865)
          ·
            refine ⟨9683997591180869561069149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12911996788241159414758865 9683997591180869561069149)
            ·
              refine ⟨3631499096692826085400931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9683997591180869561069149 3631499096692826085400931)
              ·
                refine ⟨5447248645039239128101397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631499096692826085400931 5447248645039239128101397)
                ·
                  refine ⟨255339780236214334129753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5447248645039239128101397 255339780236214334129753)
                  ·
                    rfl

theorem cell23_4475452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 6].length) (baseStart_4475452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475452 prefixEnd_4475452 := by exact prefixLift 4475452
  have htrace : WordTrace (prefixWord ++ tailWord_4475452) baseStart_4475452 baseEnd_4475452 := by
    simpa [prefixWord, tailWord_4475452, baseEnd_4475452] using wordTrace_append hprefix tailTrace_4475452
  have hstable : (prefixWord ++ tailWord_4475452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475452).length < 2 ^ (prefixWord ++ tailWord_4475452).sum := by decide
  have hdescent : baseEnd_4475452 < baseStart_4475452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475455 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 3, 5, 2]
def baseStart_4475455 : Nat := 118140960795 + 4475455 * 2 ^ 59
def prefixEnd_4475455 : Nat := 4983230072969 + 3 ^ 40 * 4475455 * 2
def baseEnd_4475455 : Nat := 2298059562567892495430263

theorem tailTrace_4475455 : CollatzResearch.WordTrace tailWord_4475455 prefixEnd_4475455 2298059562567892495430263 := by
  unfold tailWord_4475455
  simp only [CollatzResearch.WordTrace]
  refine ⟨163233254001198356706347819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108822169334132237804231879 163233254001198356706347819)
  ·
    refine ⟨244849881001797535059521729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163233254001198356706347819 244849881001797535059521729)
    ·
      refine ⟨183637410751348151294641297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244849881001797535059521729 183637410751348151294641297)
      ·
        refine ⟨137728058063511113470980973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183637410751348151294641297 137728058063511113470980973)
        ·
          refine ⟨51648021773816667551617865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137728058063511113470980973 51648021773816667551617865)
          ·
            refine ⟨38736016330362500663713399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51648021773816667551617865 38736016330362500663713399)
            ·
              refine ⟨58104024495543750995570099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38736016330362500663713399 58104024495543750995570099)
              ·
                refine ⟨87156036743315626493355149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58104024495543750995570099 87156036743315626493355149)
                ·
                  refine ⟨32683513778743359935008181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87156036743315626493355149 32683513778743359935008181)
                  ·
                    refine ⟨3064079416757189993907017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32683513778743359935008181 3064079416757189993907017)
                    ·
                      refine ⟨2298059562567892495430263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064079416757189993907017 2298059562567892495430263)
                      ·
                        rfl

theorem cell23_4475455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 5, 2].length) (baseStart_4475455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475455 prefixEnd_4475455 := by exact prefixLift 4475455
  have htrace : WordTrace (prefixWord ++ tailWord_4475455) baseStart_4475455 baseEnd_4475455 := by
    simpa [prefixWord, tailWord_4475455, baseEnd_4475455] using wordTrace_append hprefix tailTrace_4475455
  have hstable : (prefixWord ++ tailWord_4475455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475455).length < 2 ^ (prefixWord ++ tailWord_4475455).sum := by decide
  have hdescent : baseEnd_4475455 < baseStart_4475455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475496 : List Nat := [2, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4475496 : Nat := 118140960795 + 4475496 * 2 ^ 59
def prefixEnd_4475496 : Nat := 4983230072969 + 3 ^ 40 * 4475496 * 2
def baseEnd_4475496 : Nat := 2298080615274726835017575

theorem tailTrace_4475496 : CollatzResearch.WordTrace tailWord_4475496 prefixEnd_4475496 2298080615274726835017575 := by
  unfold tailWord_4475496
  simp only [CollatzResearch.WordTrace]
  refine ⟨81617374697024910354295171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108823166262699880472393561 81617374697024910354295171)
  ·
    refine ⟨122426062045537365531442757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81617374697024910354295171 122426062045537365531442757)
    ·
      refine ⟨22954886633538256037145517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 122426062045537365531442757 22954886633538256037145517)
      ·
        refine ⟨8608082487576846013929569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22954886633538256037145517 8608082487576846013929569)
        ·
          refine ⟨6456061865682634510447177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8608082487576846013929569 6456061865682634510447177)
          ·
            refine ⟨4842046399261975882835383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456061865682634510447177 4842046399261975882835383)
            ·
              refine ⟨7263069598892963824253075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842046399261975882835383 7263069598892963824253075)
              ·
                refine ⟨10894604398339445736379613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263069598892963824253075 10894604398339445736379613)
                ·
                  refine ⟨4085476649377292151142355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10894604398339445736379613 4085476649377292151142355)
                  ·
                    refine ⟨6128214974065938226713533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4085476649377292151142355 6128214974065938226713533)
                    ·
                      refine ⟨2298080615274726835017575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6128214974065938226713533 2298080615274726835017575)
                      ·
                        rfl

theorem cell23_4475496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4475496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475496 prefixEnd_4475496 := by exact prefixLift 4475496
  have htrace : WordTrace (prefixWord ++ tailWord_4475496) baseStart_4475496 baseEnd_4475496 := by
    simpa [prefixWord, tailWord_4475496, baseEnd_4475496] using wordTrace_append hprefix tailTrace_4475496
  have hstable : (prefixWord ++ tailWord_4475496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475496).length < 2 ^ (prefixWord ++ tailWord_4475496).sum := by decide
  have hdescent : baseEnd_4475496 < baseStart_4475496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475535 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3]
def baseStart_4475535 : Nat := 118140960795 + 4475535 * 2 ^ 59
def prefixEnd_4475535 : Nat := 4983230072969 + 3 ^ 40 * 4475535 * 2
def baseEnd_4475535 : Nat := 2298100641020252182429895

theorem tailTrace_4475535 : CollatzResearch.WordTrace tailWord_4475535 prefixEnd_4475535 2298100641020252182429895 := by
  unfold tailWord_4475535
  simp only [CollatzResearch.WordTrace]
  refine ⟨163236171840908530369260059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108824114560605686912840039 163236171840908530369260059)
  ·
    refine ⟨244854257761362795553890089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163236171840908530369260059 244854257761362795553890089)
    ·
      refine ⟨183640693321022096665417567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244854257761362795553890089 183640693321022096665417567)
      ·
        refine ⟨275461039981533144998126351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183640693321022096665417567 275461039981533144998126351)
        ·
          refine ⟨413191559972299717497189527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275461039981533144998126351 413191559972299717497189527)
          ·
            refine ⟨619787339958449576245784291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413191559972299717497189527 619787339958449576245784291)
            ·
              refine ⟨929681009937674364368676437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 619787339958449576245784291 929681009937674364368676437)
              ·
                refine ⟨10894699335207121457445427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 929681009937674364368676437 10894699335207121457445427)
                ·
                  refine ⟨16342049002810682186168141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10894699335207121457445427 16342049002810682186168141)
                  ·
                    refine ⟨6128268376054005819813053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16342049002810682186168141 6128268376054005819813053)
                    ·
                      refine ⟨2298100641020252182429895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6128268376054005819813053 2298100641020252182429895)
                      ·
                        rfl

theorem cell23_4475535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 3, 3].length) (baseStart_4475535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475535 prefixEnd_4475535 := by exact prefixLift 4475535
  have htrace : WordTrace (prefixWord ++ tailWord_4475535) baseStart_4475535 baseEnd_4475535 := by
    simpa [prefixWord, tailWord_4475535, baseEnd_4475535] using wordTrace_append hprefix tailTrace_4475535
  have hstable : (prefixWord ++ tailWord_4475535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475535).length < 2 ^ (prefixWord ++ tailWord_4475535).sum := by decide
  have hdescent : baseEnd_4475535 < baseStart_4475535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475546 : List Nat := [3, 1, 1, 6, 1, 1, 2, 2, 2, 4]
def baseStart_4475546 : Nat := 118140960795 + 4475546 * 2 ^ 59
def prefixEnd_4475546 : Nat := 4983230072969 + 3 ^ 40 * 4475546 * 2
def baseEnd_4475546 : Nat := 766035429769150546464115

theorem tailTrace_4475546 : CollatzResearch.WordTrace tailWord_4475546 prefixEnd_4475546 766035429769150546464115 := by
  unfold tailWord_4475546
  simp only [CollatzResearch.WordTrace]
  refine ⟨40809143260967169811977623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108824382029245786165273661 40809143260967169811977623)
  ·
    refine ⟨61213714891450754717966435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40809143260967169811977623 61213714891450754717966435)
    ·
      refine ⟨91820572337176132076949653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61213714891450754717966435 91820572337176132076949653)
      ·
        refine ⟨4304089328305131191107015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 91820572337176132076949653 4304089328305131191107015)
        ·
          refine ⟨6456133992457696786660523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304089328305131191107015 6456133992457696786660523)
          ·
            refine ⟨9684200988686545179990785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6456133992457696786660523 9684200988686545179990785)
            ·
              refine ⟨7263150741514908884993089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9684200988686545179990785 7263150741514908884993089)
              ·
                refine ⟨5447363056136181663744817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7263150741514908884993089 5447363056136181663744817)
                ·
                  refine ⟨4085522292102136247808613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5447363056136181663744817 4085522292102136247808613)
                  ·
                    refine ⟨766035429769150546464115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085522292102136247808613 766035429769150546464115)
                    ·
                      rfl

theorem cell23_4475546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_4475546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475546 prefixEnd_4475546 := by exact prefixLift 4475546
  have htrace : WordTrace (prefixWord ++ tailWord_4475546) baseStart_4475546 baseEnd_4475546 := by
    simpa [prefixWord, tailWord_4475546, baseEnd_4475546] using wordTrace_append hprefix tailTrace_4475546
  have hstable : (prefixWord ++ tailWord_4475546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475546).length < 2 ^ (prefixWord ++ tailWord_4475546).sum := by decide
  have hdescent : baseEnd_4475546 < baseStart_4475546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475553 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 1, 2, 2]
def baseStart_4475553 : Nat := 118140960795 + 4475553 * 2 ^ 59
def prefixEnd_4475553 : Nat := 4983230072969 + 3 ^ 40 * 4475553 * 2
def baseEnd_4475553 : Nat := 2298109883672033112004813

theorem tailTrace_4475553 : CollatzResearch.WordTrace tailWord_4475553 prefixEnd_4475553 2298109883672033112004813 := by
  unfold tailWord_4475553
  simp only [CollatzResearch.WordTrace]
  refine ⟨163236828354843319443415313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108824552236562212962276875 163236828354843319443415313)
  ·
    refine ⟨122427621266132489582561485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163236828354843319443415313 122427621266132489582561485)
    ·
      refine ⟨45910357974799683593460557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122427621266132489582561485 45910357974799683593460557)
      ·
        refine ⟨17216384240549881347547709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45910357974799683593460557 17216384240549881347547709)
        ·
          refine ⟨6456144090206205505330391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17216384240549881347547709 6456144090206205505330391)
          ·
            refine ⟨9684216135309308257995587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6456144090206205505330391 9684216135309308257995587)
            ·
              refine ⟨14526324202963962386993381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9684216135309308257995587 14526324202963962386993381)
              ·
                refine ⟨2723685788055742947561259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14526324202963962386993381 2723685788055742947561259)
                ·
                  refine ⟨4085528682083614421341889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723685788055742947561259 4085528682083614421341889)
                  ·
                    refine ⟨3064146511562710816006417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085528682083614421341889 3064146511562710816006417)
                    ·
                      refine ⟨2298109883672033112004813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064146511562710816006417 2298109883672033112004813)
                      ·
                        rfl

theorem cell23_4475553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_4475553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475553 prefixEnd_4475553 := by exact prefixLift 4475553
  have htrace : WordTrace (prefixWord ++ tailWord_4475553) baseStart_4475553 baseEnd_4475553 := by
    simpa [prefixWord, tailWord_4475553, baseEnd_4475553] using wordTrace_append hprefix tailTrace_4475553
  have hstable : (prefixWord ++ tailWord_4475553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475553).length < 2 ^ (prefixWord ++ tailWord_4475553).sum := by decide
  have hdescent : baseEnd_4475553 < baseStart_4475553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475559 : List Nat := [1, 1, 6, 3, 1, 2, 1, 8]
def baseStart_4475559 : Nat := 118140960795 + 4475559 * 2 ^ 59
def prefixEnd_4475559 : Nat := 4983230072969 + 3 ^ 40 * 4475559 * 2
def baseEnd_4475559 : Nat := 85115294983554077352955

theorem tailTrace_4475559 : CollatzResearch.WordTrace tailWord_4475559 prefixEnd_4475559 85115294983554077352955 := by
  unfold tailWord_4475559
  simp only [CollatzResearch.WordTrace]
  refine ⟨163237047192821582468133731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108824698128547721645422487 163237047192821582468133731)
  ·
    refine ⟨244855570789232373702200597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163237047192821582468133731 244855570789232373702200597)
    ·
      refine ⟨11477604880745267517290653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 244855570789232373702200597 11477604880745267517290653)
      ·
        refine ⟨4304101830279475318983995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11477604880745267517290653 4304101830279475318983995)
        ·
          refine ⟨6456152745419212978475993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304101830279475318983995 6456152745419212978475993)
          ·
            refine ⟨4842114559064409733856995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456152745419212978475993 4842114559064409733856995)
            ·
              refine ⟨7263171838596614600785493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842114559064409733856995 7263171838596614600785493)
              ·
                refine ⟨85115294983554077352955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7263171838596614600785493 85115294983554077352955)
                ·
                  rfl

theorem cell23_4475559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 8].length) (baseStart_4475559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475559 prefixEnd_4475559 := by exact prefixLift 4475559
  have htrace : WordTrace (prefixWord ++ tailWord_4475559) baseStart_4475559 baseEnd_4475559 := by
    simpa [prefixWord, tailWord_4475559, baseEnd_4475559] using wordTrace_append hprefix tailTrace_4475559
  have hstable : (prefixWord ++ tailWord_4475559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475559).length < 2 ^ (prefixWord ++ tailWord_4475559).sum := by decide
  have hdescent : baseEnd_4475559 < baseStart_4475559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475596 : List Nat := [2, 2, 1, 5, 1, 2, 1, 3, 1, 3, 2]
def baseStart_4475596 : Nat := 118140960795 + 4475596 * 2 ^ 59
def prefixEnd_4475596 : Nat := 4983230072969 + 3 ^ 40 * 4475596 * 2
def baseEnd_4475596 : Nat := 2298131963340176443767115

theorem tailTrace_4475596 : CollatzResearch.WordTrace tailWord_4475596 prefixEnd_4475596 2298131963340176443767115 := by
  unfold tailWord_4475596
  simp only [CollatzResearch.WordTrace]
  refine ⟨81619198346843768893615321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108825597795791691858153761 81619198346843768893615321)
  ·
    refine ⟨61214398760132826670211491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81619198346843768893615321 61214398760132826670211491)
    ·
      refine ⟨91821598140199240005317237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61214398760132826670211491 91821598140199240005317237)
      ·
        refine ⟨8608274825643678750498491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 91821598140199240005317237 8608274825643678750498491)
        ·
          refine ⟨12912412238465518125747737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608274825643678750498491 12912412238465518125747737)
          ·
            refine ⟨9684309178849138594310803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12912412238465518125747737 9684309178849138594310803)
            ·
              refine ⟨14526463768273707891466205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9684309178849138594310803 14526463768273707891466205)
              ·
                refine ⟨5447423913102640459299827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14526463768273707891466205 5447423913102640459299827)
                ·
                  refine ⟨8171135869653960688949741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447423913102640459299827 8171135869653960688949741)
                  ·
                    refine ⟨3064175951120235258356153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8171135869653960688949741 3064175951120235258356153)
                    ·
                      refine ⟨2298131963340176443767115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064175951120235258356153 2298131963340176443767115)
                      ·
                        rfl

theorem cell23_4475596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_4475596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475596 prefixEnd_4475596 := by exact prefixLift 4475596
  have htrace : WordTrace (prefixWord ++ tailWord_4475596) baseStart_4475596 baseEnd_4475596 := by
    simpa [prefixWord, tailWord_4475596, baseEnd_4475596] using wordTrace_append hprefix tailTrace_4475596
  have hstable : (prefixWord ++ tailWord_4475596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475596).length < 2 ^ (prefixWord ++ tailWord_4475596).sum := by decide
  have hdescent : baseEnd_4475596 < baseStart_4475596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475609 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 4, 2, 2]
def baseStart_4475609 : Nat := 118140960795 + 4475609 * 2 ^ 59
def prefixEnd_4475609 : Nat := 4983230072969 + 3 ^ 40 * 4475609 * 2
def baseEnd_4475609 : Nat := 2298138638588684892904555

theorem tailTrace_4475609 : CollatzResearch.WordTrace tailWord_4475609 prefixEnd_4475609 2298138638588684892904555 := by
  unfold tailWord_4475609
  simp only [CollatzResearch.WordTrace]
  refine ⟨163238870842640441007453881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108825913895093627338302587 163238870842640441007453881)
  ·
    refine ⟨122429153131980330755590411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163238870842640441007453881 122429153131980330755590411)
    ·
      refine ⟨183643729697970496133385617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122429153131980330755590411 183643729697970496133385617)
      ·
        refine ⟨137732797273477872100039213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183643729697970496133385617 137732797273477872100039213)
        ·
          refine ⟨51649798977554202037514705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 137732797273477872100039213 51649798977554202037514705)
          ·
            refine ⟨38737349233165651528136029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51649798977554202037514705 38737349233165651528136029)
            ·
              refine ⟨14526505962437119323051011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38737349233165651528136029 14526505962437119323051011)
              ·
                refine ⟨21789758943655678984576517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14526505962437119323051011 21789758943655678984576517)
                ·
                  refine ⟨4085579801935439809608097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21789758943655678984576517 4085579801935439809608097)
                  ·
                    refine ⟨3064184851451579857206073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085579801935439809608097 3064184851451579857206073)
                    ·
                      refine ⟨2298138638588684892904555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064184851451579857206073 2298138638588684892904555)
                      ·
                        rfl

theorem cell23_4475609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_4475609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475609 prefixEnd_4475609 := by exact prefixLift 4475609
  have htrace : WordTrace (prefixWord ++ tailWord_4475609) baseStart_4475609 baseEnd_4475609 := by
    simpa [prefixWord, tailWord_4475609, baseEnd_4475609] using wordTrace_append hprefix tailTrace_4475609
  have hstable : (prefixWord ++ tailWord_4475609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475609).length < 2 ^ (prefixWord ++ tailWord_4475609).sum := by decide
  have hdescent : baseEnd_4475609 < baseStart_4475609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475615 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 7]
def baseStart_4475615 : Nat := 118140960795 + 4475615 * 2 ^ 59
def prefixEnd_4475615 : Nat := 4983230072969 + 3 ^ 40 * 4475615 * 2
def baseEnd_4475615 : Nat := 255349079941401318825503

theorem tailTrace_4475615 : CollatzResearch.WordTrace tailWord_4475615 prefixEnd_4475615 255349079941401318825503 := by
  unfold tailWord_4475615
  simp only [CollatzResearch.WordTrace]
  refine ⟨163239089680618704032172299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108826059787079136021448199 163239089680618704032172299)
  ·
    refine ⟨244858634520928056048258449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163239089680618704032172299 244858634520928056048258449)
    ·
      refine ⟨183643975890696042036193837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244858634520928056048258449 183643975890696042036193837)
      ·
        refine ⟨68866490959011015763572689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183643975890696042036193837 68866490959011015763572689)
        ·
          refine ⟨51649868219258261822679517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68866490959011015763572689 51649868219258261822679517)
          ·
            refine ⟨19368700582221848183504819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51649868219258261822679517 19368700582221848183504819)
            ·
              refine ⟨29053050873332772275257229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19368700582221848183504819 29053050873332772275257229)
              ·
                refine ⟨10894894077499789603221461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29053050873332772275257229 10894894077499789603221461)
                ·
                  refine ⟨255349079941401318825503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10894894077499789603221461 255349079941401318825503)
                  ·
                    rfl

theorem cell23_4475615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 7].length) (baseStart_4475615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475615 prefixEnd_4475615 := by exact prefixLift 4475615
  have htrace : WordTrace (prefixWord ++ tailWord_4475615) baseStart_4475615 baseEnd_4475615 := by
    simpa [prefixWord, tailWord_4475615, baseEnd_4475615] using wordTrace_append hprefix tailTrace_4475615
  have hstable : (prefixWord ++ tailWord_4475615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475615).length < 2 ^ (prefixWord ++ tailWord_4475615).sum := by decide
  have hdescent : baseEnd_4475615 < baseStart_4475615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475645 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 7]
def baseStart_4475645 : Nat := 118140960795 + 4475645 * 2 ^ 59
def prefixEnd_4475645 : Nat := 4983230072969 + 3 ^ 40 * 4475645 * 2
def baseEnd_4475645 : Nat := 766052374630748917351463

theorem tailTrace_4475645 : CollatzResearch.WordTrace tailWord_4475645 prefixEnd_4475645 766052374630748917351463 := by
  unfold tailWord_4475645
  simp only [CollatzResearch.WordTrace]
  refine ⟨163240183870510019155764389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108826789247006679437176259 163240183870510019155764389)
  ·
    refine ⟨30607534475720628591705823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163240183870510019155764389 30607534475720628591705823)
    ·
      refine ⟨45911301713580942887558735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30607534475720628591705823 45911301713580942887558735)
      ·
        refine ⟨68866952570371414331338103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45911301713580942887558735 68866952570371414331338103)
        ·
          refine ⟨103300428855557121497007155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68866952570371414331338103 103300428855557121497007155)
          ·
            refine ⟨154950643283335682245510733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103300428855557121497007155 154950643283335682245510733)
            ·
              refine ⟨58106491231250880842066525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 154950643283335682245510733 58106491231250880842066525)
              ·
                refine ⟨21789934211719080315774947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58106491231250880842066525 21789934211719080315774947)
                ·
                  refine ⟨32684901317578620473662421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21789934211719080315774947 32684901317578620473662421)
                  ·
                    refine ⟨766052374630748917351463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32684901317578620473662421 766052374630748917351463)
                    ·
                      rfl

theorem cell23_4475645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_4475645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475645 prefixEnd_4475645 := by exact prefixLift 4475645
  have htrace : WordTrace (prefixWord ++ tailWord_4475645) baseStart_4475645 baseEnd_4475645 := by
    simpa [prefixWord, tailWord_4475645, baseEnd_4475645] using wordTrace_append hprefix tailTrace_4475645
  have hstable : (prefixWord ++ tailWord_4475645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475645).length < 2 ^ (prefixWord ++ tailWord_4475645).sum := by decide
  have hdescent : baseEnd_4475645 < baseStart_4475645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475666 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 7]
def baseStart_4475666 : Nat := 118140960795 + 4475666 * 2 ^ 59
def prefixEnd_4475666 : Nat := 4983230072969 + 3 ^ 40 * 4475666 * 2
def baseEnd_4475666 : Nat := 255351989665110129987977

theorem tailTrace_4475666 : CollatzResearch.WordTrace tailWord_4475666 prefixEnd_4475666 255351989665110129987977 := by
  unfold tailWord_4475666
  simp only [CollatzResearch.WordTrace]
  refine ⟨40810237450858484935569713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108827299868955959828185901 40810237450858484935569713)
  ·
    refine ⟨30607678088143863701677285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40810237450858484935569713 30607678088143863701677285)
    ·
      refine ⟨5738939641526974444064491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30607678088143863701677285 5738939641526974444064491)
      ·
        refine ⟨8608409462290461666096737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5738939641526974444064491 8608409462290461666096737)
        ·
          refine ⟨6456307096717846249572553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8608409462290461666096737 6456307096717846249572553)
          ·
            refine ⟨4842230322538384687179415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456307096717846249572553 4842230322538384687179415)
            ·
              refine ⟨7263345483807577030769123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842230322538384687179415 7263345483807577030769123)
              ·
                refine ⟨10895018225711365546153685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263345483807577030769123 10895018225711365546153685)
                ·
                  refine ⟨255351989665110129987977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10895018225711365546153685 255351989665110129987977)
                  ·
                    rfl

theorem cell23_4475666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_4475666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475666 prefixEnd_4475666 := by exact prefixLift 4475666
  have htrace : WordTrace (prefixWord ++ tailWord_4475666) baseStart_4475666 baseEnd_4475666 := by
    simpa [prefixWord, tailWord_4475666, baseEnd_4475666] using wordTrace_append hprefix tailTrace_4475666
  have hstable : (prefixWord ++ tailWord_4475666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475666).length < 2 ^ (prefixWord ++ tailWord_4475666).sum := by decide
  have hdescent : baseEnd_4475666 < baseStart_4475666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475677 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_4475677 : Nat := 118140960795 + 4475677 * 2 ^ 59
def prefixEnd_4475677 : Nat := 4983230072969 + 3 ^ 40 * 4475677 * 2
def baseEnd_4475677 : Nat := 2298173555273190626854243

theorem tailTrace_4475677 : CollatzResearch.WordTrace tailWord_4475677 prefixEnd_4475677 2298173555273190626854243 := by
  unfold tailWord_4475677
  simp only [CollatzResearch.WordTrace]
  refine ⟨163241351006394088620929285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108827567337596059080619523 163241351006394088620929285)
  ·
    refine ⟨30607753313698891616424241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163241351006394088620929285 30607753313698891616424241)
    ·
      refine ⟨22955814985274168712318181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30607753313698891616424241 22955814985274168712318181)
      ·
        refine ⟨4304215309738906633559659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22955814985274168712318181 4304215309738906633559659)
        ·
          refine ⟨6456322964608359950339489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304215309738906633559659 6456322964608359950339489)
          ·
            refine ⟨4842242223456269962754617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6456322964608359950339489 4842242223456269962754617)
            ·
              refine ⟨3631681667592202472065963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4842242223456269962754617 3631681667592202472065963)
              ·
                refine ⟨5447522501388303708098945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3631681667592202472065963 5447522501388303708098945)
                ·
                  refine ⟨4085641876041227781074209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5447522501388303708098945 4085641876041227781074209)
                  ·
                    refine ⟨3064231407030920835805657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085641876041227781074209 3064231407030920835805657)
                    ·
                      refine ⟨2298173555273190626854243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064231407030920835805657 2298173555273190626854243)
                      ·
                        rfl

theorem cell23_4475677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_4475677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475677 prefixEnd_4475677 := by exact prefixLift 4475677
  have htrace : WordTrace (prefixWord ++ tailWord_4475677) baseStart_4475677 baseEnd_4475677 := by
    simpa [prefixWord, tailWord_4475677, baseEnd_4475677] using wordTrace_append hprefix tailTrace_4475677
  have hstable : (prefixWord ++ tailWord_4475677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475677).length < 2 ^ (prefixWord ++ tailWord_4475677).sum := by decide
  have hdescent : baseEnd_4475677 < baseStart_4475677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475692 : List Nat := [2, 2, 1, 1, 1, 4, 2, 1, 5, 4]
def baseStart_4475692 : Nat := 118140960795 + 4475692 * 2 ^ 59
def prefixEnd_4475692 : Nat := 4983230072969 + 3 ^ 40 * 4475692 * 2
def baseEnd_4475692 : Nat := 766060419161002689388891

theorem tailTrace_4475692 : CollatzResearch.WordTrace tailWord_4475692 prefixEnd_4475692 766060419161002689388891 := by
  unfold tailWord_4475692
  simp only [CollatzResearch.WordTrace]
  refine ⟨81620949050669873091362665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108827932067559830788483553 81620949050669873091362665)
  ·
    refine ⟨61215711788002404818521999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 81620949050669873091362665 61215711788002404818521999)
    ·
      refine ⟨91823567682003607227782999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61215711788002404818521999 91823567682003607227782999)
      ·
        refine ⟨137735351523005410841674499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91823567682003607227782999 137735351523005410841674499)
        ·
          refine ⟨206603027284508116262511749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137735351523005410841674499 206603027284508116262511749)
          ·
            refine ⟨38738067615845271799220953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 206603027284508116262511749 38738067615845271799220953)
            ·
              refine ⟨29053550711883953849415715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38738067615845271799220953 29053550711883953849415715)
              ·
                refine ⟨43580326067825930774123573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29053550711883953849415715 43580326067825930774123573)
                ·
                  refine ⟨4085655568858681010074085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43580326067825930774123573 4085655568858681010074085)
                  ·
                    refine ⟨766060419161002689388891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085655568858681010074085 766060419161002689388891)
                    ·
                      rfl

theorem cell23_4475692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 4].length) (baseStart_4475692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475692 prefixEnd_4475692 := by exact prefixLift 4475692
  have htrace : WordTrace (prefixWord ++ tailWord_4475692) baseStart_4475692 baseEnd_4475692 := by
    simpa [prefixWord, tailWord_4475692, baseEnd_4475692] using wordTrace_append hprefix tailTrace_4475692
  have hstable : (prefixWord ++ tailWord_4475692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475692).length < 2 ^ (prefixWord ++ tailWord_4475692).sum := by decide
  have hdescent : baseEnd_4475692 < baseStart_4475692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475699 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4]
def baseStart_4475699 : Nat := 118140960795 + 4475699 * 2 ^ 59
def prefixEnd_4475699 : Nat := 4983230072969 + 3 ^ 40 * 4475699 * 2
def baseEnd_4475699 : Nat := 2298184851847589540779141

theorem tailTrace_4475699 : CollatzResearch.WordTrace tailWord_4475699 prefixEnd_4475699 2298184851847589540779141 := by
  unfold tailWord_4475699
  simp only [CollatzResearch.WordTrace]
  refine ⟨163242153412314386378230151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108828102274876257585486767 163242153412314386378230151)
  ·
    refine ⟨244863230118471579567345227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163242153412314386378230151 244863230118471579567345227)
    ·
      refine ⟨367294845177707369351017841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244863230118471579567345227 367294845177707369351017841)
      ·
        refine ⟨275471133883280527013263381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367294845177707369351017841 275471133883280527013263381)
        ·
          refine ⟨12912709400778774703746721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 275471133883280527013263381 12912709400778774703746721)
          ·
            refine ⟨9684532050584081027810041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12912709400778774703746721 9684532050584081027810041)
            ·
              refine ⟨7263399037938060770857531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9684532050584081027810041 7263399037938060770857531)
              ·
                refine ⟨10895098556907091156286297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263399037938060770857531 10895098556907091156286297)
                ·
                  refine ⟨8171323917680318367214723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10895098556907091156286297 8171323917680318367214723)
                  ·
                    refine ⟨12256985876520477550822085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8171323917680318367214723 12256985876520477550822085)
                    ·
                      refine ⟨2298184851847589540779141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12256985876520477550822085 2298184851847589540779141)
                      ·
                        rfl

theorem cell23_4475699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 1, 4].length) (baseStart_4475699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475699 prefixEnd_4475699 := by exact prefixLift 4475699
  have htrace : WordTrace (prefixWord ++ tailWord_4475699) baseStart_4475699 baseEnd_4475699 := by
    simpa [prefixWord, tailWord_4475699, baseEnd_4475699] using wordTrace_append hprefix tailTrace_4475699
  have hstable : (prefixWord ++ tailWord_4475699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475699).length < 2 ^ (prefixWord ++ tailWord_4475699).sum := by decide
  have hdescent : baseEnd_4475699 < baseStart_4475699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475749 : List Nat := [1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_4475749 : Nat := 118140960795 + 4475749 * 2 ^ 59
def prefixEnd_4475749 : Nat := 4983230072969 + 3 ^ 40 * 4475749 * 2
def baseEnd_4475749 : Nat := 2298210525880314345153911

theorem tailTrace_4475749 : CollatzResearch.WordTrace tailWord_4475749 prefixEnd_4475749 2298210525880314345153911 := by
  unfold tailWord_4475749
  simp only [CollatzResearch.WordTrace]
  refine ⟨163243977062133244917550301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108829318041422163278366867 163243977062133244917550301)
  ·
    refine ⟨61216491398299966844081363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163243977062133244917550301 61216491398299966844081363)
    ·
      refine ⟨91824737097449950266122045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61216491398299966844081363 91824737097449950266122045)
      ·
        refine ⟨34434276411543731349795767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 91824737097449950266122045 34434276411543731349795767)
        ·
          refine ⟨51651414617315597024693651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34434276411543731349795767 51651414617315597024693651)
          ·
            refine ⟨77477121925973395537040477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51651414617315597024693651 77477121925973395537040477)
            ·
              refine ⟨29053920722240023326390179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 77477121925973395537040477 29053920722240023326390179)
              ·
                refine ⟨43580881083360034989585269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29053920722240023326390179 43580881083360034989585269)
                ·
                  refine ⟨4085707601565003280273619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43580881083360034989585269 4085707601565003280273619)
                  ·
                    refine ⟨6128561402347504920410429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4085707601565003280273619 6128561402347504920410429)
                    ·
                      refine ⟨2298210525880314345153911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6128561402347504920410429 2298210525880314345153911)
                      ·
                        rfl

theorem cell23_4475749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_4475749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475749 prefixEnd_4475749 := by exact prefixLift 4475749
  have htrace : WordTrace (prefixWord ++ tailWord_4475749) baseStart_4475749 baseEnd_4475749 := by
    simpa [prefixWord, tailWord_4475749, baseEnd_4475749] using wordTrace_append hprefix tailTrace_4475749
  have hstable : (prefixWord ++ tailWord_4475749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475749).length < 2 ^ (prefixWord ++ tailWord_4475749).sum := by decide
  have hdescent : baseEnd_4475749 < baseStart_4475749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475769 : List Nat := [1, 2, 1, 3, 2, 4, 1, 3, 1, 5]
def baseStart_4475769 : Nat := 118140960795 + 4475769 * 2 ^ 59
def prefixEnd_4475769 : Nat := 4983230072969 + 3 ^ 40 * 4475769 * 2
def baseEnd_4475769 : Nat := 766073598497801422301273

theorem tailTrace_4475769 : CollatzResearch.WordTrace tailWord_4475769 prefixEnd_4475769 766073598497801422301273 := by
  unfold tailWord_4475769
  simp only [CollatzResearch.WordTrace]
  refine ⟨163244706522060788333278361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108829804348040525555518907 163244706522060788333278361)
  ·
    refine ⟨122433529891545591249958771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163244706522060788333278361 122433529891545591249958771)
    ·
      refine ⟨183650294837318386874938157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122433529891545591249958771 183650294837318386874938157)
      ·
        refine ⟨68868860563994395078101809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183650294837318386874938157 68868860563994395078101809)
        ·
          refine ⟨51651645422995796308576357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68868860563994395078101809 51651645422995796308576357)
          ·
            refine ⟨9684683516811711807858067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 51651645422995796308576357 9684683516811711807858067)
            ·
              refine ⟨14527025275217567711787101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9684683516811711807858067 14527025275217567711787101)
              ·
                refine ⟨5447634478206587891920163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14527025275217567711787101 5447634478206587891920163)
                ·
                  refine ⟨8171451717309881837880245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5447634478206587891920163 8171451717309881837880245)
                  ·
                    refine ⟨766073598497801422301273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8171451717309881837880245 766073598497801422301273)
                    ·
                      rfl

theorem cell23_4475769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 5].length) (baseStart_4475769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475769 prefixEnd_4475769 := by exact prefixLift 4475769
  have htrace : WordTrace (prefixWord ++ tailWord_4475769) baseStart_4475769 baseEnd_4475769 := by
    simpa [prefixWord, tailWord_4475769, baseEnd_4475769] using wordTrace_append hprefix tailTrace_4475769
  have hstable : (prefixWord ++ tailWord_4475769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475769).length < 2 ^ (prefixWord ++ tailWord_4475769).sum := by decide
  have hdescent : baseEnd_4475769 < baseStart_4475769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475783 : List Nat := [1, 1, 4, 2, 3, 1, 2, 4, 1, 1, 3]
def baseStart_4475783 : Nat := 118140960795 + 4475783 * 2 ^ 59
def prefixEnd_4475783 : Nat := 4983230072969 + 3 ^ 40 * 4475783 * 2
def baseEnd_4475783 : Nat := 2298227984222567212128755

theorem tailTrace_4475783 : CollatzResearch.WordTrace tailWord_4475783 prefixEnd_4475783 2298227984222567212128755 := by
  unfold tailWord_4475783
  simp only [CollatzResearch.WordTrace]
  refine ⟨163245217144010068724288003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108830144762673379149525335 163245217144010068724288003)
  ·
    refine ⟨244867825716015103086432005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163245217144010068724288003 244867825716015103086432005)
    ·
      refine ⟨45912717321752831828706001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 244867825716015103086432005 45912717321752831828706001)
      ·
        refine ⟨34434537991314623871529501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45912717321752831828706001 34434537991314623871529501)
        ·
          refine ⟨12912951746742983951823563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34434537991314623871529501 12912951746742983951823563)
          ·
            refine ⟨19369427620114475927735345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12912951746742983951823563 19369427620114475927735345)
            ·
              refine ⟨14527070715085856945801509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19369427620114475927735345 14527070715085856945801509)
              ·
                refine ⟨2723825759078598177337783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14527070715085856945801509 2723825759078598177337783)
                ·
                  refine ⟨4085738638617897266006675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723825759078598177337783 4085738638617897266006675)
                  ·
                    refine ⟨6128607957926845899010013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4085738638617897266006675 6128607957926845899010013)
                    ·
                      refine ⟨2298227984222567212128755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6128607957926845899010013 2298227984222567212128755)
                      ·
                        rfl

theorem cell23_4475783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_4475783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475783 prefixEnd_4475783 := by exact prefixLift 4475783
  have htrace : WordTrace (prefixWord ++ tailWord_4475783) baseStart_4475783 baseEnd_4475783 := by
    simpa [prefixWord, tailWord_4475783, baseEnd_4475783] using wordTrace_append hprefix tailTrace_4475783
  have hstable : (prefixWord ++ tailWord_4475783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475783).length < 2 ^ (prefixWord ++ tailWord_4475783).sum := by decide
  have hdescent : baseEnd_4475783 < baseStart_4475783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475812 : List Nat := [2, 3, 1, 2, 1, 2, 3, 9]
def baseStart_4475812 : Nat := 118140960795 + 4475812 * 2 ^ 59
def prefixEnd_4475812 : Nat := 4983230072969 + 3 ^ 40 * 4475812 * 2
def baseEnd_4475812 : Nat := 85120106487464725876523

theorem tailTrace_4475812 : CollatzResearch.WordTrace tailWord_4475812 prefixEnd_4475812 85120106487464725876523 := by
  unfold tailWord_4475812
  simp only [CollatzResearch.WordTrace]
  refine ⟨81623137430452503338546845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108830849907270004451395793 81623137430452503338546845)
  ·
    refine ⟨30608676536419688751955067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 81623137430452503338546845 30608676536419688751955067)
    ·
      refine ⟨45913014804629533127932601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30608676536419688751955067 45913014804629533127932601)
      ·
        refine ⟨34434761103472149845949451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45913014804629533127932601 34434761103472149845949451)
        ·
          refine ⟨51652141655208224768924177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34434761103472149845949451 51652141655208224768924177)
          ·
            refine ⟨38739106241406168576693133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51652141655208224768924177 38739106241406168576693133)
            ·
              refine ⟨14527164840527313216259925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38739106241406168576693133 14527164840527313216259925)
              ·
                refine ⟨85120106487464725876523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14527164840527313216259925 85120106487464725876523)
                ·
                  rfl

theorem cell23_4475812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 9].length) (baseStart_4475812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475812 prefixEnd_4475812 := by exact prefixLift 4475812
  have htrace : WordTrace (prefixWord ++ tailWord_4475812) baseStart_4475812 baseEnd_4475812 := by
    simpa [prefixWord, tailWord_4475812, baseEnd_4475812] using wordTrace_append hprefix tailTrace_4475812
  have hstable : (prefixWord ++ tailWord_4475812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475812).length < 2 ^ (prefixWord ++ tailWord_4475812).sum := by decide
  have hdescent : baseEnd_4475812 < baseStart_4475812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475823 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 1, 2, 2]
def baseStart_4475823 : Nat := 118140960795 + 4475823 * 2 ^ 59
def prefixEnd_4475823 : Nat := 4983230072969 + 3 ^ 40 * 4475823 * 2
def baseEnd_4475823 : Nat := 2298248523448747055628571

theorem tailTrace_4475823 : CollatzResearch.WordTrace tailWord_4475823 prefixEnd_4475823 2298248523448747055628571 := by
  unfold tailWord_4475823
  simp only [CollatzResearch.WordTrace]
  refine ⟨163246676063865155555744123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108831117375910103703829415 163246676063865155555744123)
  ·
    refine ⟨244870014095797733333616185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163246676063865155555744123 244870014095797733333616185)
    ·
      refine ⟨183652510571848300000212139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244870014095797733333616185 183652510571848300000212139)
      ·
        refine ⟨275478765857772450000318209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183652510571848300000212139 275478765857772450000318209)
        ·
          refine ⟨206609074393329337500238657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 275478765857772450000318209 206609074393329337500238657)
          ·
            refine ⟨154956805794997003125178993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 206609074393329337500238657 154956805794997003125178993)
            ·
              refine ⟨116217604346247752343884245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 154956805794997003125178993 116217604346247752343884245)
              ·
                refine ⟨2723850101865181695559787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 116217604346247752343884245 2723850101865181695559787)
                ·
                  refine ⟨4085775152797772543339681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2723850101865181695559787 4085775152797772543339681)
                  ·
                    refine ⟨3064331364598329407504761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4085775152797772543339681 3064331364598329407504761)
                    ·
                      refine ⟨2298248523448747055628571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064331364598329407504761 2298248523448747055628571)
                      ·
                        rfl

theorem cell23_4475823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 1, 2, 2].length) (baseStart_4475823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475823 prefixEnd_4475823 := by exact prefixLift 4475823
  have htrace : WordTrace (prefixWord ++ tailWord_4475823) baseStart_4475823 baseEnd_4475823 := by
    simpa [prefixWord, tailWord_4475823, baseEnd_4475823] using wordTrace_append hprefix tailTrace_4475823
  have hstable : (prefixWord ++ tailWord_4475823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475823).length < 2 ^ (prefixWord ++ tailWord_4475823).sum := by decide
  have hdescent : baseEnd_4475823 < baseStart_4475823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475872 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 6, 6]
def baseStart_4475872 : Nat := 118140960795 + 4475872 * 2 ^ 59
def prefixEnd_4475872 : Nat := 4983230072969 + 3 ^ 40 * 4475872 * 2
def baseEnd_4475872 : Nat := 766091228000272454638615

theorem tailTrace_4475872 : CollatzResearch.WordTrace tailWord_4475872 prefixEnd_4475872 766091228000272454638615 := by
  unfold tailWord_4475872
  simp only [CollatzResearch.WordTrace]
  refine ⟨81624231620343818462138935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108832308827125091282851913 81624231620343818462138935)
  ·
    refine ⟨122436347430515727693208403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81624231620343818462138935 122436347430515727693208403)
    ·
      refine ⟨183654521145773591539812605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122436347430515727693208403 183654521145773591539812605)
      ·
        refine ⟨68870445429665096827429727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183654521145773591539812605 68870445429665096827429727)
        ·
          refine ⟨103305668144497645241144591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68870445429665096827429727 103305668144497645241144591)
          ·
            refine ⟨154958502216746467861716887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103305668144497645241144591 154958502216746467861716887)
            ·
              refine ⟨232437753325119701792575331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154958502216746467861716887 232437753325119701792575331)
              ·
                refine ⟨348656629987679552688862997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 232437753325119701792575331 348656629987679552688862997)
                ·
                  refine ⟨16343279530672479032290453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 348656629987679552688862997 16343279530672479032290453)
                  ·
                    refine ⟨766091228000272454638615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16343279530672479032290453 766091228000272454638615)
                    ·
                      rfl

theorem cell23_4475872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_4475872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475872 prefixEnd_4475872 := by exact prefixLift 4475872
  have htrace : WordTrace (prefixWord ++ tailWord_4475872) baseStart_4475872 baseEnd_4475872 := by
    simpa [prefixWord, tailWord_4475872, baseEnd_4475872] using wordTrace_append hprefix tailTrace_4475872
  have hstable : (prefixWord ++ tailWord_4475872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475872).length < 2 ^ (prefixWord ++ tailWord_4475872).sum := by decide
  have hdescent : baseEnd_4475872 < baseStart_4475872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475909 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_4475909 : Nat := 118140960795 + 4475909 * 2 ^ 59
def prefixEnd_4475909 : Nat := 4983230072969 + 3 ^ 40 * 4475909 * 2
def baseEnd_4475909 : Nat := 2298292682785033719153175

theorem tailTrace_4475909 : CollatzResearch.WordTrace tailWord_4475909 prefixEnd_4475909 2298292682785033719153175 := by
  unfold tailWord_4475909
  simp only [CollatzResearch.WordTrace]
  refine ⟨163249812741553592243374781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108833208494369061495583187 163249812741553592243374781)
  ·
    refine ⟨61218679778082597091265543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 163249812741553592243374781 61218679778082597091265543)
    ·
      refine ⟨91828019667123895636898315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61218679778082597091265543 91828019667123895636898315)
      ·
        refine ⟨137742029500685843455347473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 91828019667123895636898315 137742029500685843455347473)
        ·
          refine ⟨103306522125514382591510605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 137742029500685843455347473 103306522125514382591510605)
          ·
            refine ⟨38739945797067893471816477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 103306522125514382591510605 38739945797067893471816477)
            ·
              refine ⟨14527479673900460051931179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38739945797067893471816477 14527479673900460051931179)
              ·
                refine ⟨21791219510850690077896769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14527479673900460051931179 21791219510850690077896769)
                ·
                  refine ⟨16343414633138017558422577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21791219510850690077896769 16343414633138017558422577)
                  ·
                    refine ⟨12257560974853513168816933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16343414633138017558422577 12257560974853513168816933)
                    ·
                      refine ⟨2298292682785033719153175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12257560974853513168816933 2298292682785033719153175)
                      ·
                        rfl

theorem cell23_4475909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_4475909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475909 prefixEnd_4475909 := by exact prefixLift 4475909
  have htrace : WordTrace (prefixWord ++ tailWord_4475909) baseStart_4475909 baseEnd_4475909 := by
    simpa [prefixWord, tailWord_4475909, baseEnd_4475909] using wordTrace_append hprefix tailTrace_4475909
  have hstable : (prefixWord ++ tailWord_4475909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475909).length < 2 ^ (prefixWord ++ tailWord_4475909).sum := by decide
  have hdescent : baseEnd_4475909 < baseStart_4475909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475966 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_4475966 : Nat := 118140960795 + 4475966 * 2 ^ 59
def prefixEnd_4475966 : Nat := 4983230072969 + 3 ^ 40 * 4475966 * 2
def baseEnd_4475966 : Nat := 766107317060779998713471

theorem tailTrace_4475966 : CollatzResearch.WordTrace tailWord_4475966 prefixEnd_4475966 766107317060779998713471 := by
  unfold tailWord_4475966
  simp only [CollatzResearch.WordTrace]
  refine ⟨20406486462793386372274969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108834594468231393985466501 20406486462793386372274969)
  ·
    refine ⟨15304864847095039779206227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20406486462793386372274969 15304864847095039779206227)
    ·
      refine ⟨22957297270642559668809341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15304864847095039779206227 22957297270642559668809341)
      ·
        refine ⟨8608986476490959875803503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22957297270642559668809341 8608986476490959875803503)
        ·
          refine ⟨12913479714736439813705255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8608986476490959875803503 12913479714736439813705255)
          ·
            refine ⟨19370219572104659720557883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12913479714736439813705255 19370219572104659720557883)
            ·
              refine ⟨29055329358156989580836825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19370219572104659720557883 29055329358156989580836825)
              ·
                refine ⟨21791497018617742185627619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29055329358156989580836825 21791497018617742185627619)
                ·
                  refine ⟨32687245527926613278441429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21791497018617742185627619 32687245527926613278441429)
                  ·
                    refine ⟨766107317060779998713471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32687245527926613278441429 766107317060779998713471)
                    ·
                      rfl

theorem cell23_4475966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_4475966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475966 prefixEnd_4475966 := by exact prefixLift 4475966
  have htrace : WordTrace (prefixWord ++ tailWord_4475966) baseStart_4475966 baseEnd_4475966 := by
    simpa [prefixWord, tailWord_4475966, baseEnd_4475966] using wordTrace_append hprefix tailTrace_4475966
  have hstable : (prefixWord ++ tailWord_4475966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475966).length < 2 ^ (prefixWord ++ tailWord_4475966).sum := by decide
  have hdescent : baseEnd_4475966 < baseStart_4475966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4475986 : List Nat := [3, 2, 2, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_4475986 : Nat := 118140960795 + 4475986 * 2 ^ 59
def prefixEnd_4475986 : Nat := 4983230072969 + 3 ^ 40 * 4475986 * 2
def baseEnd_4475986 : Nat := 2298332220795429917890321

theorem tailTrace_4475986 : CollatzResearch.WordTrace tailWord_4475986 prefixEnd_4475986 2298332220795429917890321 := by
  unfold tailWord_4475986
  simp only [CollatzResearch.WordTrace]
  refine ⟨40813155290568658598481953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108835080774849756262618541 40813155290568658598481953)
  ·
    refine ⟨30609866467926493948861465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40813155290568658598481953 30609866467926493948861465)
    ·
      refine ⟨22957399850944870461646099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30609866467926493948861465 22957399850944870461646099)
      ·
        refine ⟨34436099776417305692469149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22957399850944870461646099 34436099776417305692469149)
        ·
          refine ⟨12913537416156489634675931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34436099776417305692469149 12913537416156489634675931)
          ·
            refine ⟨19370306124234734452013897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12913537416156489634675931 19370306124234734452013897)
            ·
              refine ⟨14527729593176050839010423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19370306124234734452013897 14527729593176050839010423)
              ·
                refine ⟨21791594389764076258515635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14527729593176050839010423 21791594389764076258515635)
                ·
                  refine ⟨32687391584646114387773453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21791594389764076258515635 32687391584646114387773453)
                  ·
                    refine ⟨12257771844242292895415045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32687391584646114387773453 12257771844242292895415045)
                    ·
                      refine ⟨2298332220795429917890321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12257771844242292895415045 2298332220795429917890321)
                      ·
                        rfl

theorem cell23_4475986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_4475986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4475986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4475986 prefixEnd_4475986 := by exact prefixLift 4475986
  have htrace : WordTrace (prefixWord ++ tailWord_4475986) baseStart_4475986 baseEnd_4475986 := by
    simpa [prefixWord, tailWord_4475986, baseEnd_4475986] using wordTrace_append hprefix tailTrace_4475986
  have hstable : (prefixWord ++ tailWord_4475986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4475986).length < 2 ^ (prefixWord ++ tailWord_4475986).sum := by decide
  have hdescent : baseEnd_4475986 < baseStart_4475986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4475986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476009 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 8]
def baseStart_4476009 : Nat := 118140960795 + 4476009 * 2 ^ 59
def prefixEnd_4476009 : Nat := 4983230072969 + 3 ^ 40 * 4476009 * 2
def baseEnd_4476009 : Nat := 255371558983387036433635

theorem tailTrace_4476009 : CollatzResearch.WordTrace tailWord_4476009 prefixEnd_4476009 255371558983387036433635 := by
  unfold tailWord_4476009
  simp only [CollatzResearch.WordTrace]
  refine ⟨163253460041191309322015081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108835640027460872881343387 163253460041191309322015081)
  ·
    refine ⟨122440095030893481991511311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163253460041191309322015081 122440095030893481991511311)
    ·
      refine ⟨183660142546340222987266967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122440095030893481991511311 183660142546340222987266967)
      ·
        refine ⟨275490213819510334480900451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 183660142546340222987266967 275490213819510334480900451)
        ·
          refine ⟨413235320729265501721350677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275490213819510334480900451 413235320729265501721350677)
          ·
            refine ⟨19370405659184320393188313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 413235320729265501721350677 19370405659184320393188313)
            ·
              refine ⟨14527804244388240294891235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19370405659184320393188313 14527804244388240294891235)
              ·
                refine ⟨21791706366582360442336853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14527804244388240294891235 21791706366582360442336853)
                ·
                  refine ⟨255371558983387036433635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21791706366582360442336853 255371558983387036433635)
                  ·
                    rfl

theorem cell23_4476009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 8].length) (baseStart_4476009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476009 prefixEnd_4476009 := by exact prefixLift 4476009
  have htrace : WordTrace (prefixWord ++ tailWord_4476009) baseStart_4476009 baseEnd_4476009 := by
    simpa [prefixWord, tailWord_4476009, baseEnd_4476009] using wordTrace_append hprefix tailTrace_4476009
  have hstable : (prefixWord ++ tailWord_4476009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476009).length < 2 ^ (prefixWord ++ tailWord_4476009).sum := by decide
  have hdescent : baseEnd_4476009 < baseStart_4476009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476013 : List Nat := [1, 5, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_4476013 : Nat := 118140960795 + 4476013 * 2 ^ 59
def prefixEnd_4476013 : Nat := 4983230072969 + 3 ^ 40 * 4476013 * 2
def baseEnd_4476013 : Nat := 766115361591033770750899

theorem tailTrace_4476013 : CollatzResearch.WordTrace tailWord_4476013 prefixEnd_4476013 766115361591033770750899 := by
  unfold tailWord_4476013
  simp only [CollatzResearch.WordTrace]
  refine ⟨163253605933176818005160693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108835737288784545336773795 163253605933176818005160693)
  ·
    refine ⟨15305025556235326687983815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 163253605933176818005160693 15305025556235326687983815)
    ·
      refine ⟨22957538334352990031975723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15305025556235326687983815 22957538334352990031975723)
      ·
        refine ⟨34436307501529485047963585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22957538334352990031975723 34436307501529485047963585)
        ·
          refine ⟨25827230626147113785972689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34436307501529485047963585 25827230626147113785972689)
          ·
            refine ⟨19370422969610335339479517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25827230626147113785972689 19370422969610335339479517)
            ·
              refine ⟨7263908613603875752304819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19370422969610335339479517 7263908613603875752304819)
              ·
                refine ⟨10895862920405813628457229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263908613603875752304819 10895862920405813628457229)
                ·
                  refine ⟨4085948595152180110671461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10895862920405813628457229 4085948595152180110671461)
                  ·
                    refine ⟨766115361591033770750899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4085948595152180110671461 766115361591033770750899)
                    ·
                      rfl

theorem cell23_4476013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_4476013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476013 prefixEnd_4476013 := by exact prefixLift 4476013
  have htrace : WordTrace (prefixWord ++ tailWord_4476013) baseStart_4476013 baseEnd_4476013 := by
    simpa [prefixWord, tailWord_4476013, baseEnd_4476013] using wordTrace_append hprefix tailTrace_4476013
  have hstable : (prefixWord ++ tailWord_4476013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476013).length < 2 ^ (prefixWord ++ tailWord_4476013).sum := by decide
  have hdescent : baseEnd_4476013 < baseStart_4476013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476040 : List Nat := [2, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4476040 : Nat := 118140960795 + 4476040 * 2 ^ 59
def prefixEnd_4476040 : Nat := 4983230072969 + 3 ^ 40 * 4476040 * 2
def baseEnd_4476040 : Nat := 2298359948750772706615073

theorem tailTrace_4476040 : CollatzResearch.WordTrace tailWord_4476040 prefixEnd_4476040 2298359948750772706615073 := by
  unfold tailWord_4476040
  simp only [CollatzResearch.WordTrace]
  refine ⟨81627295352039500808196787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 108836393802719334410929049 81627295352039500808196787)
  ·
    refine ⟨122440943028059251212295181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 81627295352039500808196787 122440943028059251212295181)
    ·
      refine ⟨45915353635522219204610693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 122440943028059251212295181 45915353635522219204610693)
      ·
        refine ⟨8609128806660416100864505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45915353635522219204610693 8609128806660416100864505)
        ·
          refine ⟨6456846604995312075648379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8609128806660416100864505 6456846604995312075648379)
          ·
            refine ⟨9685269907492968113472569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6456846604995312075648379 9685269907492968113472569)
            ·
              refine ⟨7263952430619726085104427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9685269907492968113472569 7263952430619726085104427)
              ·
                refine ⟨10895928645929589127656641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7263952430619726085104427 10895928645929589127656641)
                ·
                  refine ⟨8171946484447191845742481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10895928645929589127656641 8171946484447191845742481)
                  ·
                    refine ⟨6128959863335393884306861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8171946484447191845742481 6128959863335393884306861)
                    ·
                      refine ⟨2298359948750772706615073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6128959863335393884306861 2298359948750772706615073)
                      ·
                        rfl

theorem cell23_4476040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4476040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476040 prefixEnd_4476040 := by exact prefixLift 4476040
  have htrace : WordTrace (prefixWord ++ tailWord_4476040) baseStart_4476040 baseEnd_4476040 := by
    simpa [prefixWord, tailWord_4476040, baseEnd_4476040] using wordTrace_append hprefix tailTrace_4476040
  have hstable : (prefixWord ++ tailWord_4476040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476040).length < 2 ^ (prefixWord ++ tailWord_4476040).sum := by decide
  have hdescent : baseEnd_4476040 < baseStart_4476040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476097 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 2, 3, 2]
def baseStart_4476097 : Nat := 118140960795 + 4476097 * 2 ^ 59
def prefixEnd_4476097 : Nat := 4983230072969 + 3 ^ 40 * 4476097 * 2
def baseEnd_4476097 : Nat := 2298389217148078983602311

theorem tailTrace_4476097 : CollatzResearch.WordTrace tailWord_4476097 prefixEnd_4476097 2298389217148078983602311 := by
  unfold tailWord_4476097
  simp only [CollatzResearch.WordTrace]
  refine ⟨163256669664872500351218545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108837779776581666900812363 163256669664872500351218545)
  ·
    refine ⟨122442502248654375263413909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163256669664872500351218545 122442502248654375263413909)
    ·
      refine ⟨5739492292905673840472527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 122442502248654375263413909 5739492292905673840472527)
      ·
        refine ⟨8609238439358510760708791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5739492292905673840472527 8609238439358510760708791)
        ·
          refine ⟨12913857659037766141063187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8609238439358510760708791 12913857659037766141063187)
          ·
            refine ⟨19370786488556649211594781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12913857659037766141063187 19370786488556649211594781)
            ·
              refine ⟨7264044933208743454348043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19370786488556649211594781 7264044933208743454348043)
              ·
                refine ⟨10896067399813115181522065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264044933208743454348043 10896067399813115181522065)
                ·
                  refine ⟨8172050549859836386141549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10896067399813115181522065 8172050549859836386141549)
                  ·
                    refine ⟨3064518956197438644803081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8172050549859836386141549 3064518956197438644803081)
                    ·
                      refine ⟨2298389217148078983602311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064518956197438644803081 2298389217148078983602311)
                      ·
                        rfl

theorem cell23_4476097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_4476097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476097 prefixEnd_4476097 := by exact prefixLift 4476097
  have htrace : WordTrace (prefixWord ++ tailWord_4476097) baseStart_4476097 baseEnd_4476097 := by
    simpa [prefixWord, tailWord_4476097, baseEnd_4476097] using wordTrace_append hprefix tailTrace_4476097
  have hstable : (prefixWord ++ tailWord_4476097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476097).length < 2 ^ (prefixWord ++ tailWord_4476097).sum := by decide
  have hdescent : baseEnd_4476097 < baseStart_4476097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476110 : List Nat := [4, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_4476110 : Nat := 118140960795 + 4476110 * 2 ^ 59
def prefixEnd_4476110 : Nat := 4983230072969 + 3 ^ 40 * 4476110 * 2
def baseEnd_4476110 : Nat := 2298395892396587432739751

theorem tailTrace_4476110 : CollatzResearch.WordTrace tailWord_4476110 prefixEnd_4476110 2298395892396587432739751 := by
  unfold tailWord_4476110
  simp only [CollatzResearch.WordTrace]
  refine ⟨20407142976728175446430223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 108838095875883602380961189 20407142976728175446430223)
  ·
    refine ⟨30610714465092263169645335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20407142976728175446430223 30610714465092263169645335)
    ·
      refine ⟨45916071697638394754468003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30610714465092263169645335 45916071697638394754468003)
      ·
        refine ⟨68874107546457592131702005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45916071697638394754468003 68874107546457592131702005)
        ·
          refine ⟨6456947582480399262347063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 68874107546457592131702005 6456947582480399262347063)
          ·
            refine ⟨9685421373720598893520595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6456947582480399262347063 9685421373720598893520595)
            ·
              refine ⟨14528132060580898340280893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9685421373720598893520595 14528132060580898340280893)
              ·
                refine ⟨5448049522717836877605335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14528132060580898340280893 5448049522717836877605335)
                ·
                  refine ⟨8172074284076755316408003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448049522717836877605335 8172074284076755316408003)
                  ·
                    refine ⟨12258111426115132974612005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8172074284076755316408003 12258111426115132974612005)
                    ·
                      refine ⟨2298395892396587432739751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12258111426115132974612005 2298395892396587432739751)
                      ·
                        rfl

theorem cell23_4476110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_4476110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476110 prefixEnd_4476110 := by exact prefixLift 4476110
  have htrace : WordTrace (prefixWord ++ tailWord_4476110) baseStart_4476110 baseEnd_4476110 := by
    simpa [prefixWord, tailWord_4476110, baseEnd_4476110] using wordTrace_append hprefix tailTrace_4476110
  have hstable : (prefixWord ++ tailWord_4476110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476110).length < 2 ^ (prefixWord ++ tailWord_4476110).sum := by decide
  have hdescent : baseEnd_4476110 < baseStart_4476110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476127 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 1, 2, 2]
def baseStart_4476127 : Nat := 118140960795 + 4476127 * 2 ^ 59
def prefixEnd_4476127 : Nat := 4983230072969 + 3 ^ 40 * 4476127 * 2
def baseEnd_4476127 : Nat := 2298404621567713866227173

theorem tailTrace_4476127 : CollatzResearch.WordTrace tailWord_4476127 prefixEnd_4476127 2298404621567713866227173 := by
  unfold tailWord_4476127
  simp only [CollatzResearch.WordTrace]
  refine ⟨163257763854763815474810635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108838509236509210316540423 163257763854763815474810635)
  ·
    refine ⟨244886645782145723212215953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163257763854763815474810635 244886645782145723212215953)
    ·
      refine ⟨183664984336609292409161965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244886645782145723212215953 183664984336609292409161965)
      ·
        refine ⟨68874369126228484653435737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 183664984336609292409161965 68874369126228484653435737)
        ·
          refine ⟨51655776844671363490076803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68874369126228484653435737 51655776844671363490076803)
          ·
            refine ⟨77483665267007045235115205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51655776844671363490076803 77483665267007045235115205)
            ·
              refine ⟨14528187237563820981584101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 77483665267007045235115205 14528187237563820981584101)
              ·
                refine ⟨2724035107043216434047019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14528187237563820981584101 2724035107043216434047019)
                ·
                  refine ⟨4086052660564824651070529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2724035107043216434047019 4086052660564824651070529)
                  ·
                    refine ⟨3064539495423618488302897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086052660564824651070529 3064539495423618488302897)
                    ·
                      refine ⟨2298404621567713866227173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064539495423618488302897 2298404621567713866227173)
                      ·
                        rfl

theorem cell23_4476127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 1, 2, 2].length) (baseStart_4476127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476127 prefixEnd_4476127 := by exact prefixLift 4476127
  have htrace : WordTrace (prefixWord ++ tailWord_4476127) baseStart_4476127 baseEnd_4476127 := by
    simpa [prefixWord, tailWord_4476127, baseEnd_4476127] using wordTrace_append hprefix tailTrace_4476127
  have hstable : (prefixWord ++ tailWord_4476127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476127).length < 2 ^ (prefixWord ++ tailWord_4476127).sum := by decide
  have hdescent : baseEnd_4476127 < baseStart_4476127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476178 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_4476178 : Nat := 118140960795 + 4476178 * 2 ^ 59
def prefixEnd_4476178 : Nat := 4983230072969 + 3 ^ 40 * 4476178 * 2
def baseEnd_4476178 : Nat := 2298430809081093166689439

theorem tailTrace_4476178 : CollatzResearch.WordTrace tailWord_4476178 prefixEnd_4476178 2298430809081093166689439 := by
  unfold tailWord_4476178
  simp only [CollatzResearch.WordTrace]
  refine ⟨40814905994394762796229297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 108839749318386034123278125 40814905994394762796229297)
  ·
    refine ⟨30611179495796072097171973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40814905994394762796229297 30611179495796072097171973)
    ·
      refine ⟨5739596155461763518219745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30611179495796072097171973 5739596155461763518219745)
      ·
        refine ⟨4304697116596322638664809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5739596155461763518219745 4304697116596322638664809)
        ·
          refine ⟨3228522837447241978998607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4304697116596322638664809 3228522837447241978998607)
          ·
            refine ⟨4842784256170862968497911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3228522837447241978998607 4842784256170862968497911)
            ·
              refine ⟨7264176384256294452746867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4842784256170862968497911 7264176384256294452746867)
              ·
                refine ⟨10896264576384441679120301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7264176384256294452746867 10896264576384441679120301)
                ·
                  refine ⟨4086099216144165629670113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10896264576384441679120301 4086099216144165629670113)
                  ·
                    refine ⟨3064574412108124222252585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4086099216144165629670113 3064574412108124222252585)
                    ·
                      refine ⟨2298430809081093166689439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064574412108124222252585 2298430809081093166689439)
                      ·
                        rfl

theorem cell23_4476178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_4476178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476178 prefixEnd_4476178 := by exact prefixLift 4476178
  have htrace : WordTrace (prefixWord ++ tailWord_4476178) baseStart_4476178 baseEnd_4476178 := by
    simpa [prefixWord, tailWord_4476178, baseEnd_4476178] using wordTrace_append hprefix tailTrace_4476178
  have hstable : (prefixWord ++ tailWord_4476178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476178).length < 2 ^ (prefixWord ++ tailWord_4476178).sum := by decide
  have hdescent : baseEnd_4476178 < baseStart_4476178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476217 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4476217 : Nat := 118140960795 + 4476217 * 2 ^ 59
def prefixEnd_4476217 : Nat := 4983230072969 + 3 ^ 40 * 4476217 * 2
def baseEnd_4476217 : Nat := 2298450834826618514101759

theorem tailTrace_4476217 : CollatzResearch.WordTrace tailWord_4476217 prefixEnd_4476217 2298450834826618514101759 := by
  unfold tailWord_4476217
  simp only [CollatzResearch.WordTrace]
  refine ⟨163261046424437760845586905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108840697616291840563724603 163261046424437760845586905)
  ·
    refine ⟨122445784818328320634190179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 163261046424437760845586905 122445784818328320634190179)
    ·
      refine ⟨183668677227492480951285269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 122445784818328320634190179 183668677227492480951285269)
      ·
        refine ⟨8609469245038710044591497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 183668677227492480951285269 8609469245038710044591497)
        ·
          refine ⟨6457101933779032533443623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8609469245038710044591497 6457101933779032533443623)
          ·
            refine ⟨9685652900668548800165435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457101933779032533443623 9685652900668548800165435)
            ·
              refine ⟨14528479351002823200248153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9685652900668548800165435 14528479351002823200248153)
              ·
                refine ⟨10896359513252117400186115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14528479351002823200248153 10896359513252117400186115)
                ·
                  refine ⟨16344539269878176100279173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10896359513252117400186115 16344539269878176100279173)
                  ·
                    refine ⟨3064601113102158018802345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16344539269878176100279173 3064601113102158018802345)
                    ·
                      refine ⟨2298450834826618514101759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064601113102158018802345 2298450834826618514101759)
                      ·
                        rfl

theorem cell23_4476217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4476217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476217 prefixEnd_4476217 := by exact prefixLift 4476217
  have htrace : WordTrace (prefixWord ++ tailWord_4476217) baseStart_4476217 baseEnd_4476217 := by
    simpa [prefixWord, tailWord_4476217, baseEnd_4476217] using wordTrace_append hprefix tailTrace_4476217
  have hstable : (prefixWord ++ tailWord_4476217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476217).length < 2 ^ (prefixWord ++ tailWord_4476217).sum := by decide
  have hdescent : baseEnd_4476217 < baseStart_4476217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476221 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4476221 : Nat := 118140960795 + 4476221 * 2 ^ 59
def prefixEnd_4476221 : Nat := 4983230072969 + 3 ^ 40 * 4476221 * 2
def baseEnd_4476221 : Nat := 2298452888749236498451741

theorem tailTrace_4476221 : CollatzResearch.WordTrace tailWord_4476221 prefixEnd_4476221 2298452888749236498451741 := by
  unfold tailWord_4476221
  simp only [CollatzResearch.WordTrace]
  refine ⟨163261192316423269528732517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108840794877615513019155011 163261192316423269528732517)
  ·
    refine ⟨30611473559329363036637347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 163261192316423269528732517 30611473559329363036637347)
    ·
      refine ⟨45917210338994044554956021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30611473559329363036637347 45917210338994044554956021)
      ·
        refine ⟨4304738469280691677027127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45917210338994044554956021 4304738469280691677027127)
        ·
          refine ⟨6457107703921037515540691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4304738469280691677027127 6457107703921037515540691)
          ·
            refine ⟨9685661555881556273311037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6457107703921037515540691 9685661555881556273311037)
            ·
              refine ⟨3632123083455583602491639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9685661555881556273311037 3632123083455583602491639)
              ·
                refine ⟨5448184625183375403737459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3632123083455583602491639 5448184625183375403737459)
                ·
                  refine ⟨8172276937775063105606189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5448184625183375403737459 8172276937775063105606189)
                  ·
                    refine ⟨3064603851665648664602321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8172276937775063105606189 3064603851665648664602321)
                    ·
                      refine ⟨2298452888749236498451741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064603851665648664602321 2298452888749236498451741)
                      ·
                        rfl

theorem cell23_4476221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4476221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476221 prefixEnd_4476221 := by exact prefixLift 4476221
  have htrace : WordTrace (prefixWord ++ tailWord_4476221) baseStart_4476221 baseEnd_4476221 := by
    simpa [prefixWord, tailWord_4476221, baseEnd_4476221] using wordTrace_append hprefix tailTrace_4476221
  have hstable : (prefixWord ++ tailWord_4476221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476221).length < 2 ^ (prefixWord ++ tailWord_4476221).sum := by decide
  have hdescent : baseEnd_4476221 < baseStart_4476221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4476243 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 1, 7, 2]
def baseStart_4476243 : Nat := 118140960795 + 4476243 * 2 ^ 59
def prefixEnd_4476243 : Nat := 4983230072969 + 3 ^ 40 * 4476243 * 2
def baseEnd_4476243 : Nat := 2298464185323635412376639

theorem tailTrace_4476243 : CollatzResearch.WordTrace tailWord_4476243 prefixEnd_4476243 2298464185323635412376639 := by
  unfold tailWord_4476243
  simp only [CollatzResearch.WordTrace]
  refine ⟨163261994722343567286033383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 108841329814895711524022255 163261994722343567286033383)
  ·
    refine ⟨244892992083515350929050075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 163261994722343567286033383 244892992083515350929050075)
    ·
      refine ⟨367339488125273026393575113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 244892992083515350929050075 367339488125273026393575113)
      ·
        refine ⟨275504616093954769795181335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 367339488125273026393575113 275504616093954769795181335)
        ·
          refine ⟨413256924140932154692772003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 275504616093954769795181335 413256924140932154692772003)
          ·
            refine ⟨619885386211398232039158005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 413256924140932154692772003 619885386211398232039158005)
            ·
              refine ⟨58114254957318584253671063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 619885386211398232039158005 58114254957318584253671063)
              ·
                refine ⟨87171382435977876380506595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58114254957318584253671063 87171382435977876380506595)
                ·
                  refine ⟨130757073653966814570759893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 87171382435977876380506595 130757073653966814570759893)
                  ·
                    refine ⟨3064618913764847216502185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 130757073653966814570759893 3064618913764847216502185)
                    ·
                      refine ⟨2298464185323635412376639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3064618913764847216502185 2298464185323635412376639)
                      ·
                        rfl

theorem cell23_4476243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 7, 2].length) (baseStart_4476243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4476243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4476243 prefixEnd_4476243 := by exact prefixLift 4476243
  have htrace : WordTrace (prefixWord ++ tailWord_4476243) baseStart_4476243 baseEnd_4476243 := by
    simpa [prefixWord, tailWord_4476243, baseEnd_4476243] using wordTrace_append hprefix tailTrace_4476243
  have hstable : (prefixWord ++ tailWord_4476243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4476243).length < 2 ^ (prefixWord ++ tailWord_4476243).sum := by decide
  have hdescent : baseEnd_4476243 < baseStart_4476243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4476243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
