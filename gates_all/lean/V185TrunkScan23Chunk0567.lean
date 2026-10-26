import V185TrunkScan23Chunk0566

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3352076 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 7]
def baseStart_3352076 : Nat := 118140960795 + 3352076 * 2 ^ 59
def prefixEnd_3352076 : Nat := 4983230072969 + 3 ^ 40 * 3352076 * 2
def baseEnd_3352076 : Nat := 191247353155636913437121

theorem tailTrace_3352076 : CollatzResearch.WordTrace tailWord_3352076 prefixEnd_3352076 191247353155636913437121 := by
  unfold tailWord_3352076
  simp only [CollatzResearch.WordTrace]
  refine ⟨61130127902004307923866041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81506837202672410565154721 61130127902004307923866041)
  ·
    refine ⟨45847595926503230942899531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61130127902004307923866041 45847595926503230942899531)
    ·
      refine ⟨68771393889754846414349297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45847595926503230942899531 68771393889754846414349297)
      ·
        refine ⟨51578545417316134810761973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68771393889754846414349297 51578545417316134810761973)
        ·
          refine ⟨4835488632873387638508935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51578545417316134810761973 4835488632873387638508935)
          ·
            refine ⟨7253232949310081457763403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835488632873387638508935 7253232949310081457763403)
            ·
              refine ⟨10879849423965122186645105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253232949310081457763403 10879849423965122186645105)
              ·
                refine ⟨8159887067973841639983829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10879849423965122186645105 8159887067973841639983829)
                ·
                  refine ⟨191247353155636913437121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8159887067973841639983829 191247353155636913437121)
                  ·
                    rfl

theorem cell23_3352076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_3352076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352076 prefixEnd_3352076 := by exact prefixLift 3352076
  have htrace : WordTrace (prefixWord ++ tailWord_3352076) baseStart_3352076 baseEnd_3352076 := by
    simpa [prefixWord, tailWord_3352076, baseEnd_3352076] using wordTrace_append hprefix tailTrace_3352076
  have hstable : (prefixWord ++ tailWord_3352076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352076).length < 2 ^ (prefixWord ++ tailWord_3352076).sum := by decide
  have hdescent : baseEnd_3352076 < baseStart_3352076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352093 : List Nat := [1, 4, 2, 2, 1, 1, 4, 3, 5]
def baseStart_3352093 : Nat := 118140960795 + 3352093 * 2 ^ 59
def prefixEnd_3352093 : Nat := 4983230072969 + 3 ^ 40 * 3352093 * 2
def baseEnd_3352093 : Nat := 191248323063539850491279

theorem tailTrace_3352093 : CollatzResearch.WordTrace tailWord_3352093 prefixEnd_3352093 191248323063539850491279 := by
  unfold tailWord_3352093
  simp only [CollatzResearch.WordTrace]
  refine ⟨122260875844947027751100933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81507250563298018500733955 122260875844947027751100933)
  ·
    refine ⟨22923914220927567703331425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122260875844947027751100933 22923914220927567703331425)
    ·
      refine ⟨17192935665695675777498569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22923914220927567703331425 17192935665695675777498569)
      ·
        refine ⟨12894701749271756833123927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17192935665695675777498569 12894701749271756833123927)
        ·
          refine ⟨19342052623907635249685891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894701749271756833123927 19342052623907635249685891)
          ·
            refine ⟨29013078935861452874528837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19342052623907635249685891 29013078935861452874528837)
            ·
              refine ⟨5439952300474022413974157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29013078935861452874528837 5439952300474022413974157)
              ·
                refine ⟨2039982112677758405240309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439952300474022413974157 2039982112677758405240309)
                ·
                  refine ⟨191248323063539850491279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039982112677758405240309 191248323063539850491279)
                  ·
                    rfl

theorem cell23_3352093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_3352093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352093 prefixEnd_3352093 := by exact prefixLift 3352093
  have htrace : WordTrace (prefixWord ++ tailWord_3352093) baseStart_3352093 baseEnd_3352093 := by
    simpa [prefixWord, tailWord_3352093, baseEnd_3352093] using wordTrace_append hprefix tailTrace_3352093
  have hstable : (prefixWord ++ tailWord_3352093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352093).length < 2 ^ (prefixWord ++ tailWord_3352093).sum := by decide
  have hdescent : baseEnd_3352093 < baseStart_3352093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352104 : List Nat := [2, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3352104 : Nat := 118140960795 + 3352104 * 2 ^ 59
def prefixEnd_3352104 : Nat := 4983230072969 + 3 ^ 40 * 3352104 * 2
def baseEnd_3352104 : Nat := 1721240555859058111383961

theorem tailTrace_3352104 : CollatzResearch.WordTrace tailWord_3352104 prefixEnd_3352104 1721240555859058111383961 := by
  unfold tailWord_3352104
  simp only [CollatzResearch.WordTrace]
  refine ⟨61130638523953588314875683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81507518031938117753167577 61130638523953588314875683)
  ·
    refine ⟨91695957785930382472313525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61130638523953588314875683 91695957785930382472313525)
    ·
      refine ⟨8596496042430973356779393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91695957785930382472313525 8596496042430973356779393)
      ·
        refine ⟨6447372031823230017584545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596496042430973356779393 6447372031823230017584545)
        ·
          refine ⟨4835529023867422513188409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6447372031823230017584545 4835529023867422513188409)
          ·
            refine ⟨3626646767900566884891307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835529023867422513188409 3626646767900566884891307)
            ·
              refine ⟨5439970151850850327336961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626646767900566884891307 5439970151850850327336961)
              ·
                refine ⟨4079977613888137745502721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439970151850850327336961 4079977613888137745502721)
                ·
                  refine ⟨3059983210416103309127041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079977613888137745502721 3059983210416103309127041)
                  ·
                    refine ⟨2294987407812077481845281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059983210416103309127041 2294987407812077481845281)
                    ·
                      refine ⟨1721240555859058111383961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294987407812077481845281 1721240555859058111383961)
                      ·
                        rfl

theorem cell23_3352104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3352104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352104 prefixEnd_3352104 := by exact prefixLift 3352104
  have htrace : WordTrace (prefixWord ++ tailWord_3352104) baseStart_3352104 baseEnd_3352104 := by
    simpa [prefixWord, tailWord_3352104, baseEnd_3352104] using wordTrace_append hprefix tailTrace_3352104
  have hstable : (prefixWord ++ tailWord_3352104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352104).length < 2 ^ (prefixWord ++ tailWord_3352104).sum := by decide
  have hdescent : baseEnd_3352104 < baseStart_3352104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352106 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3352106 : Nat := 118140960795 + 3352106 * 2 ^ 59
def prefixEnd_3352106 : Nat := 4983230072969 + 3 ^ 40 * 3352106 * 2
def baseEnd_3352106 : Nat := 573747194273455701186317

theorem tailTrace_3352106 : CollatzResearch.WordTrace tailWord_3352106 prefixEnd_3352106 573747194273455701186317 := by
  unfold tailWord_3352106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30565337498474982742831043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81507566662599953980882781 30565337498474982742831043)
  ·
    refine ⟨45848006247712474114246565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30565337498474982742831043 45848006247712474114246565)
    ·
      refine ⟨8596501171446088896421231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45848006247712474114246565 8596501171446088896421231)
      ·
        refine ⟨12894751757169133344631847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8596501171446088896421231 12894751757169133344631847)
        ·
          refine ⟨19342127635753700016947771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894751757169133344631847 19342127635753700016947771)
          ·
            refine ⟨29013191453630550025421657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19342127635753700016947771 29013191453630550025421657)
            ·
              refine ⟨21759893590222912519066243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29013191453630550025421657 21759893590222912519066243)
              ·
                refine ⟨32639840385334368778599365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21759893590222912519066243 32639840385334368778599365)
                ·
                  refine ⟨6119970072250194145987381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32639840385334368778599365 6119970072250194145987381)
                  ·
                    refine ⟨573747194273455701186317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6119970072250194145987381 573747194273455701186317)
                    ·
                      rfl

theorem cell23_3352106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3352106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352106 prefixEnd_3352106 := by exact prefixLift 3352106
  have htrace : WordTrace (prefixWord ++ tailWord_3352106) baseStart_3352106 baseEnd_3352106 := by
    simpa [prefixWord, tailWord_3352106, baseEnd_3352106] using wordTrace_append hprefix tailTrace_3352106
  have hstable : (prefixWord ++ tailWord_3352106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352106).length < 2 ^ (prefixWord ++ tailWord_3352106).sum := by decide
  have hdescent : baseEnd_3352106 < baseStart_3352106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352139 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4]
def baseStart_3352139 : Nat := 118140960795 + 3352139 * 2 ^ 59
def prefixEnd_3352139 : Nat := 4983230072969 + 3 ^ 40 * 3352139 * 2
def baseEnd_3352139 : Nat := 1721258527681965474446299

theorem tailTrace_3352139 : CollatzResearch.WordTrace tailWord_3352139 prefixEnd_3352139 1721258527681965474446299 := by
  unfold tailWord_3352139
  simp only [CollatzResearch.WordTrace]
  refine ⟨122262553602780377607275471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81508369068520251738183647 122262553602780377607275471)
  ·
    refine ⟨183393830404170566410913207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122262553602780377607275471 183393830404170566410913207)
    ·
      refine ⟨275090745606255849616369811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183393830404170566410913207 275090745606255849616369811)
      ·
        refine ⟨412636118409383774424554717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275090745606255849616369811 412636118409383774424554717)
        ·
          refine ⟨154738544403518915409208019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 412636118409383774424554717 154738544403518915409208019)
          ·
            refine ⟨232107816605278373113812029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154738544403518915409208019 232107816605278373113812029)
            ·
              refine ⟨87040431226979389917679511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232107816605278373113812029 87040431226979389917679511)
              ·
                refine ⟨130560646840469084876519267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87040431226979389917679511 130560646840469084876519267)
                ·
                  refine ⟨195840970260703627314778901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130560646840469084876519267 195840970260703627314778901)
                  ·
                    refine ⟨9180045480970482530380261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 195840970260703627314778901 9180045480970482530380261)
                    ·
                      refine ⟨1721258527681965474446299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9180045480970482530380261 1721258527681965474446299)
                      ·
                        rfl

theorem cell23_3352139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 4].length) (baseStart_3352139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352139 prefixEnd_3352139 := by exact prefixLift 3352139
  have htrace : WordTrace (prefixWord ++ tailWord_3352139) baseStart_3352139 baseEnd_3352139 := by
    simpa [prefixWord, tailWord_3352139, baseEnd_3352139] using wordTrace_append hprefix tailTrace_3352139
  have hstable : (prefixWord ++ tailWord_3352139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352139).length < 2 ^ (prefixWord ++ tailWord_3352139).sum := by decide
  have hdescent : baseEnd_3352139 < baseStart_3352139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352163 : List Nat := [1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3]
def baseStart_3352163 : Nat := 118140960795 + 3352163 * 2 ^ 59
def prefixEnd_3352163 : Nat := 4983230072969 + 3 ^ 40 * 3352163 * 2
def baseEnd_3352163 : Nat := 1721270851217673380546189

theorem tailTrace_3352163 : CollatzResearch.WordTrace tailWord_3352163 prefixEnd_3352163 1721270851217673380546189 := by
  unfold tailWord_3352163
  simp only [CollatzResearch.WordTrace]
  refine ⟨122263428954693429706149143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81508952636462286470766095 122263428954693429706149143)
  ·
    refine ⟨183395143432040144559223715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122263428954693429706149143 183395143432040144559223715)
    ·
      refine ⟨275092715148060216838835573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183395143432040144559223715 275092715148060216838835573)
      ·
        refine ⟨25789942045130645328640835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275092715148060216838835573 25789942045130645328640835)
        ·
          refine ⟨38684913067695967992961253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25789942045130645328640835 38684913067695967992961253)
          ·
            refine ⟨7253421200192993998680235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38684913067695967992961253 7253421200192993998680235)
            ·
              refine ⟨10880131800289490998020353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253421200192993998680235 10880131800289490998020353)
              ·
                refine ⟨8160098850217118248515265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10880131800289490998020353 8160098850217118248515265)
                ·
                  refine ⟨6120074137662838686386449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8160098850217118248515265 6120074137662838686386449)
                  ·
                    refine ⟨4590055603247129014789837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120074137662838686386449 4590055603247129014789837)
                    ·
                      refine ⟨1721270851217673380546189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590055603247129014789837 1721270851217673380546189)
                      ·
                        rfl

theorem cell23_3352163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_3352163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352163 prefixEnd_3352163 := by exact prefixLift 3352163
  have htrace : WordTrace (prefixWord ++ tailWord_3352163) baseStart_3352163 baseEnd_3352163 := by
    simpa [prefixWord, tailWord_3352163, baseEnd_3352163] using wordTrace_append hprefix tailTrace_3352163
  have hstable : (prefixWord ++ tailWord_3352163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352163).length < 2 ^ (prefixWord ++ tailWord_3352163).sum := by decide
  have hdescent : baseEnd_3352163 < baseStart_3352163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352169 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_3352169 : Nat := 118140960795 + 3352169 * 2 ^ 59
def prefixEnd_3352169 : Nat := 4983230072969 + 3 ^ 40 * 3352169 * 2
def baseEnd_3352169 : Nat := 1721273932101600357071161

theorem tailTrace_3352169 : CollatzResearch.WordTrace tailWord_3352169 prefixEnd_3352169 1721273932101600357071161 := by
  unfold tailWord_3352169
  simp only [CollatzResearch.WordTrace]
  refine ⟨122263647792671692730867561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81509098528447795153911707 122263647792671692730867561)
  ·
    refine ⟨91697735844503769548150671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122263647792671692730867561 91697735844503769548150671)
    ·
      refine ⟨137546603766755654322226007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91697735844503769548150671 137546603766755654322226007)
      ·
        refine ⟨206319905650133481483339011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137546603766755654322226007 206319905650133481483339011)
        ·
          refine ⟨309479858475200222225008517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206319905650133481483339011 309479858475200222225008517)
          ·
            refine ⟨58027473464100041667189097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309479858475200222225008517 58027473464100041667189097)
            ·
              refine ⟨43520605098075031250391823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58027473464100041667189097 43520605098075031250391823)
              ·
                refine ⟨65280907647112546875587735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43520605098075031250391823 65280907647112546875587735)
                ·
                  refine ⟨97921361470668820313381603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65280907647112546875587735 97921361470668820313381603)
                  ·
                    refine ⟨146882042206003230470072405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97921361470668820313381603 146882042206003230470072405)
                    ·
                      refine ⟨1721273932101600357071161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146882042206003230470072405 1721273932101600357071161)
                      ·
                        rfl

theorem cell23_3352169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_3352169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352169 prefixEnd_3352169 := by exact prefixLift 3352169
  have htrace : WordTrace (prefixWord ++ tailWord_3352169) baseStart_3352169 baseEnd_3352169 := by
    simpa [prefixWord, tailWord_3352169, baseEnd_3352169] using wordTrace_append hprefix tailTrace_3352169
  have hstable : (prefixWord ++ tailWord_3352169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352169).length < 2 ^ (prefixWord ++ tailWord_3352169).sum := by decide
  have hdescent : baseEnd_3352169 < baseStart_3352169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352170 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3352170 : Nat := 118140960795 + 3352170 * 2 ^ 59
def prefixEnd_3352170 : Nat := 4983230072969 + 3 ^ 40 * 3352170 * 2
def baseEnd_3352170 : Nat := 573758148527418284386219

theorem tailTrace_3352170 : CollatzResearch.WordTrace tailWord_3352170 prefixEnd_3352170 573758148527418284386219 := by
  unfold tailWord_3352170
  simp only [CollatzResearch.WordTrace]
  refine ⟨30565921066417017475413491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81509122843778713267769309 30565921066417017475413491)
  ·
    refine ⟨45848881599625526213120237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30565921066417017475413491 45848881599625526213120237)
    ·
      refine ⟨17193330599859572329920089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45848881599625526213120237 17193330599859572329920089)
      ·
        refine ⟨12894997949894679247440067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17193330599859572329920089 12894997949894679247440067)
        ·
          refine ⟨19342496924842018871160101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12894997949894679247440067 19342496924842018871160101)
          ·
            refine ⟨3626718173407878538342519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19342496924842018871160101 3626718173407878538342519)
            ·
              refine ⟨5440077260111817807513779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626718173407878538342519 5440077260111817807513779)
              ·
                refine ⟨8160115890167726711270669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440077260111817807513779 8160115890167726711270669)
                ·
                  refine ⟨3060043458812897516726501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8160115890167726711270669 3060043458812897516726501)
                  ·
                    refine ⟨573758148527418284386219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060043458812897516726501 573758148527418284386219)
                    ·
                      rfl

theorem cell23_3352170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3352170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352170 prefixEnd_3352170 := by exact prefixLift 3352170
  have htrace : WordTrace (prefixWord ++ tailWord_3352170) baseStart_3352170 baseEnd_3352170 := by
    simpa [prefixWord, tailWord_3352170, baseEnd_3352170] using wordTrace_append hprefix tailTrace_3352170
  have hstable : (prefixWord ++ tailWord_3352170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352170).length < 2 ^ (prefixWord ++ tailWord_3352170).sum := by decide
  have hdescent : baseEnd_3352170 < baseStart_3352170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352243 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 2, 4]
def baseStart_3352243 : Nat := 118140960795 + 3352243 * 2 ^ 59
def prefixEnd_3352243 : Nat := 4983230072969 + 3 ^ 40 * 3352243 * 2
def baseEnd_3352243 : Nat := 573770643223344355848607

theorem tailTrace_3352243 : CollatzResearch.WordTrace tailWord_3352243 prefixEnd_3352243 573770643223344355848607 := by
  unfold tailWord_3352243
  simp only [CollatzResearch.WordTrace]
  refine ⟨122266346794403603369061383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81510897862935735579374255 122266346794403603369061383)
  ·
    refine ⟨183399520191605405053592075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122266346794403603369061383 183399520191605405053592075)
    ·
      refine ⟨275099280287408107580388113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183399520191605405053592075 275099280287408107580388113)
      ·
        refine ⟨206324460215556080685291085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275099280287408107580388113 206324460215556080685291085)
        ·
          refine ⟨77371672580833530256984157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206324460215556080685291085 77371672580833530256984157)
          ·
            refine ⟨29014377217812573846369059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77371672580833530256984157 29014377217812573846369059)
            ·
              refine ⟨43521565826718860769553589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29014377217812573846369059 43521565826718860769553589)
              ·
                refine ⟨4080146796254893197145649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43521565826718860769553589 4080146796254893197145649)
                ·
                  refine ⟨3060110097191169897859237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080146796254893197145649 3060110097191169897859237)
                  ·
                    refine ⟨573770643223344355848607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060110097191169897859237 573770643223344355848607)
                    ·
                      rfl

theorem cell23_3352243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 2, 4].length) (baseStart_3352243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352243 prefixEnd_3352243 := by exact prefixLift 3352243
  have htrace : WordTrace (prefixWord ++ tailWord_3352243) baseStart_3352243 baseEnd_3352243 := by
    simpa [prefixWord, tailWord_3352243, baseEnd_3352243] using wordTrace_append hprefix tailTrace_3352243
  have hstable : (prefixWord ++ tailWord_3352243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352243).length < 2 ^ (prefixWord ++ tailWord_3352243).sum := by decide
  have hdescent : baseEnd_3352243 < baseStart_3352243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352250 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2]
def baseStart_3352250 : Nat := 118140960795 + 3352250 * 2 ^ 59
def prefixEnd_3352250 : Nat := 4983230072969 + 3 ^ 40 * 3352250 * 2
def baseEnd_3352250 : Nat := 1721315524034614540158289

theorem tailTrace_3352250 : CollatzResearch.WordTrace tailWord_3352250 prefixEnd_3352250 1721315524034614540158289 := by
  unfold tailWord_3352250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566650526344560891141551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81511068070252162376377469 30566650526344560891141551)
  ·
    refine ⟨45849975789516841336712327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30566650526344560891141551 45849975789516841336712327)
    ·
      refine ⟨68774963684275262005068491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45849975789516841336712327 68774963684275262005068491)
      ·
        refine ⟨103162445526412893007602737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68774963684275262005068491 103162445526412893007602737)
        ·
          refine ⟨77371834144809669755702053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103162445526412893007602737 77371834144809669755702053)
          ·
            refine ⟨14507218902151813079194135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77371834144809669755702053 14507218902151813079194135)
            ·
              refine ⟨21760828353227719618791203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14507218902151813079194135 21760828353227719618791203)
              ·
                refine ⟨32641242529841579428186805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21760828353227719618791203 32641242529841579428186805)
                ·
                  refine ⟨3060116487172648071392513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32641242529841579428186805 3060116487172648071392513)
                  ·
                    refine ⟨2295087365379486053544385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3060116487172648071392513 2295087365379486053544385)
                    ·
                      refine ⟨1721315524034614540158289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295087365379486053544385 1721315524034614540158289)
                      ·
                        rfl

theorem cell23_3352250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2].length) (baseStart_3352250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352250 prefixEnd_3352250 := by exact prefixLift 3352250
  have htrace : WordTrace (prefixWord ++ tailWord_3352250) baseStart_3352250 baseEnd_3352250 := by
    simpa [prefixWord, tailWord_3352250, baseEnd_3352250] using wordTrace_append hprefix tailTrace_3352250
  have hstable : (prefixWord ++ tailWord_3352250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352250).length < 2 ^ (prefixWord ++ tailWord_3352250).sum := by decide
  have hdescent : baseEnd_3352250 < baseStart_3352250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352253 : List Nat := [1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_3352253 : Nat := 118140960795 + 3352253 * 2 ^ 59
def prefixEnd_3352253 : Nat := 4983230072969 + 3 ^ 40 * 3352253 * 2
def baseEnd_3352253 : Nat := 1721317064476578028420775

theorem tailTrace_3352253 : CollatzResearch.WordTrace tailWord_3352253 prefixEnd_3352253 1721317064476578028420775 := by
  unfold tailWord_3352253
  simp only [CollatzResearch.WordTrace]
  refine ⟨122266711524367375076925413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81511141016244916717950275 122266711524367375076925413)
  ·
    refine ⟨22925008410818882826923515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122266711524367375076925413 22925008410818882826923515)
    ·
      refine ⟨34387512616228324240385273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22925008410818882826923515 34387512616228324240385273)
      ·
        refine ⟨25790634462171243180288955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34387512616228324240385273 25790634462171243180288955)
        ·
          refine ⟨38685951693256864770433433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25790634462171243180288955 38685951693256864770433433)
          ·
            refine ⟨29014463769942648577825075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38685951693256864770433433 29014463769942648577825075)
            ·
              refine ⟨43521695654913972866737613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29014463769942648577825075 43521695654913972866737613)
              ·
                refine ⟨16320635870592739825026605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43521695654913972866737613 16320635870592739825026605)
                ·
                  refine ⟨6120238451472277434384977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16320635870592739825026605 6120238451472277434384977)
                  ·
                    refine ⟨4590178838604208075788733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120238451472277434384977 4590178838604208075788733)
                    ·
                      refine ⟨1721317064476578028420775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590178838604208075788733 1721317064476578028420775)
                      ·
                        rfl

theorem cell23_3352253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_3352253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352253 prefixEnd_3352253 := by exact prefixLift 3352253
  have htrace : WordTrace (prefixWord ++ tailWord_3352253) baseStart_3352253 baseEnd_3352253 := by
    simpa [prefixWord, tailWord_3352253, baseEnd_3352253] using wordTrace_append hprefix tailTrace_3352253
  have hstable : (prefixWord ++ tailWord_3352253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352253).length < 2 ^ (prefixWord ++ tailWord_3352253).sum := by decide
  have hdescent : baseEnd_3352253 < baseStart_3352253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352270 : List Nat := [4, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3352270 : Nat := 118140960795 + 3352270 * 2 ^ 59
def prefixEnd_3352270 : Nat := 4983230072969 + 3 ^ 40 * 3352270 * 2
def baseEnd_3352270 : Nat := 1721325793647704461908197

theorem tailTrace_3352270 : CollatzResearch.WordTrace tailWord_3352270 prefixEnd_3352270 1721325793647704461908197 := by
  unfold tailWord_3352270
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283416445663223372536783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81511554376870524653529509 15283416445663223372536783)
  ·
    refine ⟨22925124668494835058805175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15283416445663223372536783 22925124668494835058805175)
    ·
      refine ⟨34387687002742252588207763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22925124668494835058805175 34387687002742252588207763)
      ·
        refine ⟨51581530504113378882311645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34387687002742252588207763 51581530504113378882311645)
        ·
          refine ⟨19343073939042517080866867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51581530504113378882311645 19343073939042517080866867)
          ·
            refine ⟨29014610908563775621300301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19343073939042517080866867 29014610908563775621300301)
            ·
              refine ⟨10880479090711415857987613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29014610908563775621300301 10880479090711415857987613)
              ·
                refine ⟨4080179659016780946745355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10880479090711415857987613 4080179659016780946745355)
                ·
                  refine ⟨6120269488525171420118033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080179659016780946745355 6120269488525171420118033)
                  ·
                    refine ⟨4590202116393878565088525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120269488525171420118033 4590202116393878565088525)
                    ·
                      refine ⟨1721325793647704461908197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590202116393878565088525 1721325793647704461908197)
                      ·
                        rfl

theorem cell23_3352270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3352270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352270 prefixEnd_3352270 := by exact prefixLift 3352270
  have htrace : WordTrace (prefixWord ++ tailWord_3352270) baseStart_3352270 baseEnd_3352270 := by
    simpa [prefixWord, tailWord_3352270, baseEnd_3352270] using wordTrace_append hprefix tailTrace_3352270
  have hstable : (prefixWord ++ tailWord_3352270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352270).length < 2 ^ (prefixWord ++ tailWord_3352270).sum := by decide
  have hdescent : baseEnd_3352270 < baseStart_3352270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352300 : List Nat := [2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 3]
def baseStart_3352300 : Nat := 118140960795 + 3352300 * 2 ^ 59
def prefixEnd_3352300 : Nat := 4983230072969 + 3 ^ 40 * 3352300 * 2
def baseEnd_3352300 : Nat := 1721341198067339344533059

theorem tailTrace_3352300 : CollatzResearch.WordTrace tailWord_3352300 prefixEnd_3352300 1721341198067339344533059 := by
  unfold tailWord_3352300
  simp only [CollatzResearch.WordTrace]
  refine ⟨61134212877598551051943177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81512283836798068069257569 61134212877598551051943177)
  ·
    refine ⟨45850659658198913288957383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61134212877598551051943177 45850659658198913288957383)
    ·
      refine ⟨68775989487298369933436075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45850659658198913288957383 68775989487298369933436075)
      ·
        refine ⟨103163984230947554900154113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68775989487298369933436075 103163984230947554900154113)
        ·
          refine ⟨77372988173210666175115585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103163984230947554900154113 77372988173210666175115585)
          ·
            refine ⟨58029741129907999631336689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77372988173210666175115585 58029741129907999631336689)
            ·
              refine ⟨43522305847430999723502517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58029741129907999631336689 43522305847430999723502517)
              ·
                refine ⟨4080216173196656224078361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43522305847430999723502517 4080216173196656224078361)
                ·
                  refine ⟨3060162129897492168058771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080216173196656224078361 3060162129897492168058771)
                  ·
                    refine ⟨4590243194846238252088157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060162129897492168058771 4590243194846238252088157)
                    ·
                      refine ⟨1721341198067339344533059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590243194846238252088157 1721341198067339344533059)
                      ·
                        rfl

theorem cell23_3352300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_3352300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352300 prefixEnd_3352300 := by exact prefixLift 3352300
  have htrace : WordTrace (prefixWord ++ tailWord_3352300) baseStart_3352300 baseEnd_3352300 := by
    simpa [prefixWord, tailWord_3352300, baseEnd_3352300] using wordTrace_append hprefix tailTrace_3352300
  have hstable : (prefixWord ++ tailWord_3352300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352300).length < 2 ^ (prefixWord ++ tailWord_3352300).sum := by decide
  have hdescent : baseEnd_3352300 < baseStart_3352300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352318 : List Nat := [4, 2, 2, 1, 3, 2, 1, 3, 1, 2, 2]
def baseStart_3352318 : Nat := 118140960795 + 3352318 * 2 ^ 59
def prefixEnd_3352318 : Nat := 4983230072969 + 3 ^ 40 * 3352318 * 2
def baseEnd_3352318 : Nat := 1721350440719120274107977

theorem tailTrace_3352318 : CollatzResearch.WordTrace tailWord_3352318 prefixEnd_3352318 1721350440719120274107977 := by
  unfold tailWord_3352318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15283635283641486397255201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81512721512754594118694405 15283635283641486397255201)
  ·
    refine ⟨11462726462731114797941401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15283635283641486397255201 11462726462731114797941401)
    ·
      refine ⟨8597044847048336098456051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11462726462731114797941401 8597044847048336098456051)
      ·
        refine ⟨12895567270572504147684077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597044847048336098456051 12895567270572504147684077)
        ·
          refine ⟨4835837726464689055381529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12895567270572504147684077 4835837726464689055381529)
          ·
            refine ⟨3626878294848516791536147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835837726464689055381529 3626878294848516791536147)
            ·
              refine ⟨5440317442272775187304221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626878294848516791536147 5440317442272775187304221)
              ·
                refine ⟨2040119040852290695239083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5440317442272775187304221 2040119040852290695239083)
                ·
                  refine ⟨3060178561278436042858625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040119040852290695239083 3060178561278436042858625)
                  ·
                    refine ⟨2295133920958827032143969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3060178561278436042858625 2295133920958827032143969)
                    ·
                      refine ⟨1721350440719120274107977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295133920958827032143969 1721350440719120274107977)
                      ·
                        rfl

theorem cell23_3352318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_3352318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352318 prefixEnd_3352318 := by exact prefixLift 3352318
  have htrace : WordTrace (prefixWord ++ tailWord_3352318) baseStart_3352318 baseEnd_3352318 := by
    simpa [prefixWord, tailWord_3352318, baseEnd_3352318] using wordTrace_append hprefix tailTrace_3352318
  have hstable : (prefixWord ++ tailWord_3352318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352318).length < 2 ^ (prefixWord ++ tailWord_3352318).sum := by decide
  have hdescent : baseEnd_3352318 < baseStart_3352318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352374 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2]
def baseStart_3352374 : Nat := 118140960795 + 3352374 * 2 ^ 59
def prefixEnd_3352374 : Nat := 4983230072969 + 3 ^ 40 * 3352374 * 2
def baseEnd_3352374 : Nat := 1721379195635772055007719

theorem tailTrace_3352374 : CollatzResearch.WordTrace tailWord_3352374 prefixEnd_3352374 1721379195635772055007719 := by
  unfold tailWord_3352374
  simp only [CollatzResearch.WordTrace]
  refine ⟨7641945297308063296380011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81514083171286008494720117 7641945297308063296380011)
  ·
    refine ⟨11462917945962094944570017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7641945297308063296380011 11462917945962094944570017)
    ·
      refine ⟨8597188459471571208427513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11462917945962094944570017 8597188459471571208427513)
      ·
        refine ⟨6447891344603678406320635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8597188459471571208427513 6447891344603678406320635)
        ·
          refine ⟨9671837016905517609480953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6447891344603678406320635 9671837016905517609480953)
          ·
            refine ⟨7253877762679138207110715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9671837016905517609480953 7253877762679138207110715)
            ·
              refine ⟨10880816644018707310666073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253877762679138207110715 10880816644018707310666073)
              ·
                refine ⟨8160612483014030482999555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10880816644018707310666073 8160612483014030482999555)
                ·
                  refine ⟨12240918724521045724499333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8160612483014030482999555 12240918724521045724499333)
                  ·
                    refine ⟨2295172260847696073343625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12240918724521045724499333 2295172260847696073343625)
                    ·
                      refine ⟨1721379195635772055007719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295172260847696073343625 1721379195635772055007719)
                      ·
                        rfl

theorem cell23_3352374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_3352374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352374 prefixEnd_3352374 := by exact prefixLift 3352374
  have htrace : WordTrace (prefixWord ++ tailWord_3352374) baseStart_3352374 baseEnd_3352374 := by
    simpa [prefixWord, tailWord_3352374, baseEnd_3352374] using wordTrace_append hprefix tailTrace_3352374
  have hstable : (prefixWord ++ tailWord_3352374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352374).length < 2 ^ (prefixWord ++ tailWord_3352374).sum := by decide
  have hdescent : baseEnd_3352374 < baseStart_3352374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352393 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_3352393 : Nat := 118140960795 + 3352393 * 2 ^ 59
def prefixEnd_3352393 : Nat := 4983230072969 + 3 ^ 40 * 3352393 * 2
def baseEnd_3352393 : Nat := 573796317256069160223377

theorem tailTrace_3352393 : CollatzResearch.WordTrace tailWord_3352393 prefixEnd_3352393 573796317256069160223377 := by
  unfold tailWord_3352393
  simp only [CollatzResearch.WordTrace]
  refine ⟨122271817743860178987021833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81514545162573452658014555 122271817743860178987021833)
  ·
    refine ⟨91703863307895134240266375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122271817743860178987021833 91703863307895134240266375)
    ·
      refine ⟨137555794961842701360399563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91703863307895134240266375 137555794961842701360399563)
      ·
        refine ⟨206333692442764052040599345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137555794961842701360399563 206333692442764052040599345)
        ·
          refine ⟨154750269332073039030449509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206333692442764052040599345 154750269332073039030449509)
          ·
            refine ⟨29015675499763694818209283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154750269332073039030449509 29015675499763694818209283)
            ·
              refine ⟨43523513249645542227313925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29015675499763694818209283 43523513249645542227313925)
              ·
                refine ⟨8160658734308539167621361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43523513249645542227313925 8160658734308539167621361)
                ·
                  refine ⟨6120494050731404375716021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8160658734308539167621361 6120494050731404375716021)
                  ·
                    refine ⟨573796317256069160223377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6120494050731404375716021 573796317256069160223377)
                    ·
                      rfl

theorem cell23_3352393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_3352393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352393 prefixEnd_3352393 := by exact prefixLift 3352393
  have htrace : WordTrace (prefixWord ++ tailWord_3352393) baseStart_3352393 baseEnd_3352393 := by
    simpa [prefixWord, tailWord_3352393, baseEnd_3352393] using wordTrace_append hprefix tailTrace_3352393
  have hstable : (prefixWord ++ tailWord_3352393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352393).length < 2 ^ (prefixWord ++ tailWord_3352393).sum := by decide
  have hdescent : baseEnd_3352393 < baseStart_3352393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352453 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 8]
def baseStart_3352453 : Nat := 118140960795 + 3352453 * 2 ^ 59
def prefixEnd_3352453 : Nat := 4983230072969 + 3 ^ 40 * 3352453 * 2
def baseEnd_3352453 : Nat := 191268862289719693991095

theorem tailTrace_3352453 : CollatzResearch.WordTrace tailWord_3352453 prefixEnd_3352453 191268862289719693991095 := by
  unfold tailWord_3352453
  simp only [CollatzResearch.WordTrace]
  refine ⟨122274006123642809234206013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81516004082428539489470675 122274006123642809234206013)
  ·
    refine ⟨45852752296366053462827255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122274006123642809234206013 45852752296366053462827255)
    ·
      refine ⟨68779128444549080194240883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45852752296366053462827255 68779128444549080194240883)
      ·
        refine ⟨103168692666823620291361325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68779128444549080194240883 103168692666823620291361325)
        ·
          refine ⟨38688259750058857609260497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103168692666823620291361325 38688259750058857609260497)
          ·
            refine ⟨29016194812544143206945373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38688259750058857609260497 29016194812544143206945373)
            ·
              refine ⟨10881073054704053702604515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29016194812544143206945373 10881073054704053702604515)
              ·
                refine ⟨16321609582056080553906773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881073054704053702604515 16321609582056080553906773)
                ·
                  refine ⟨191268862289719693991095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16321609582056080553906773 191268862289719693991095)
                  ·
                    rfl

theorem cell23_3352453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_3352453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352453 prefixEnd_3352453 := by exact prefixLift 3352453
  have htrace : WordTrace (prefixWord ++ tailWord_3352453) baseStart_3352453 baseEnd_3352453 := by
    simpa [prefixWord, tailWord_3352453, baseEnd_3352453] using wordTrace_append hprefix tailTrace_3352453
  have hstable : (prefixWord ++ tailWord_3352453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352453).length < 2 ^ (prefixWord ++ tailWord_3352453).sum := by decide
  have hdescent : baseEnd_3352453 < baseStart_3352453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352457 : List Nat := [1, 2, 1, 1, 5, 1, 1, 6, 1, 4]
def baseStart_3352457 : Nat := 118140960795 + 3352457 * 2 ^ 59
def prefixEnd_3352457 : Nat := 4983230072969 + 3 ^ 40 * 3352457 * 2
def baseEnd_3352457 : Nat := 573807271510031743423279

theorem tailTrace_3352457 : CollatzResearch.WordTrace tailWord_3352457 prefixEnd_3352457 573807271510031743423279 := by
  unfold tailWord_3352457
  simp only [CollatzResearch.WordTrace]
  refine ⟨122274152015628317917351625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81516101343752211944901083 122274152015628317917351625)
  ·
    refine ⟨91705614011721238438013719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122274152015628317917351625 91705614011721238438013719)
    ·
      refine ⟨137558421017581857657020579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91705614011721238438013719 137558421017581857657020579)
      ·
        refine ⟨206337631526372786485530869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137558421017581857657020579 206337631526372786485530869)
        ·
          refine ⟨19344152955597448733018519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206337631526372786485530869 19344152955597448733018519)
          ·
            refine ⟨29016229433396173099527779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19344152955597448733018519 29016229433396173099527779)
            ·
              refine ⟨43524344150094259649291669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29016229433396173099527779 43524344150094259649291669)
              ·
                refine ⟨2040203632035668421060547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43524344150094259649291669 2040203632035668421060547)
                ·
                  refine ⟨3060305448053502631590821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040203632035668421060547 3060305448053502631590821)
                  ·
                    refine ⟨573807271510031743423279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060305448053502631590821 573807271510031743423279)
                    ·
                      rfl

theorem cell23_3352457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 1, 4].length) (baseStart_3352457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352457 prefixEnd_3352457 := by exact prefixLift 3352457
  have htrace : WordTrace (prefixWord ++ tailWord_3352457) baseStart_3352457 baseEnd_3352457 := by
    simpa [prefixWord, tailWord_3352457, baseEnd_3352457] using wordTrace_append hprefix tailTrace_3352457
  have hstable : (prefixWord ++ tailWord_3352457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352457).length < 2 ^ (prefixWord ++ tailWord_3352457).sum := by decide
  have hdescent : baseEnd_3352457 < baseStart_3352457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352508 : List Nat := [2, 2, 2, 5, 1, 1, 3, 2, 1, 4]
def baseStart_3352508 : Nat := 118140960795 + 3352508 * 2 ^ 59
def prefixEnd_3352508 : Nat := 4983230072969 + 3 ^ 40 * 3352508 * 2
def baseEnd_3352508 : Nat := 573816000681158176910701

theorem tailTrace_3352508 : CollatzResearch.WordTrace tailWord_3352508 prefixEnd_3352508 573816000681158176910701 := by
  unfold tailWord_3352508
  simp only [CollatzResearch.WordTrace]
  refine ⟨61138006069221776813729089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81517341425629035751638785 61138006069221776813729089)
  ·
    refine ⟨45853504551916332610296817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61138006069221776813729089 45853504551916332610296817)
    ·
      refine ⟨34390128413937249457722613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45853504551916332610296817 34390128413937249457722613)
      ·
        refine ⟨3224074538806617136661495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34390128413937249457722613 3224074538806617136661495)
        ·
          refine ⟨4836111808209925704992243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224074538806617136661495 4836111808209925704992243)
          ·
            refine ⟨7254167712314888557488365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836111808209925704992243 7254167712314888557488365)
            ·
              refine ⟨2720312892118083209058137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7254167712314888557488365 2720312892118083209058137)
              ·
                refine ⟨2040234669088562406793603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2720312892118083209058137 2040234669088562406793603)
                ·
                  refine ⟨3060352003632843610190405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040234669088562406793603 3060352003632843610190405)
                  ·
                    refine ⟨573816000681158176910701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060352003632843610190405 573816000681158176910701)
                    ·
                      rfl

theorem cell23_3352508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_3352508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352508 prefixEnd_3352508 := by exact prefixLift 3352508
  have htrace : WordTrace (prefixWord ++ tailWord_3352508) baseStart_3352508 baseEnd_3352508 := by
    simpa [prefixWord, tailWord_3352508, baseEnd_3352508] using wordTrace_append hprefix tailTrace_3352508
  have hstable : (prefixWord ++ tailWord_3352508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352508).length < 2 ^ (prefixWord ++ tailWord_3352508).sum := by decide
  have hdescent : baseEnd_3352508 < baseStart_3352508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352534 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 3, 5]
def baseStart_3352534 : Nat := 118140960795 + 3352534 * 2 ^ 59
def prefixEnd_3352534 : Nat := 4983230072969 + 3 ^ 40 * 3352534 * 2
def baseEnd_3352534 : Nat := 573820450846830476335661

theorem tailTrace_3352534 : CollatzResearch.WordTrace tailWord_3352534 prefixEnd_3352534 573820450846830476335661 := by
  unfold tailWord_3352534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7642310027271835004244041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81517973624232906711936437 7642310027271835004244041)
  ·
    refine ⟨5731732520453876253183031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7642310027271835004244041 5731732520453876253183031)
    ·
      refine ⟨8597598780680814379774547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731732520453876253183031 8597598780680814379774547)
      ·
        refine ⟨12896398171021221569661821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597598780680814379774547 12896398171021221569661821)
        ·
          refine ⟨4836149314132958088623183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12896398171021221569661821 4836149314132958088623183)
          ·
            refine ⟨7254223971199437132934775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836149314132958088623183 7254223971199437132934775)
            ·
              refine ⟨10881335956799155699402163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254223971199437132934775 10881335956799155699402163)
              ·
                refine ⟨16322003935198733549103245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881335956799155699402163 16322003935198733549103245)
                ·
                  refine ⟨6120751475699525080913717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16322003935198733549103245 6120751475699525080913717)
                  ·
                    refine ⟨573820450846830476335661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6120751475699525080913717 573820450846830476335661)
                    ·
                      rfl

theorem cell23_3352534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_3352534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352534 prefixEnd_3352534 := by exact prefixLift 3352534
  have htrace : WordTrace (prefixWord ++ tailWord_3352534) baseStart_3352534 baseEnd_3352534 := by
    simpa [prefixWord, tailWord_3352534, baseEnd_3352534] using wordTrace_append hprefix tailTrace_3352534
  have hstable : (prefixWord ++ tailWord_3352534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352534).length < 2 ^ (prefixWord ++ tailWord_3352534).sum := by decide
  have hdescent : baseEnd_3352534 < baseStart_3352534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352537 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_3352537 : Nat := 118140960795 + 3352537 * 2 ^ 59
def prefixEnd_3352537 : Nat := 4983230072969 + 3 ^ 40 * 3352537 * 2
def baseEnd_3352537 : Nat := 1721462892982454917269469

theorem tailTrace_3352537 : CollatzResearch.WordTrace tailWord_3352537 prefixEnd_3352537 1721462892982454917269469 := by
  unfold tailWord_3352537
  simp only [CollatzResearch.WordTrace]
  refine ⟨122277069855338491580263865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81518046570225661053509243 122277069855338491580263865)
  ·
    refine ⟨91707802391503868685197899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122277069855338491580263865 91707802391503868685197899)
    ·
      refine ⟨137561703587255803027796849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91707802391503868685197899 137561703587255803027796849)
      ·
        refine ⟨103171277690441852270847637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137561703587255803027796849 103171277690441852270847637)
        ·
          refine ⟨4836153641739461825195983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103171277690441852270847637 4836153641739461825195983)
          ·
            refine ⟨7254230462609192737793975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836153641739461825195983 7254230462609192737793975)
            ·
              refine ⟨10881345693913789106690963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254230462609192737793975 10881345693913789106690963)
              ·
                refine ⟨16322018540870683660036445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881345693913789106690963 16322018540870683660036445)
                ·
                  refine ⟨6120756952826506372513667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16322018540870683660036445 6120756952826506372513667)
                  ·
                    refine ⟨9181135429239759558770501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120756952826506372513667 9181135429239759558770501)
                    ·
                      refine ⟨1721462892982454917269469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9181135429239759558770501 1721462892982454917269469)
                      ·
                        rfl

theorem cell23_3352537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_3352537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352537 prefixEnd_3352537 := by exact prefixLift 3352537
  have htrace : WordTrace (prefixWord ++ tailWord_3352537) baseStart_3352537 baseEnd_3352537 := by
    simpa [prefixWord, tailWord_3352537, baseEnd_3352537] using wordTrace_append hprefix tailTrace_3352537
  have hstable : (prefixWord ++ tailWord_3352537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352537).length < 2 ^ (prefixWord ++ tailWord_3352537).sum := by decide
  have hdescent : baseEnd_3352537 < baseStart_3352537 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352541 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_3352541 : Nat := 118140960795 + 3352541 * 2 ^ 59
def prefixEnd_3352541 : Nat := 4983230072969 + 3 ^ 40 * 3352541 * 2
def baseEnd_3352541 : Nat := 1721464946905072901619451

theorem tailTrace_3352541 : CollatzResearch.WordTrace tailWord_3352541 prefixEnd_3352541 1721464946905072901619451 := by
  unfold tailWord_3352541
  simp only [CollatzResearch.WordTrace]
  refine ⟨122277215747324000263409477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81518143831549333508939651 122277215747324000263409477)
  ·
    refine ⟨22926977952623250049389277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122277215747324000263409477 22926977952623250049389277)
    ·
      refine ⟨8597616732233718768520979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22926977952623250049389277 8597616732233718768520979)
      ·
        refine ⟨12896425098350578152781469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8597616732233718768520979 12896425098350578152781469)
        ·
          refine ⟨4836159411881466807293051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12896425098350578152781469 4836159411881466807293051)
          ·
            refine ⟨7254239117822200210939577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836159411881466807293051 7254239117822200210939577)
            ·
              refine ⟨5440679338366650158204683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7254239117822200210939577 5440679338366650158204683)
              ·
                refine ⟨8161019007549975237307025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440679338366650158204683 8161019007549975237307025)
                ·
                  refine ⟨6120764255662481427980269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161019007549975237307025 6120764255662481427980269)
                  ·
                    refine ⟨2295286595873430535492601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6120764255662481427980269 2295286595873430535492601)
                    ·
                      refine ⟨1721464946905072901619451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295286595873430535492601 1721464946905072901619451)
                      ·
                        rfl

theorem cell23_3352541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_3352541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352541 prefixEnd_3352541 := by exact prefixLift 3352541
  have htrace : WordTrace (prefixWord ++ tailWord_3352541) baseStart_3352541 baseEnd_3352541 := by
    simpa [prefixWord, tailWord_3352541, baseEnd_3352541] using wordTrace_append hprefix tailTrace_3352541
  have hstable : (prefixWord ++ tailWord_3352541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352541).length < 2 ^ (prefixWord ++ tailWord_3352541).sum := by decide
  have hdescent : baseEnd_3352541 < baseStart_3352541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352554 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_3352554 : Nat := 118140960795 + 3352554 * 2 ^ 59
def prefixEnd_3352554 : Nat := 4983230072969 + 3 ^ 40 * 3352554 * 2
def baseEnd_3352554 : Nat := 1721471622153581350756891

theorem tailTrace_3352554 : CollatzResearch.WordTrace tailWord_3352554 prefixEnd_3352554 1721471622153581350756891 := by
  unfold tailWord_3352554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30569422474069225870908179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81518459930851268989088477 30569422474069225870908179)
  ·
    refine ⟨45854133711103838806362269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30569422474069225870908179 45854133711103838806362269)
    ·
      refine ⟨17195300141663939552385851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45854133711103838806362269 17195300141663939552385851)
      ·
        refine ⟨25792950212495909328578777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17195300141663939552385851 25792950212495909328578777)
        ·
          refine ⟨19344712659371931996434083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25792950212495909328578777 19344712659371931996434083)
          ·
            refine ⟨29017068989057897994651125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19344712659371931996434083 29017068989057897994651125)
            ·
              refine ⟨2720350217724177936998543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29017068989057897994651125 2720350217724177936998543)
              ·
                refine ⟨4080525326586266905497815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720350217724177936998543 4080525326586266905497815)
                ·
                  refine ⟨6120787989879400358246723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4080525326586266905497815 6120787989879400358246723)
                  ·
                    refine ⟨9181181984819100537370085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6120787989879400358246723 9181181984819100537370085)
                    ·
                      refine ⟨1721471622153581350756891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9181181984819100537370085 1721471622153581350756891)
                      ·
                        rfl

theorem cell23_3352554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_3352554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352554 prefixEnd_3352554 := by exact prefixLift 3352554
  have htrace : WordTrace (prefixWord ++ tailWord_3352554) baseStart_3352554 baseEnd_3352554 := by
    simpa [prefixWord, tailWord_3352554, baseEnd_3352554] using wordTrace_append hprefix tailTrace_3352554
  have hstable : (prefixWord ++ tailWord_3352554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352554).length < 2 ^ (prefixWord ++ tailWord_3352554).sum := by decide
  have hdescent : baseEnd_3352554 < baseStart_3352554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352574 : List Nat := [4, 2, 2, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3352574 : Nat := 118140960795 + 3352574 * 2 ^ 59
def prefixEnd_3352574 : Nat := 4983230072969 + 3 ^ 40 * 3352574 * 2
def baseEnd_3352574 : Nat := 1721481891766671272506799

theorem tailTrace_3352574 : CollatzResearch.WordTrace tailWord_3352574 prefixEnd_3352574 1721481891766671272506799 := by
  unfold tailWord_3352574
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284802419525555862420097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81518946237469631266240517 15284802419525555862420097)
  ·
    refine ⟨11463601814644166896815073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15284802419525555862420097 11463601814644166896815073)
    ·
      refine ⟨8597701360983125172611305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11463601814644166896815073 8597701360983125172611305)
      ·
        refine ⟨6448276020737343879458479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8597701360983125172611305 6448276020737343879458479)
        ·
          refine ⟨9672414031106015819187719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448276020737343879458479 9672414031106015819187719)
          ·
            refine ⟨14508621046659023728781579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9672414031106015819187719 14508621046659023728781579)
            ·
              refine ⟨21762931569988535593172369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14508621046659023728781579 21762931569988535593172369)
              ·
                refine ⟨16322198677491401694879277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21762931569988535593172369 16322198677491401694879277)
                ·
                  refine ⟨6120824504059275635579729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16322198677491401694879277 6120824504059275635579729)
                  ·
                    refine ⟨4590618378044456726684797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6120824504059275635579729 4590618378044456726684797)
                    ·
                      refine ⟨1721481891766671272506799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590618378044456726684797 1721481891766671272506799)
                      ·
                        rfl

theorem cell23_3352574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3352574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352574 prefixEnd_3352574 := by exact prefixLift 3352574
  have htrace : WordTrace (prefixWord ++ tailWord_3352574) baseStart_3352574 baseEnd_3352574 := by
    simpa [prefixWord, tailWord_3352574, baseEnd_3352574] using wordTrace_append hprefix tailTrace_3352574
  have hstable : (prefixWord ++ tailWord_3352574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352574).length < 2 ^ (prefixWord ++ tailWord_3352574).sum := by decide
  have hdescent : baseEnd_3352574 < baseStart_3352574 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352587 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3]
def baseStart_3352587 : Nat := 118140960795 + 3352587 * 2 ^ 59
def prefixEnd_3352587 : Nat := 4983230072969 + 3 ^ 40 * 3352587 * 2
def baseEnd_3352587 : Nat := 1721488567015179721644239

theorem tailTrace_3352587 : CollatzResearch.WordTrace tailWord_3352587 prefixEnd_3352587 1721488567015179721644239 := by
  unfold tailWord_3352587
  simp only [CollatzResearch.WordTrace]
  refine ⟨122278893505157350119584015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81519262336771566746389343 122278893505157350119584015)
  ·
    refine ⟨183418340257736025179376023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122278893505157350119584015 183418340257736025179376023)
    ·
      refine ⟨275127510386604037769064035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183418340257736025179376023 275127510386604037769064035)
      ·
        refine ⟨412691265579906056653596053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275127510386604037769064035 412691265579906056653596053)
        ·
          refine ⟨19344903074058096405637315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 412691265579906056653596053 19344903074058096405637315)
          ·
            refine ⟨29017354611087144608455973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19344903074058096405637315 29017354611087144608455973)
            ·
              refine ⟨5440753989578839614085495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29017354611087144608455973 5440753989578839614085495)
              ·
                refine ⟨8161130984368259421128243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440753989578839614085495 8161130984368259421128243)
                ·
                  refine ⟨12241696476552389131692365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8161130984368259421128243 12241696476552389131692365)
                  ·
                    refine ⟨4590636178707145924384637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12241696476552389131692365 4590636178707145924384637)
                    ·
                      refine ⟨1721488567015179721644239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590636178707145924384637 1721488567015179721644239)
                      ·
                        rfl

theorem cell23_3352587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 3].length) (baseStart_3352587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352587 prefixEnd_3352587 := by exact prefixLift 3352587
  have htrace : WordTrace (prefixWord ++ tailWord_3352587) baseStart_3352587 baseEnd_3352587 := by
    simpa [prefixWord, tailWord_3352587, baseEnd_3352587] using wordTrace_append hprefix tailTrace_3352587
  have hstable : (prefixWord ++ tailWord_3352587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352587).length < 2 ^ (prefixWord ++ tailWord_3352587).sum := by decide
  have hdescent : baseEnd_3352587 < baseStart_3352587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352590 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3352590 : Nat := 118140960795 + 3352590 * 2 ^ 59
def prefixEnd_3352590 : Nat := 4983230072969 + 3 ^ 40 * 3352590 * 2
def baseEnd_3352590 : Nat := 573830035819047736635575

theorem tailTrace_3352590 : CollatzResearch.WordTrace tailWord_3352590 prefixEnd_3352590 573830035819047736635575 := by
  unfold tailWord_3352590
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284875365518310203992903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81519335282764321087962149 15284875365518310203992903)
  ·
    refine ⟨22927313048277465305989355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15284875365518310203992903 22927313048277465305989355)
    ·
      refine ⟨34390969572416197958984033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22927313048277465305989355 34390969572416197958984033)
      ·
        refine ⟨25793227179312148469238025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34390969572416197958984033 25793227179312148469238025)
        ·
          refine ⟨19344920384484111351928519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25793227179312148469238025 19344920384484111351928519)
          ·
            refine ⟨29017380576726167027892779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19344920384484111351928519 29017380576726167027892779)
            ·
              refine ⟨43526070865089250541839169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29017380576726167027892779 43526070865089250541839169)
              ·
                refine ⟨32644553148816937906379377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43526070865089250541839169 32644553148816937906379377)
                ·
                  refine ⟨24483414861612703429784533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32644553148816937906379377 24483414861612703429784533)
                  ·
                    refine ⟨573830035819047736635575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24483414861612703429784533 573830035819047736635575)
                    ·
                      rfl

theorem cell23_3352590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3352590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352590 prefixEnd_3352590 := by exact prefixLift 3352590
  have htrace : WordTrace (prefixWord ++ tailWord_3352590) baseStart_3352590 baseEnd_3352590 := by
    simpa [prefixWord, tailWord_3352590, baseEnd_3352590] using wordTrace_append hprefix tailTrace_3352590
  have hstable : (prefixWord ++ tailWord_3352590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352590).length < 2 ^ (prefixWord ++ tailWord_3352590).sum := by decide
  have hdescent : baseEnd_3352590 < baseStart_3352590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352600 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3352600 : Nat := 118140960795 + 3352600 * 2 ^ 59
def prefixEnd_3352600 : Nat := 4983230072969 + 3 ^ 40 * 3352600 * 2
def baseEnd_3352600 : Nat := 1721495242263688170781679

theorem tailTrace_3352600 : CollatzResearch.WordTrace tailWord_3352600 prefixEnd_3352600 1721495242263688170781679 := by
  unfold tailWord_3352600
  simp only [CollatzResearch.WordTrace]
  refine ⟨61139683827055126669903627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81519578436073502226538169 61139683827055126669903627)
  ·
    refine ⟨91709525740582690004855441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61139683827055126669903627 91709525740582690004855441)
    ·
      refine ⟨68782144305437017503641581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91709525740582690004855441 68782144305437017503641581)
      ·
        refine ⟨25793304114538881563865593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68782144305437017503641581 25793304114538881563865593)
        ·
          refine ⟨19344978085904161172899195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25793304114538881563865593 19344978085904161172899195)
          ·
            refine ⟨29017467128856241759348793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19344978085904161172899195 29017467128856241759348793)
            ·
              refine ⟨21763100346642181319511595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29017467128856241759348793 21763100346642181319511595)
              ·
                refine ⟨32644650519963271979267393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21763100346642181319511595 32644650519963271979267393)
                ·
                  refine ⟨24483487889972453984450545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32644650519963271979267393 24483487889972453984450545)
                  ·
                    refine ⟨18362615917479340488337909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24483487889972453984450545 18362615917479340488337909)
                    ·
                      refine ⟨1721495242263688170781679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18362615917479340488337909 1721495242263688170781679)
                      ·
                        rfl

theorem cell23_3352600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3352600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352600 prefixEnd_3352600 := by exact prefixLift 3352600
  have htrace : WordTrace (prefixWord ++ tailWord_3352600) baseStart_3352600 baseEnd_3352600 := by
    simpa [prefixWord, tailWord_3352600, baseEnd_3352600] using wordTrace_append hprefix tailTrace_3352600
  have hstable : (prefixWord ++ tailWord_3352600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352600).length < 2 ^ (prefixWord ++ tailWord_3352600).sum := by decide
  have hdescent : baseEnd_3352600 < baseStart_3352600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352627 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 3, 4, 2]
def baseStart_3352627 : Nat := 118140960795 + 3352627 * 2 ^ 59
def prefixEnd_3352627 : Nat := 4983230072969 + 3 ^ 40 * 3352627 * 2
def baseEnd_3352627 : Nat := 1721509106241359565144055

theorem tailTrace_3352627 : CollatzResearch.WordTrace tailWord_3352627 prefixEnd_3352627 1721509106241359565144055 := by
  unfold tailWord_3352627
  simp only [CollatzResearch.WordTrace]
  refine ⟨122280352425012436951040135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81520234950008291300693423 122280352425012436951040135)
  ·
    refine ⟨183420528637518655426560203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122280352425012436951040135 183420528637518655426560203)
    ·
      refine ⟨275130792956277983139840305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183420528637518655426560203 275130792956277983139840305)
      ·
        refine ⟨206348094717208487354880229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275130792956277983139840305 206348094717208487354880229)
        ·
          refine ⟨38690267759476591379040043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206348094717208487354880229 38690267759476591379040043)
          ·
            refine ⟨58035401639214887068560065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38690267759476591379040043 58035401639214887068560065)
            ·
              refine ⟨43526551229411165301420049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58035401639214887068560065 43526551229411165301420049)
              ·
                refine ⟨32644913422058373976065037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43526551229411165301420049 32644913422058373976065037)
                ·
                  refine ⟨12241842533271890241024389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32644913422058373976065037 12241842533271890241024389)
                  ·
                    refine ⟨2295345474988479420192073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12241842533271890241024389 2295345474988479420192073)
                    ·
                      refine ⟨1721509106241359565144055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295345474988479420192073 1721509106241359565144055)
                      ·
                        rfl

theorem cell23_3352627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 3, 4, 2].length) (baseStart_3352627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352627 prefixEnd_3352627 := by exact prefixLift 3352627
  have htrace : WordTrace (prefixWord ++ tailWord_3352627) baseStart_3352627 baseEnd_3352627 := by
    simpa [prefixWord, tailWord_3352627, baseEnd_3352627] using wordTrace_append hprefix tailTrace_3352627
  have hstable : (prefixWord ++ tailWord_3352627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352627).length < 2 ^ (prefixWord ++ tailWord_3352627).sum := by decide
  have hdescent : baseEnd_3352627 < baseStart_3352627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352638 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3352638 : Nat := 118140960795 + 3352638 * 2 ^ 59
def prefixEnd_3352638 : Nat := 4983230072969 + 3 ^ 40 * 3352638 * 2
def baseEnd_3352638 : Nat := 1721514754528559022106505

theorem tailTrace_3352638 : CollatzResearch.WordTrace tailWord_3352638 prefixEnd_3352638 1721514754528559022106505 := by
  unfold tailWord_3352638
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285094203496573228711321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81520502418648390553127045 15285094203496573228711321)
  ·
    refine ⟨11463820652622429921533491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15285094203496573228711321 11463820652622429921533491)
    ·
      refine ⟨17195730978933644882300237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11463820652622429921533491 17195730978933644882300237)
      ·
        refine ⟨6448399117100116830862589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17195730978933644882300237 6448399117100116830862589)
        ·
          refine ⟨2418149668912543811573471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6448399117100116830862589 2418149668912543811573471)
          ·
            refine ⟨3627224503368815717360207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418149668912543811573471 3627224503368815717360207)
            ·
              refine ⟨5440836755053223576040311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3627224503368815717360207 5440836755053223576040311)
              ·
                refine ⟨8161255132579835364060467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440836755053223576040311 8161255132579835364060467)
                ·
                  refine ⟨12241882698869753046090701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8161255132579835364060467 12241882698869753046090701)
                  ·
                    refine ⟨4590706012076157392284013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12241882698869753046090701 4590706012076157392284013)
                    ·
                      refine ⟨1721514754528559022106505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590706012076157392284013 1721514754528559022106505)
                      ·
                        rfl

theorem cell23_3352638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3352638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352638 prefixEnd_3352638 := by exact prefixLift 3352638
  have htrace : WordTrace (prefixWord ++ tailWord_3352638) baseStart_3352638 baseEnd_3352638 := by
    simpa [prefixWord, tailWord_3352638, baseEnd_3352638] using wordTrace_append hprefix tailTrace_3352638
  have hstable : (prefixWord ++ tailWord_3352638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352638).length < 2 ^ (prefixWord ++ tailWord_3352638).sum := by decide
  have hdescent : baseEnd_3352638 < baseStart_3352638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352714 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3352714 : Nat := 118140960795 + 3352714 * 2 ^ 59
def prefixEnd_3352714 : Nat := 4983230072969 + 3 ^ 40 * 3352714 * 2
def baseEnd_3352714 : Nat := 573851259686100241585385

theorem tailTrace_3352714 : CollatzResearch.WordTrace tailWord_3352714 prefixEnd_3352714 573851259686100241585385 := by
  unfold tailWord_3352714
  simp only [CollatzResearch.WordTrace]
  refine ⟨30570881393924312702364299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81522350383798167206304797 30570881393924312702364299)
  ·
    refine ⟨45856322090886469053546449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30570881393924312702364299 45856322090886469053546449)
    ·
      refine ⟨34392241568164851790159837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45856322090886469053546449 34392241568164851790159837)
      ·
        refine ⟨12897090588061819421309939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34392241568164851790159837 12897090588061819421309939)
        ·
          refine ⟨19345635882092729131964909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897090588061819421309939 19345635882092729131964909)
          ·
            refine ⟨7254613455784773424486841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19345635882092729131964909 7254613455784773424486841)
            ·
              refine ⟨5440960091838580068365131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7254613455784773424486841 5440960091838580068365131)
              ·
                refine ⟨8161440137757870102547697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5440960091838580068365131 8161440137757870102547697)
                ·
                  refine ⟨6121080103318402576910773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8161440137757870102547697 6121080103318402576910773)
                  ·
                    refine ⟨573851259686100241585385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6121080103318402576910773 573851259686100241585385)
                    ·
                      rfl

theorem cell23_3352714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3352714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352714 prefixEnd_3352714 := by exact prefixLift 3352714
  have htrace : WordTrace (prefixWord ++ tailWord_3352714) baseStart_3352714 baseEnd_3352714 := by
    simpa [prefixWord, tailWord_3352714, baseEnd_3352714] using wordTrace_append hprefix tailTrace_3352714
  have hstable : (prefixWord ++ tailWord_3352714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352714).length < 2 ^ (prefixWord ++ tailWord_3352714).sum := by decide
  have hdescent : baseEnd_3352714 < baseStart_3352714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352801 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_3352801 : Nat := 118140960795 + 3352801 * 2 ^ 59
def prefixEnd_3352801 : Nat := 4983230072969 + 3 ^ 40 * 3352801 * 2
def baseEnd_3352801 : Nat := 1721598451875241884368255

theorem tailTrace_3352801 : CollatzResearch.WordTrace tailWord_3352801 prefixEnd_3352801 1721598451875241884368255 := by
  unfold tailWord_3352801
  simp only [CollatzResearch.WordTrace]
  refine ⟨122286698726382064667874257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81524465817588043111916171 122286698726382064667874257)
  ·
    refine ⟨91715024044786548500905693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122286698726382064667874257 91715024044786548500905693)
    ·
      refine ⟨34393134016794955687839635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91715024044786548500905693 34393134016794955687839635)
      ·
        refine ⟨51589701025192433531759453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34393134016794955687839635 51589701025192433531759453)
        ·
          refine ⟨19346137884447162574409795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51589701025192433531759453 19346137884447162574409795)
          ·
            refine ⟨29019206826670743861614693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19346137884447162574409795 29019206826670743861614693)
            ·
              refine ⟨5441101280000764474052755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29019206826670743861614693 5441101280000764474052755)
              ·
                refine ⟨8161651920001146711079133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441101280000764474052755 8161651920001146711079133)
                ·
                  refine ⟨3060619470000430016654675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8161651920001146711079133 3060619470000430016654675)
                  ·
                    refine ⟨4590929205000645024982013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060619470000430016654675 4590929205000645024982013)
                    ·
                      refine ⟨1721598451875241884368255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590929205000645024982013 1721598451875241884368255)
                      ·
                        rfl

theorem cell23_3352801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_3352801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352801 prefixEnd_3352801 := by exact prefixLift 3352801
  have htrace : WordTrace (prefixWord ++ tailWord_3352801) baseStart_3352801 baseEnd_3352801 := by
    simpa [prefixWord, tailWord_3352801, baseEnd_3352801] using wordTrace_append hprefix tailTrace_3352801
  have hstable : (prefixWord ++ tailWord_3352801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352801).length < 2 ^ (prefixWord ++ tailWord_3352801).sum := by decide
  have hdescent : baseEnd_3352801 < baseStart_3352801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3]
def baseStart_3352827 : Nat := 118140960795 + 3352827 * 2 ^ 59
def prefixEnd_3352827 : Nat := 4983230072969 + 3 ^ 40 * 3352827 * 2
def baseEnd_3352827 : Nat := 1721611802372258782643135

theorem tailTrace_3352827 : CollatzResearch.WordTrace tailWord_3352827 prefixEnd_3352827 1721611802372258782643135 := by
  unfold tailWord_3352827
  simp only [CollatzResearch.WordTrace]
  refine ⟨122287647024287871108320735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81525098016191914072213823 122287647024287871108320735)
  ·
    refine ⟨183431470536431806662481103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122287647024287871108320735 183431470536431806662481103)
    ·
      refine ⟨275147205804647709993721655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183431470536431806662481103 275147205804647709993721655)
      ·
        refine ⟨412720808706971564990582483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275147205804647709993721655 412720808706971564990582483)
        ·
          refine ⟨619081213060457347485873725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412720808706971564990582483 619081213060457347485873725)
          ·
            refine ⟨232155454897671505307202647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619081213060457347485873725 232155454897671505307202647)
            ·
              refine ⟨348233182346507257960803971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232155454897671505307202647 348233182346507257960803971)
              ·
                refine ⟨522349773519760886941205957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348233182346507257960803971 522349773519760886941205957)
                ·
                  refine ⟨97940582534955166301476117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 522349773519760886941205957 97940582534955166301476117)
                  ·
                    refine ⟨4590964806326023420381693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 97940582534955166301476117 4590964806326023420381693)
                    ·
                      refine ⟨1721611802372258782643135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4590964806326023420381693 1721611802372258782643135)
                      ·
                        rfl

theorem cell23_3352827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 3].length) (baseStart_3352827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352827 prefixEnd_3352827 := by exact prefixLift 3352827
  have htrace : WordTrace (prefixWord ++ tailWord_3352827) baseStart_3352827 baseEnd_3352827 := by
    simpa [prefixWord, tailWord_3352827, baseEnd_3352827] using wordTrace_append hprefix tailTrace_3352827
  have hstable : (prefixWord ++ tailWord_3352827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352827).length < 2 ^ (prefixWord ++ tailWord_3352827).sum := by decide
  have hdescent : baseEnd_3352827 < baseStart_3352827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352844 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 1, 1, 5]
def baseStart_3352844 : Nat := 118140960795 + 3352844 * 2 ^ 59
def prefixEnd_3352844 : Nat := 4983230072969 + 3 ^ 40 * 3352844 * 2
def baseEnd_3352844 : Nat := 1721620531543385216130557

theorem tailTrace_3352844 : CollatzResearch.WordTrace tailWord_3352844 prefixEnd_3352844 1721620531543385216130557 := by
  unfold tailWord_3352844
  simp only [CollatzResearch.WordTrace]
  refine ⟨61144133532613141505844793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81525511376817522007793057 61144133532613141505844793)
  ·
    refine ⟨45858100149459856129383595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61144133532613141505844793 45858100149459856129383595)
    ·
      refine ⟨68787150224189784194075393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45858100149459856129383595 68787150224189784194075393)
      ·
        refine ⟨51590362668142338145556545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68787150224189784194075393 51590362668142338145556545)
        ·
          refine ⟨38692772001106753609167409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51590362668142338145556545 38692772001106753609167409)
          ·
            refine ⟨29019579000830065206875557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38692772001106753609167409 29019579000830065206875557)
            ·
              refine ⟨5441171062655637226289167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29019579000830065206875557 5441171062655637226289167)
              ·
                refine ⟨8161756593983455839433751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5441171062655637226289167 8161756593983455839433751)
                ·
                  refine ⟨12242634890975183759150627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8161756593983455839433751 12242634890975183759150627)
                  ·
                    refine ⟨18363952336462775638725941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12242634890975183759150627 18363952336462775638725941)
                    ·
                      refine ⟨1721620531543385216130557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18363952336462775638725941 1721620531543385216130557)
                      ·
                        rfl

theorem cell23_3352844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_3352844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352844 prefixEnd_3352844 := by exact prefixLift 3352844
  have htrace : WordTrace (prefixWord ++ tailWord_3352844) baseStart_3352844 baseEnd_3352844 := by
    simpa [prefixWord, tailWord_3352844, baseEnd_3352844] using wordTrace_append hprefix tailTrace_3352844
  have hstable : (prefixWord ++ tailWord_3352844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352844).length < 2 ^ (prefixWord ++ tailWord_3352844).sum := by decide
  have hdescent : baseEnd_3352844 < baseStart_3352844 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352864 : List Nat := [2, 1, 1, 5, 2, 2, 2, 8]
def baseStart_3352864 : Nat := 118140960795 + 3352864 * 2 ^ 59
def prefixEnd_3352864 : Nat := 4983230072969 + 3 ^ 40 * 3352864 * 2
def baseEnd_3352864 : Nat := 63764103746536116217795

theorem tailTrace_3352864 : CollatzResearch.WordTrace tailWord_3352864 prefixEnd_3352864 63764103746536116217795 := by
  unfold tailWord_3352864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61144498262576913213708823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81525997683435884284945097 61144498262576913213708823)
  ·
    refine ⟨91716747393865369820563235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61144498262576913213708823 91716747393865369820563235)
    ·
      refine ⟨137575121090798054730844853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91716747393865369820563235 137575121090798054730844853)
      ·
        refine ⟨12897667602262317631016705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137575121090798054730844853 12897667602262317631016705)
        ·
          refine ⟨9673250701696738223262529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12897667602262317631016705 9673250701696738223262529)
          ·
            refine ⟨7254938026272553667446897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9673250701696738223262529 7254938026272553667446897)
            ·
              refine ⟨5441203519704415250585173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7254938026272553667446897 5441203519704415250585173)
              ·
                refine ⟨63764103746536116217795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5441203519704415250585173 63764103746536116217795)
                ·
                  rfl

theorem cell23_3352864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 8].length) (baseStart_3352864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352864 prefixEnd_3352864 := by exact prefixLift 3352864
  have htrace : WordTrace (prefixWord ++ tailWord_3352864) baseStart_3352864 baseEnd_3352864 := by
    simpa [prefixWord, tailWord_3352864, baseEnd_3352864] using wordTrace_append hprefix tailTrace_3352864
  have hstable : (prefixWord ++ tailWord_3352864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352864).length < 2 ^ (prefixWord ++ tailWord_3352864).sum := by decide
  have hdescent : baseEnd_3352864 < baseStart_3352864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352867 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6]
def baseStart_3352867 : Nat := 118140960795 + 3352867 * 2 ^ 59
def prefixEnd_3352867 : Nat := 4983230072969 + 3 ^ 40 * 3352867 * 2
def baseEnd_3352867 : Nat := 1721632341598438626142951

theorem tailTrace_3352867 : CollatzResearch.WordTrace tailWord_3352867 prefixEnd_3352867 1721632341598438626142951 := by
  unfold tailWord_3352867
  simp only [CollatzResearch.WordTrace]
  refine ⟨122289105944142957939776855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81526070629428638626517903 122289105944142957939776855)
  ·
    refine ⟨183433658916214436909665283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122289105944142957939776855 183433658916214436909665283)
    ·
      refine ⟨275150488374321655364497925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183433658916214436909665283 275150488374321655364497925)
      ·
        refine ⟨51590716570185310380843361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275150488374321655364497925 51590716570185310380843361)
        ·
          refine ⟨38693037427638982785632521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51590716570185310380843361 38693037427638982785632521)
          ·
            refine ⟨29019778070729237089224391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38693037427638982785632521 29019778070729237089224391)
            ·
              refine ⟨43529667106093855633836587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29019778070729237089224391 43529667106093855633836587)
              ·
                refine ⟨65294500659140783450754881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43529667106093855633836587 65294500659140783450754881)
                ·
                  refine ⟨48970875494355587588066161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65294500659140783450754881 48970875494355587588066161)
                  ·
                    refine ⟨36728156620766690691049621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48970875494355587588066161 36728156620766690691049621)
                    ·
                      refine ⟨1721632341598438626142951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36728156620766690691049621 1721632341598438626142951)
                      ·
                        rfl

theorem cell23_3352867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_3352867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352867 prefixEnd_3352867 := by exact prefixLift 3352867
  have htrace : WordTrace (prefixWord ++ tailWord_3352867) baseStart_3352867 baseEnd_3352867 := by
    simpa [prefixWord, tailWord_3352867, baseEnd_3352867] using wordTrace_append hprefix tailTrace_3352867
  have hstable : (prefixWord ++ tailWord_3352867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352867).length < 2 ^ (prefixWord ++ tailWord_3352867).sum := by decide
  have hdescent : baseEnd_3352867 < baseStart_3352867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352868 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_3352868 : Nat := 118140960795 + 3352868 * 2 ^ 59
def prefixEnd_3352868 : Nat := 4983230072969 + 3 ^ 40 * 3352868 * 2
def baseEnd_3352868 : Nat := 573877618359697707410149

theorem tailTrace_3352868 : CollatzResearch.WordTrace tailWord_3352868 prefixEnd_3352868 573877618359697707410149 := by
  unfold tailWord_3352868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61144571208569667555281629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81526094944759556740375505 61144571208569667555281629)
  ·
    refine ⟨22929214203213625333230611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61144571208569667555281629 22929214203213625333230611)
    ·
      refine ⟨34393821304820437999845917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22929214203213625333230611 34393821304820437999845917)
      ·
        refine ⟨12897682989307664249942219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34393821304820437999845917 12897682989307664249942219)
        ·
          refine ⟨19346524483961496374913329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12897682989307664249942219 19346524483961496374913329)
          ·
            refine ⟨14509893362971122281184997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19346524483961496374913329 14509893362971122281184997)
            ·
              refine ⟨2720605005557085427722187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14509893362971122281184997 2720605005557085427722187)
              ·
                refine ⟨4080907508335628141583281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720605005557085427722187 4080907508335628141583281)
                ·
                  refine ⟨3060680631251721106187461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080907508335628141583281 3060680631251721106187461)
                  ·
                    refine ⟨573877618359697707410149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060680631251721106187461 573877618359697707410149)
                    ·
                      rfl

theorem cell23_3352868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_3352868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352868 prefixEnd_3352868 := by exact prefixLift 3352868
  have htrace : WordTrace (prefixWord ++ tailWord_3352868) baseStart_3352868 baseEnd_3352868 := by
    simpa [prefixWord, tailWord_3352868, baseEnd_3352868] using wordTrace_append hprefix tailTrace_3352868
  have hstable : (prefixWord ++ tailWord_3352868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352868).length < 2 ^ (prefixWord ++ tailWord_3352868).sum := by decide
  have hdescent : baseEnd_3352868 < baseStart_3352868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352887 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_3352887 : Nat := 118140960795 + 3352887 * 2 ^ 59
def prefixEnd_3352887 : Nat := 4983230072969 + 3 ^ 40 * 3352887 * 2
def baseEnd_3352887 : Nat := 1721642611211528547892859

theorem tailTrace_3352887 : CollatzResearch.WordTrace tailWord_3352887 prefixEnd_3352887 1721642611211528547892859 := by
  unfold tailWord_3352887
  simp only [CollatzResearch.WordTrace]
  refine ⟨122289835404070501355504915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81526556936047000903669943 122289835404070501355504915)
  ·
    refine ⟨183434753106105752033257373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122289835404070501355504915 183434753106105752033257373)
    ·
      refine ⟨68788032414789657012471515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183434753106105752033257373 68788032414789657012471515)
      ·
        refine ⟨103182048622184485518707273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68788032414789657012471515 103182048622184485518707273)
        ·
          refine ⟨77386536466638364139030455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103182048622184485518707273 77386536466638364139030455)
          ·
            refine ⟨116079804699957546208545683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77386536466638364139030455 116079804699957546208545683)
            ·
              refine ⟨174119707049936319312818525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116079804699957546208545683 174119707049936319312818525)
              ·
                refine ⟨65294890143726119742306947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174119707049936319312818525 65294890143726119742306947)
                ·
                  refine ⟨97942335215589179613460421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65294890143726119742306947 97942335215589179613460421)
                  ·
                    refine ⟨18364187852922971177523829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97942335215589179613460421 18364187852922971177523829)
                    ·
                      refine ⟨1721642611211528547892859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18364187852922971177523829 1721642611211528547892859)
                      ·
                        rfl

theorem cell23_3352887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_3352887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352887 prefixEnd_3352887 := by exact prefixLift 3352887
  have htrace : WordTrace (prefixWord ++ tailWord_3352887) baseStart_3352887 baseEnd_3352887 := by
    simpa [prefixWord, tailWord_3352887, baseEnd_3352887] using wordTrace_append hprefix tailTrace_3352887
  have hstable : (prefixWord ++ tailWord_3352887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352887).length < 2 ^ (prefixWord ++ tailWord_3352887).sum := by decide
  have hdescent : baseEnd_3352887 < baseStart_3352887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352908 : List Nat := [2, 2, 1, 3, 2, 1, 4, 2, 2, 1, 3]
def baseStart_3352908 : Nat := 118140960795 + 3352908 * 2 ^ 59
def prefixEnd_3352908 : Nat := 4983230072969 + 3 ^ 40 * 3352908 * 2
def baseEnd_3352908 : Nat := 1721653394305272965730263

theorem tailTrace_3352908 : CollatzResearch.WordTrace tailWord_3352908 prefixEnd_3352908 1721653394305272965730263 := by
  unfold tailWord_3352908
  simp only [CollatzResearch.WordTrace]
  refine ⟨61145300668497210971009689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81527067557996281294679585 61145300668497210971009689)
  ·
    refine ⟨45858975501372908228257267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61145300668497210971009689 45858975501372908228257267)
    ·
      refine ⟨68788463252059362342385901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45858975501372908228257267 68788463252059362342385901)
      ·
        refine ⟨25795673719522260878394713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68788463252059362342385901 25795673719522260878394713)
        ·
          refine ⟨19346755289641695658796035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25795673719522260878394713 19346755289641695658796035)
          ·
            refine ⟨29020132934462543488194053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19346755289641695658796035 29020132934462543488194053)
            ·
              refine ⟨5441274925211726904036385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29020132934462543488194053 5441274925211726904036385)
              ·
                refine ⟨4080956193908795178027289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441274925211726904036385 4080956193908795178027289)
                ·
                  refine ⟨3060717145431596383520467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4080956193908795178027289 3060717145431596383520467)
                  ·
                    refine ⟨4591075718147394575280701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060717145431596383520467 4591075718147394575280701)
                    ·
                      refine ⟨1721653394305272965730263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4591075718147394575280701 1721653394305272965730263)
                      ·
                        rfl

theorem cell23_3352908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_3352908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352908 prefixEnd_3352908 := by exact prefixLift 3352908
  have htrace : WordTrace (prefixWord ++ tailWord_3352908) baseStart_3352908 baseEnd_3352908 := by
    simpa [prefixWord, tailWord_3352908, baseEnd_3352908] using wordTrace_append hprefix tailTrace_3352908
  have hstable : (prefixWord ++ tailWord_3352908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352908).length < 2 ^ (prefixWord ++ tailWord_3352908).sum := by decide
  have hdescent : baseEnd_3352908 < baseStart_3352908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352914 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3352914 : Nat := 118140960795 + 3352914 * 2 ^ 59
def prefixEnd_3352914 : Nat := 4983230072969 + 3 ^ 40 * 3352914 * 2
def baseEnd_3352914 : Nat := 1721656475189199942255235

theorem tailTrace_3352914 : CollatzResearch.WordTrace tailWord_3352914 prefixEnd_3352914 1721656475189199942255235 := by
  unfold tailWord_3352914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30572705043743171241684449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81527213449981789977825197 30572705043743171241684449)
  ·
    refine ⟨22929528782807378431263337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30572705043743171241684449 22929528782807378431263337)
    ·
      refine ⟨17197146587105533823447503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22929528782807378431263337 17197146587105533823447503)
      ·
        refine ⟨25795719880658300735171255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17197146587105533823447503 25795719880658300735171255)
        ·
          refine ⟨38693579820987451102756883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25795719880658300735171255 38693579820987451102756883)
          ·
            refine ⟨58040369731481176654135325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38693579820987451102756883 58040369731481176654135325)
            ·
              refine ⟨21765138649305441245300747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58040369731481176654135325 21765138649305441245300747)
              ·
                refine ⟨32647707973958161867951121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21765138649305441245300747 32647707973958161867951121)
                ·
                  refine ⟨24485780980468621400963341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32647707973958161867951121 24485780980468621400963341)
                  ·
                    refine ⟨9182167867675733025361253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24485780980468621400963341 9182167867675733025361253)
                    ·
                      refine ⟨1721656475189199942255235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9182167867675733025361253 1721656475189199942255235)
                      ·
                        rfl

theorem cell23_3352914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3352914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352914 prefixEnd_3352914 := by exact prefixLift 3352914
  have htrace : WordTrace (prefixWord ++ tailWord_3352914) baseStart_3352914 baseEnd_3352914 := by
    simpa [prefixWord, tailWord_3352914, baseEnd_3352914] using wordTrace_append hprefix tailTrace_3352914
  have hstable : (prefixWord ++ tailWord_3352914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352914).length < 2 ^ (prefixWord ++ tailWord_3352914).sum := by decide
  have hdescent : baseEnd_3352914 < baseStart_3352914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352926 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3352926 : Nat := 118140960795 + 3352926 * 2 ^ 59
def prefixEnd_3352926 : Nat := 4983230072969 + 3 ^ 40 * 3352926 * 2
def baseEnd_3352926 : Nat := 1721662636957053895305181

theorem tailTrace_3352926 : CollatzResearch.WordTrace tailWord_3352926 prefixEnd_3352926 1721662636957053895305181 := by
  unfold tailWord_3352926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15286407231366151377021829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81527505233952807344116421 15286407231366151377021829)
  ·
    refine ⟨2866201355881153383191593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15286407231366151377021829 2866201355881153383191593)
    ·
      refine ⟨2149651016910865037393695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2866201355881153383191593 2149651016910865037393695)
      ·
        refine ⟨3224476525366297556090543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149651016910865037393695 3224476525366297556090543)
        ·
          refine ⟨4836714788049446334135815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224476525366297556090543 4836714788049446334135815)
          ·
            refine ⟨7255072182074169501203723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836714788049446334135815 7255072182074169501203723)
            ·
              refine ⟨10882608273111254251805585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255072182074169501203723 10882608273111254251805585)
              ·
                refine ⟨8161956204833440688854189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10882608273111254251805585 8161956204833440688854189)
                ·
                  refine ⟨3060733576812540258320321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8161956204833440688854189 3060733576812540258320321)
                  ·
                    refine ⟨2295550182609405193740241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3060733576812540258320321 2295550182609405193740241)
                    ·
                      refine ⟨1721662636957053895305181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295550182609405193740241 1721662636957053895305181)
                      ·
                        rfl

theorem cell23_3352926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3352926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352926 prefixEnd_3352926 := by exact prefixLift 3352926
  have htrace : WordTrace (prefixWord ++ tailWord_3352926) baseStart_3352926 baseEnd_3352926 := by
    simpa [prefixWord, tailWord_3352926, baseEnd_3352926] using wordTrace_append hprefix tailTrace_3352926
  have hstable : (prefixWord ++ tailWord_3352926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352926).length < 2 ^ (prefixWord ++ tailWord_3352926).sum := by decide
  have hdescent : baseEnd_3352926 < baseStart_3352926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352961 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3352961 : Nat := 118140960795 + 3352961 * 2 ^ 59
def prefixEnd_3352961 : Nat := 4983230072969 + 3 ^ 40 * 3352961 * 2
def baseEnd_3352961 : Nat := 1721680608779961258367519

theorem tailTrace_3352961 : CollatzResearch.WordTrace tailWord_3352961 prefixEnd_3352961 1721680608779961258367519 := by
  unfold tailWord_3352961
  simp only [CollatzResearch.WordTrace]
  refine ⟨122292534405802411993698737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81528356270534941329132491 122292534405802411993698737)
  ·
    refine ⟨91719400804351808995274053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122292534405802411993698737 91719400804351808995274053)
    ·
      refine ⟨17197387650815964186613885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91719400804351808995274053 17197387650815964186613885)
      ·
        refine ⟨6449020369055986569980207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17197387650815964186613885 6449020369055986569980207)
        ·
          refine ⟨9673530553583979854970311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449020369055986569980207 9673530553583979854970311)
          ·
            refine ⟨14510295830375969782455467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9673530553583979854970311 14510295830375969782455467)
            ·
              refine ⟨21765443745563954673683201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14510295830375969782455467 21765443745563954673683201)
              ·
                refine ⟨16324082809172966005262401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21765443745563954673683201 16324082809172966005262401)
                ·
                  refine ⟨12243062106879724503946801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16324082809172966005262401 12243062106879724503946801)
                  ·
                    refine ⟨9182296580159793377960101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12243062106879724503946801 9182296580159793377960101)
                    ·
                      refine ⟨1721680608779961258367519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9182296580159793377960101 1721680608779961258367519)
                      ·
                        rfl

theorem cell23_3352961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3352961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352961 prefixEnd_3352961 := by exact prefixLift 3352961
  have htrace : WordTrace (prefixWord ++ tailWord_3352961) baseStart_3352961 baseEnd_3352961 := by
    simpa [prefixWord, tailWord_3352961, baseEnd_3352961] using wordTrace_append hprefix tailTrace_3352961
  have hstable : (prefixWord ++ tailWord_3352961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352961).length < 2 ^ (prefixWord ++ tailWord_3352961).sum := by decide
  have hdescent : baseEnd_3352961 < baseStart_3352961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352971 : List Nat := [1, 1, 1, 1, 4, 4, 2, 4, 5]
def baseStart_3352971 : Nat := 118140960795 + 3352971 * 2 ^ 59
def prefixEnd_3352971 : Nat := 4983230072969 + 3 ^ 40 * 3352971 * 2
def baseEnd_3352971 : Nat := 191298415954056246582497

theorem tailTrace_3352971 : CollatzResearch.WordTrace tailWord_3352971 prefixEnd_3352971 191298415954056246582497 := by
  unfold tailWord_3352971
  simp only [CollatzResearch.WordTrace]
  refine ⟨122292899135766183701562767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81528599423844122467708511 122292899135766183701562767)
  ·
    refine ⟨183439348703649275552344151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122292899135766183701562767 183439348703649275552344151)
    ·
      refine ⟨275159023055473913328516227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183439348703649275552344151 275159023055473913328516227)
      ·
        refine ⟨412738534583210869992774341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275159023055473913328516227 412738534583210869992774341)
        ·
          refine ⟨77388475234352038123645189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 412738534583210869992774341 77388475234352038123645189)
          ·
            refine ⟨14510339106441007148183473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77388475234352038123645189 14510339106441007148183473)
            ·
              refine ⟨10882754329830755361137605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14510339106441007148183473 10882754329830755361137605)
              ·
                refine ⟨2040516436843266630213301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10882754329830755361137605 2040516436843266630213301)
                ·
                  refine ⟨191298415954056246582497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2040516436843266630213301 191298415954056246582497)
                  ·
                    rfl

theorem cell23_3352971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 5].length) (baseStart_3352971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352971 prefixEnd_3352971 := by exact prefixLift 3352971
  have htrace : WordTrace (prefixWord ++ tailWord_3352971) baseStart_3352971 baseEnd_3352971 := by
    simpa [prefixWord, tailWord_3352971, baseEnd_3352971] using wordTrace_append hprefix tailTrace_3352971
  have hstable : (prefixWord ++ tailWord_3352971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352971).length < 2 ^ (prefixWord ++ tailWord_3352971).sum := by decide
  have hdescent : baseEnd_3352971 < baseStart_3352971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353021 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_3353021 : Nat := 118140960795 + 3353021 * 2 ^ 59
def prefixEnd_3353021 : Nat := 4983230072969 + 3 ^ 40 * 3353021 * 2
def baseEnd_3353021 : Nat := 1721711417619231023617243

theorem tailTrace_3353021 : CollatzResearch.WordTrace tailWord_3353021 prefixEnd_3353021 1721711417619231023617243 := by
  unfold tailWord_3353021
  simp only [CollatzResearch.WordTrace]
  refine ⟨122294722785585042240882917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81529815190390028160588611 122294722785585042240882917)
  ·
    refine ⟨22930260522297195420165547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122294722785585042240882917 22930260522297195420165547)
    ·
      refine ⟨34395390783445793130248321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22930260522297195420165547 34395390783445793130248321)
      ·
        refine ⟨25796543087584344847686241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34395390783445793130248321 25796543087584344847686241)
        ·
          refine ⟨19347407315688258635764681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25796543087584344847686241 19347407315688258635764681)
          ·
            refine ⟨14510555486766193976823511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19347407315688258635764681 14510555486766193976823511)
            ·
              refine ⟨21765833230149290965235267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14510555486766193976823511 21765833230149290965235267)
              ·
                refine ⟨32648749845223936447852901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21765833230149290965235267 32648749845223936447852901)
                ·
                  refine ⟨6121640595979488083972419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32648749845223936447852901 6121640595979488083972419)
                  ·
                    refine ⟨9182460893969232125958629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6121640595979488083972419 9182460893969232125958629)
                    ·
                      refine ⟨1721711417619231023617243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9182460893969232125958629 1721711417619231023617243)
                      ·
                        rfl

theorem cell23_3353021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_3353021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353021 prefixEnd_3353021 := by exact prefixLift 3353021
  have htrace : WordTrace (prefixWord ++ tailWord_3353021) baseStart_3353021 baseEnd_3353021 := by
    simpa [prefixWord, tailWord_3353021, baseEnd_3353021] using wordTrace_append hprefix tailTrace_3353021
  have hstable : (prefixWord ++ tailWord_3353021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353021).length < 2 ^ (prefixWord ++ tailWord_3353021).sum := by decide
  have hdescent : baseEnd_3353021 < baseStart_3353021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353028 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_3353028 : Nat := 118140960795 + 3353028 * 2 ^ 59
def prefixEnd_3353028 : Nat := 4983230072969 + 3 ^ 40 * 3353028 * 2
def baseEnd_3353028 : Nat := 1721715011983812496229711

theorem tailTrace_3353028 : CollatzResearch.WordTrace tailWord_3353028 prefixEnd_3353028 1721715011983812496229711 := by
  unfold tailWord_3353028
  simp only [CollatzResearch.WordTrace]
  refine ⟨61147489048279841218193869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81529985397706454957591825 61147489048279841218193869)
  ·
    refine ⟨22930308393104940456822701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61147489048279841218193869 22930308393104940456822701)
    ·
      refine ⟨8598865647414352671308513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22930308393104940456822701 8598865647414352671308513)
      ·
        refine ⟨6449149235560764503481385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8598865647414352671308513 6449149235560764503481385)
        ·
          refine ⟨4836861926670573377611039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6449149235560764503481385 4836861926670573377611039)
          ·
            refine ⟨7255292890005860066416559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836861926670573377611039 7255292890005860066416559)
            ·
              refine ⟨10882939335008790099624839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255292890005860066416559 10882939335008790099624839)
              ·
                refine ⟨16324409002513185149437259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10882939335008790099624839 16324409002513185149437259)
                ·
                  refine ⟨24486613503769777724155889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16324409002513185149437259 24486613503769777724155889)
                  ·
                    refine ⟨18364960127827333293116917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24486613503769777724155889 18364960127827333293116917)
                    ·
                      refine ⟨1721715011983812496229711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18364960127827333293116917 1721715011983812496229711)
                      ·
                        rfl

theorem cell23_3353028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_3353028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353028 prefixEnd_3353028 := by exact prefixLift 3353028
  have htrace : WordTrace (prefixWord ++ tailWord_3353028) baseStart_3353028 baseEnd_3353028 := by
    simpa [prefixWord, tailWord_3353028, baseEnd_3353028] using wordTrace_append hprefix tailTrace_3353028
  have hstable : (prefixWord ++ tailWord_3353028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353028).length < 2 ^ (prefixWord ++ tailWord_3353028).sum := by decide
  have hdescent : baseEnd_3353028 < baseStart_3353028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353078 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 6]
def baseStart_3353078 : Nat := 118140960795 + 3353078 * 2 ^ 59
def prefixEnd_3353078 : Nat := 4983230072969 + 3 ^ 40 * 3353078 * 2
def baseEnd_3353078 : Nat := 191304520668504144511609

theorem tailTrace_3353078 : CollatzResearch.WordTrace tailWord_3353078 prefixEnd_3353078 191304520668504144511609 := by
  unfold tailWord_3353078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643550109148658810981743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81531201164252360650471925 7643550109148658810981743)
  ·
    refine ⟨11465325163722988216472615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7643550109148658810981743 11465325163722988216472615)
    ·
      refine ⟨17197987745584482324708923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465325163722988216472615 17197987745584482324708923)
      ·
        refine ⟨25796981618376723487063385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17197987745584482324708923 25796981618376723487063385)
        ·
          refine ⟨19347736213782542615297539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25796981618376723487063385 19347736213782542615297539)
          ·
            refine ⟨29021604320673813922946309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347736213782542615297539 29021604320673813922946309)
            ·
              refine ⟨5441550810126340110552433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29021604320673813922946309 5441550810126340110552433)
              ·
                refine ⟨4081163107594755082914325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5441550810126340110552433 4081163107594755082914325)
                ·
                  refine ⟨191304520668504144511609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4081163107594755082914325 191304520668504144511609)
                  ·
                    rfl

theorem cell23_3353078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_3353078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353078 prefixEnd_3353078 := by exact prefixLift 3353078
  have htrace : WordTrace (prefixWord ++ tailWord_3353078) baseStart_3353078 baseEnd_3353078 := by
    simpa [prefixWord, tailWord_3353078, baseEnd_3353078] using wordTrace_append hprefix tailTrace_3353078
  have hstable : (prefixWord ++ tailWord_3353078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353078).length < 2 ^ (prefixWord ++ tailWord_3353078).sum := by decide
  have hdescent : baseEnd_3353078 < baseStart_3353078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353098 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2]
def baseStart_3353098 : Nat := 118140960795 + 3353098 * 2 ^ 59
def prefixEnd_3353098 : Nat := 4983230072969 + 3 ^ 40 * 3353098 * 2
def baseEnd_3353098 : Nat := 1721750955629627222354389

theorem tailTrace_3353098 : CollatzResearch.WordTrace tailWord_3353098 prefixEnd_3353098 1721750955629627222354389 := by
  unfold tailWord_3353098
  simp only [CollatzResearch.WordTrace]
  refine ⟨30574382801576521097858987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81531687470870722927623965 30574382801576521097858987)
  ·
    refine ⟨45861574202364781646788481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30574382801576521097858987 45861574202364781646788481)
    ·
      refine ⟨34396180651773586235091361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45861574202364781646788481 34396180651773586235091361)
      ·
        refine ⟨25797135488830189676318521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34396180651773586235091361 25797135488830189676318521)
        ·
          refine ⟨19347851616622642257238891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25797135488830189676318521 19347851616622642257238891)
          ·
            refine ⟨29021777424933963385858337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347851616622642257238891 29021777424933963385858337)
            ·
              refine ⟨21766333068700472539393753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29021777424933963385858337 21766333068700472539393753)
              ·
                refine ⟨16324749801525354404545315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21766333068700472539393753 16324749801525354404545315)
                ·
                  refine ⟨24487124702288031606817973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16324749801525354404545315 24487124702288031606817973)
                  ·
                    refine ⟨2295667940839502963139185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24487124702288031606817973 2295667940839502963139185)
                    ·
                      refine ⟨1721750955629627222354389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295667940839502963139185 1721750955629627222354389)
                      ·
                        rfl

theorem cell23_3353098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_3353098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353098 prefixEnd_3353098 := by exact prefixLift 3353098
  have htrace : WordTrace (prefixWord ++ tailWord_3353098) baseStart_3353098 baseEnd_3353098 := by
    simpa [prefixWord, tailWord_3353098, baseEnd_3353098] using wordTrace_append hprefix tailTrace_3353098
  have hstable : (prefixWord ++ tailWord_3353098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353098).length < 2 ^ (prefixWord ++ tailWord_3353098).sum := by decide
  have hdescent : baseEnd_3353098 < baseStart_3353098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353121 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_3353121 : Nat := 118140960795 + 3353121 * 2 ^ 59
def prefixEnd_3353121 : Nat := 4983230072969 + 3 ^ 40 * 3353121 * 2
def baseEnd_3353121 : Nat := 573920921894893544122261

theorem tailTrace_3353121 : CollatzResearch.WordTrace tailWord_3353121 prefixEnd_3353121 573920921894893544122261 := by
  unfold tailWord_3353121
  simp only [CollatzResearch.WordTrace]
  refine ⟨122298370085222759319523217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81532246723481839546348811 122298370085222759319523217)
  ·
    refine ⟨91723777563917069489642413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122298370085222759319523217 91723777563917069489642413)
    ·
      refine ⟨34396416586468901058615905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91723777563917069489642413 34396416586468901058615905)
      ·
        refine ⟨25797312439851675793961929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34396416586468901058615905 25797312439851675793961929)
        ·
          refine ⟨19347984329888756845471447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25797312439851675793961929 19347984329888756845471447)
          ·
            refine ⟨29021976494833135268207171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19347984329888756845471447 29021976494833135268207171)
            ·
              refine ⟨43532964742249702902310757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29021976494833135268207171 43532964742249702902310757)
              ·
                refine ⟨8162430889171819294183267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43532964742249702902310757 8162430889171819294183267)
                ·
                  refine ⟨12243646333757728941274901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162430889171819294183267 12243646333757728941274901)
                  ·
                    refine ⟨573920921894893544122261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12243646333757728941274901 573920921894893544122261)
                    ·
                      rfl

theorem cell23_3353121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_3353121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353121 prefixEnd_3353121 := by exact prefixLift 3353121
  have htrace : WordTrace (prefixWord ++ tailWord_3353121) baseStart_3353121 baseEnd_3353121 := by
    simpa [prefixWord, tailWord_3353121, baseEnd_3353121] using wordTrace_append hprefix tailTrace_3353121
  have hstable : (prefixWord ++ tailWord_3353121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353121).length < 2 ^ (prefixWord ++ tailWord_3353121).sum := by decide
  have hdescent : baseEnd_3353121 < baseStart_3353121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353141 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_3353141 : Nat := 118140960795 + 3353141 * 2 ^ 59
def prefixEnd_3353141 : Nat := 4983230072969 + 3 ^ 40 * 3353141 * 2
def baseEnd_3353141 : Nat := 1721773035297770554116691

theorem tailTrace_3353141 : CollatzResearch.WordTrace tailWord_3353141 prefixEnd_3353141 1721773035297770554116691 := by
  unfold tailWord_3353141
  simp only [CollatzResearch.WordTrace]
  refine ⟨122299099545150302735251277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81532733030100201823500851 122299099545150302735251277)
  ·
    refine ⟨45862162329431363525719229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122299099545150302735251277 45862162329431363525719229)
    ·
      refine ⟨17198310873536761322144711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45862162329431363525719229 17198310873536761322144711)
      ·
        refine ⟨25797466310305141983217067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17198310873536761322144711 25797466310305141983217067)
        ·
          refine ⟨38696199465457712974825601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25797466310305141983217067 38696199465457712974825601)
          ·
            refine ⟨29022149599093284731119201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38696199465457712974825601 29022149599093284731119201)
            ·
              refine ⟨21766612199319963548339401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29022149599093284731119201 21766612199319963548339401)
              ·
                refine ⟨16324959149489972661254551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21766612199319963548339401 16324959149489972661254551)
                ·
                  refine ⟨24487438724234958991881827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16324959149489972661254551 24487438724234958991881827)
                  ·
                    refine ⟨36731158086352438487822741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24487438724234958991881827 36731158086352438487822741)
                    ·
                      refine ⟨1721773035297770554116691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36731158086352438487822741 1721773035297770554116691)
                      ·
                        rfl

theorem cell23_3353141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_3353141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353141 prefixEnd_3353141 := by exact prefixLift 3353141
  have htrace : WordTrace (prefixWord ++ tailWord_3353141) baseStart_3353141 baseEnd_3353141 := by
    simpa [prefixWord, tailWord_3353141, baseEnd_3353141] using wordTrace_append hprefix tailTrace_3353141
  have hstable : (prefixWord ++ tailWord_3353141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353141).length < 2 ^ (prefixWord ++ tailWord_3353141).sum := by decide
  have hdescent : baseEnd_3353141 < baseStart_3353141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353148 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_3353148 : Nat := 118140960795 + 3353148 * 2 ^ 59
def prefixEnd_3353148 : Nat := 4983230072969 + 3 ^ 40 * 3353148 * 2
def baseEnd_3353148 : Nat := 1721776629662352026729159

theorem tailTrace_3353148 : CollatzResearch.WordTrace tailWord_3353148 prefixEnd_3353148 1721776629662352026729159 := by
  unfold tailWord_3353148
  simp only [CollatzResearch.WordTrace]
  refine ⟨61149677428062471465378049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81532903237416628620504065 61149677428062471465378049)
  ·
    refine ⟨45862258071046853599033537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61149677428062471465378049 45862258071046853599033537)
    ·
      refine ⟨34396693553285140199275153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45862258071046853599033537 34396693553285140199275153)
      ·
        refine ⟨25797520164963855149456365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34396693553285140199275153 25797520164963855149456365)
        ·
          refine ⟨9674070061861445681046137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25797520164963855149456365 9674070061861445681046137)
          ·
            refine ⟨7255552546396084260784603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9674070061861445681046137 7255552546396084260784603)
            ·
              refine ⟨10883328819594126391176905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255552546396084260784603 10883328819594126391176905)
              ·
                refine ⟨8162496614695594793382679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10883328819594126391176905 8162496614695594793382679)
                ·
                  refine ⟨12243744922043392190074019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8162496614695594793382679 12243744922043392190074019)
                  ·
                    refine ⟨18365617383065088285111029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12243744922043392190074019 18365617383065088285111029)
                    ·
                      refine ⟨1721776629662352026729159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18365617383065088285111029 1721776629662352026729159)
                      ·
                        rfl

theorem cell23_3353148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_3353148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353148 prefixEnd_3353148 := by exact prefixLift 3353148
  have htrace : WordTrace (prefixWord ++ tailWord_3353148) baseStart_3353148 baseEnd_3353148 := by
    simpa [prefixWord, tailWord_3353148, baseEnd_3353148] using wordTrace_append hprefix tailTrace_3353148
  have hstable : (prefixWord ++ tailWord_3353148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353148).length < 2 ^ (prefixWord ++ tailWord_3353148).sum := by decide
  have hdescent : baseEnd_3353148 < baseStart_3353148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353191 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_3353191 : Nat := 118140960795 + 3353191 * 2 ^ 59
def prefixEnd_3353191 : Nat := 4983230072969 + 3 ^ 40 * 3353191 * 2
def baseEnd_3353191 : Nat := 1721798709330495358491461

theorem tailTrace_3353191 : CollatzResearch.WordTrace tailWord_3353191 prefixEnd_3353191 1721798709330495358491461 := by
  unfold tailWord_3353191
  simp only [CollatzResearch.WordTrace]
  refine ⟨122300923194969161274571427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81533948796646107516380951 122300923194969161274571427)
  ·
    refine ⟨183451384792453741911857141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122300923194969161274571427 183451384792453741911857141)
    ·
      refine ⟨17198567324292538304236607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183451384792453741911857141 17198567324292538304236607)
      ·
        refine ⟨25797850986438807456354911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17198567324292538304236607 25797850986438807456354911)
        ·
          refine ⟨38696776479658211184532367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25797850986438807456354911 38696776479658211184532367)
          ·
            refine ⟨58045164719487316776798551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38696776479658211184532367 58045164719487316776798551)
            ·
              refine ⟨87067747079230975165197827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58045164719487316776798551 87067747079230975165197827)
              ·
                refine ⟨130601620618846462747796741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87067747079230975165197827 130601620618846462747796741)
                ·
                  refine ⟨24487803866033711765211889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130601620618846462747796741 24487803866033711765211889)
                  ·
                    refine ⟨18365852899525283823908917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24487803866033711765211889 18365852899525283823908917)
                    ·
                      refine ⟨1721798709330495358491461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18365852899525283823908917 1721798709330495358491461)
                      ·
                        rfl

theorem cell23_3353191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_3353191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353191 prefixEnd_3353191 := by exact prefixLift 3353191
  have htrace : WordTrace (prefixWord ++ tailWord_3353191) baseStart_3353191 baseEnd_3353191 := by
    simpa [prefixWord, tailWord_3353191, baseEnd_3353191] using wordTrace_append hprefix tailTrace_3353191
  have hstable : (prefixWord ++ tailWord_3353191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353191).length < 2 ^ (prefixWord ++ tailWord_3353191).sum := by decide
  have hdescent : baseEnd_3353191 < baseStart_3353191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353206 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 2, 4]
def baseStart_3353206 : Nat := 118140960795 + 3353206 * 2 ^ 59
def prefixEnd_3353206 : Nat := 4983230072969 + 3 ^ 40 * 3353206 * 2
def baseEnd_3353206 : Nat := 573935470513437599934631

theorem tailTrace_3353206 : CollatzResearch.WordTrace tailWord_3353206 prefixEnd_3353206 573935470513437599934631 := by
  unfold tailWord_3353206
  simp only [CollatzResearch.WordTrace]
  refine ⟨7643841893119676177272967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81534313526609879224244981 7643841893119676177272967)
  ·
    refine ⟨11465762839679514265909451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7643841893119676177272967 11465762839679514265909451)
    ·
      refine ⟨17198644259519271398864177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11465762839679514265909451 17198644259519271398864177)
      ·
        refine ⟨12898983194639453549148133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17198644259519271398864177 12898983194639453549148133)
        ·
          refine ⟨2418559348994897540465275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12898983194639453549148133 2418559348994897540465275)
          ·
            refine ⟨3627839023492346310697913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418559348994897540465275 3627839023492346310697913)
            ·
              refine ⟨2720879267619259733023435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3627839023492346310697913 2720879267619259733023435)
              ·
                refine ⟨4081318901428889599535153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720879267619259733023435 4081318901428889599535153)
                ·
                  refine ⟨3060989176071667199651365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081318901428889599535153 3060989176071667199651365)
                  ·
                    refine ⟨573935470513437599934631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3060989176071667199651365 573935470513437599934631)
                    ·
                      rfl

theorem cell23_3353206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_3353206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353206 prefixEnd_3353206 := by exact prefixLift 3353206
  have htrace : WordTrace (prefixWord ++ tailWord_3353206) baseStart_3353206 baseEnd_3353206 := by
    simpa [prefixWord, tailWord_3353206, baseEnd_3353206] using wordTrace_append hprefix tailTrace_3353206
  have hstable : (prefixWord ++ tailWord_3353206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353206).length < 2 ^ (prefixWord ++ tailWord_3353206).sum := by decide
  have hdescent : baseEnd_3353206 < baseStart_3353206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353212 : List Nat := [2, 2, 2, 1, 1, 2, 6, 1, 2, 1, 3]
def baseStart_3353212 : Nat := 118140960795 + 3353212 * 2 ^ 59
def prefixEnd_3353212 : Nat := 4983230072969 + 3 ^ 40 * 3353212 * 2
def baseEnd_3353212 : Nat := 1721809492424239776328865

theorem tailTrace_3353212 : CollatzResearch.WordTrace tailWord_3353212 prefixEnd_3353212 1721809492424239776328865 := by
  unfold tailWord_3353212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61150844563946540930542945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81534459418595387907390593 61150844563946540930542945)
  ·
    refine ⟨45863133422959905697907209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61150844563946540930542945 45863133422959905697907209)
    ·
      refine ⟨34397350067219929273430407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45863133422959905697907209 34397350067219929273430407)
      ·
        refine ⟨51596025100829893910145611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34397350067219929273430407 51596025100829893910145611)
        ·
          refine ⟨77394037651244840865218417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51596025100829893910145611 77394037651244840865218417)
          ·
            refine ⟨58045528238433630648913813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77394037651244840865218417 58045528238433630648913813)
            ·
              refine ⟨2720884136176576436667835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58045528238433630648913813 2720884136176576436667835)
              ·
                refine ⟨4081326204264864655001753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720884136176576436667835 4081326204264864655001753)
                ·
                  refine ⟨3060994653198648491251315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081326204264864655001753 3060994653198648491251315)
                  ·
                    refine ⟨4591491979797972736876973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3060994653198648491251315 4591491979797972736876973)
                    ·
                      refine ⟨1721809492424239776328865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4591491979797972736876973 1721809492424239776328865)
                      ·
                        rfl

theorem cell23_3353212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_3353212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353212 prefixEnd_3353212 := by exact prefixLift 3353212
  have htrace : WordTrace (prefixWord ++ tailWord_3353212) baseStart_3353212 baseEnd_3353212 := by
    simpa [prefixWord, tailWord_3353212, baseEnd_3353212] using wordTrace_append hprefix tailTrace_3353212
  have hstable : (prefixWord ++ tailWord_3353212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353212).length < 2 ^ (prefixWord ++ tailWord_3353212).sum := by decide
  have hdescent : baseEnd_3353212 < baseStart_3353212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353231 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4]
def baseStart_3353231 : Nat := 118140960795 + 3353231 * 2 ^ 59
def prefixEnd_3353231 : Nat := 4983230072969 + 3 ^ 40 * 3353231 * 2
def baseEnd_3353231 : Nat := 1721819248556675201991277

theorem tailTrace_3353231 : CollatzResearch.WordTrace tailWord_3353231 prefixEnd_3353231 1721819248556675201991277 := by
  unfold tailWord_3353231
  simp only [CollatzResearch.WordTrace]
  refine ⟨122302382114824248106027547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81534921409882832070685031 122302382114824248106027547)
  ·
    refine ⟨183453573172236372159041321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122302382114824248106027547 183453573172236372159041321)
    ·
      refine ⟨137590179879177279119280991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183453573172236372159041321 137590179879177279119280991)
      ·
        refine ⟨206385269818765918678921487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137590179879177279119280991 206385269818765918678921487)
        ·
          refine ⟨309577904728148878018382231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206385269818765918678921487 309577904728148878018382231)
          ·
            refine ⟨464366857092223317027573347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309577904728148878018382231 464366857092223317027573347)
            ·
              refine ⟨696550285638334975541360021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464366857092223317027573347 696550285638334975541360021)
              ·
                refine ⟨32650794639296951978501251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 696550285638334975541360021 32650794639296951978501251)
                ·
                  refine ⟨48976191958945427967751877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32650794639296951978501251 48976191958945427967751877)
                  ·
                    refine ⟨9183035992302267743953477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48976191958945427967751877 9183035992302267743953477)
                    ·
                      refine ⟨1721819248556675201991277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9183035992302267743953477 1721819248556675201991277)
                      ·
                        rfl

theorem cell23_3353231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 4].length) (baseStart_3353231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353231 prefixEnd_3353231 := by exact prefixLift 3353231
  have htrace : WordTrace (prefixWord ++ tailWord_3353231) baseStart_3353231 baseEnd_3353231 := by
    simpa [prefixWord, tailWord_3353231, baseEnd_3353231] using wordTrace_append hprefix tailTrace_3353231
  have hstable : (prefixWord ++ tailWord_3353231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353231).length < 2 ^ (prefixWord ++ tailWord_3353231).sum := by decide
  have hdescent : baseEnd_3353231 < baseStart_3353231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353269 : List Nat := [1, 3, 3, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3353269 : Nat := 118140960795 + 3353269 * 2 ^ 59
def prefixEnd_3353269 : Nat := 4983230072969 + 3 ^ 40 * 3353269 * 2
def baseEnd_3353269 : Nat := 1721838760821546053316103

theorem tailTrace_3353269 : CollatzResearch.WordTrace tailWord_3353269 prefixEnd_3353269 1721838760821546053316103 := by
  unfold tailWord_3353269
  simp only [CollatzResearch.WordTrace]
  refine ⟨122303768088686580595910861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81535845392457720397273907 122303768088686580595910861)
  ·
    refine ⟨45863913033257467723466573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122303768088686580595910861 45863913033257467723466573)
    ·
      refine ⟨17198967387471550396299965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45863913033257467723466573 17198967387471550396299965)
      ·
        refine ⟨6449612770301831398612487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17198967387471550396299965 6449612770301831398612487)
        ·
          refine ⟨9674419155452747097918731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449612770301831398612487 9674419155452747097918731)
          ·
            refine ⟨14511628733179120646878097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9674419155452747097918731 14511628733179120646878097)
            ·
              refine ⟨10883721549884340485158573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14511628733179120646878097 10883721549884340485158573)
              ·
                refine ⟨4081395581206627681934465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10883721549884340485158573 4081395581206627681934465)
                ·
                  refine ⟨3061046685904970761450849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4081395581206627681934465 3061046685904970761450849)
                  ·
                    refine ⟨2295785014428728071088137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061046685904970761450849 2295785014428728071088137)
                    ·
                      refine ⟨1721838760821546053316103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295785014428728071088137 1721838760821546053316103)
                      ·
                        rfl

theorem cell23_3353269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3353269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353269 prefixEnd_3353269 := by exact prefixLift 3353269
  have htrace : WordTrace (prefixWord ++ tailWord_3353269) baseStart_3353269 baseEnd_3353269 := by
    simpa [prefixWord, tailWord_3353269, baseEnd_3353269] using wordTrace_append hprefix tailTrace_3353269
  have hstable : (prefixWord ++ tailWord_3353269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353269).length < 2 ^ (prefixWord ++ tailWord_3353269).sum := by decide
  have hdescent : baseEnd_3353269 < baseStart_3353269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353288 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 7]
def baseStart_3353288 : Nat := 118140960795 + 3353288 * 2 ^ 59
def prefixEnd_3353288 : Nat := 4983230072969 + 3 ^ 40 * 3353288 * 2
def baseEnd_3353288 : Nat := 573949505651327159659505

theorem tailTrace_3353288 : CollatzResearch.WordTrace tailWord_3353288 prefixEnd_3353288 573949505651327159659505 := by
  unfold tailWord_3353288
  simp only [CollatzResearch.WordTrace]
  refine ⟨61152230537808873420426259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81536307383745164560568345 61152230537808873420426259)
  ·
    refine ⟨91728345806713310130639389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61152230537808873420426259 91728345806713310130639389)
    ·
      refine ⟨34398129677517491298989771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91728345806713310130639389 34398129677517491298989771)
      ·
        refine ⟨51597194516276236948484657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34398129677517491298989771 51597194516276236948484657)
        ·
          refine ⟨38697895887207177711363493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51597194516276236948484657 38697895887207177711363493)
          ·
            refine ⟨7255855478851345820880655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38697895887207177711363493 7255855478851345820880655)
            ·
              refine ⟨10883783218277018731320983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7255855478851345820880655 10883783218277018731320983)
              ·
                refine ⟨16325674827415528096981475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10883783218277018731320983 16325674827415528096981475)
                ·
                  refine ⟨24488512241123292145472213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16325674827415528096981475 24488512241123292145472213)
                  ·
                    refine ⟨573949505651327159659505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24488512241123292145472213 573949505651327159659505)
                    ·
                      rfl

theorem cell23_3353288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_3353288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353288 prefixEnd_3353288 := by exact prefixLift 3353288
  have htrace : WordTrace (prefixWord ++ tailWord_3353288) baseStart_3353288 baseEnd_3353288 := by
    simpa [prefixWord, tailWord_3353288, baseEnd_3353288] using wordTrace_append hprefix tailTrace_3353288
  have hstable : (prefixWord ++ tailWord_3353288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353288).length < 2 ^ (prefixWord ++ tailWord_3353288).sum := by decide
  have hdescent : baseEnd_3353288 < baseStart_3353288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353292 : List Nat := [2, 2, 1, 5, 1, 2, 2, 3, 5]
def baseStart_3353292 : Nat := 118140960795 + 3353292 * 2 ^ 59
def prefixEnd_3353292 : Nat := 4983230072969 + 3 ^ 40 * 3353292 * 2
def baseEnd_3353292 : Nat := 191316730097399940369833

theorem tailTrace_3353292 : CollatzResearch.WordTrace tailWord_3353292 prefixEnd_3353292 191316730097399940369833 := by
  unfold tailWord_3353292
  simp only [CollatzResearch.WordTrace]
  refine ⟨61152303483801627761999065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81536404645068837015998753 61152303483801627761999065)
  ·
    refine ⟨45864227612851220821499299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61152303483801627761999065 45864227612851220821499299)
    ·
      refine ⟨68796341419276831232248949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45864227612851220821499299 68796341419276831232248949)
      ·
        refine ⟨6449657008057202928023339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68796341419276831232248949 6449657008057202928023339)
        ·
          refine ⟨9674485512085804392035009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6449657008057202928023339 9674485512085804392035009)
          ·
            refine ⟨7255864134064353294026257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9674485512085804392035009 7255864134064353294026257)
            ·
              refine ⟨5441898100548264970519693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7255864134064353294026257 5441898100548264970519693)
              ·
                refine ⟨2040711787705599363944885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5441898100548264970519693 2040711787705599363944885)
                ·
                  refine ⟨191316730097399940369833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2040711787705599363944885 191316730097399940369833)
                  ·
                    rfl

theorem cell23_3353292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_3353292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353292 prefixEnd_3353292 := by exact prefixLift 3353292
  have htrace : WordTrace (prefixWord ++ tailWord_3353292) baseStart_3353292 baseEnd_3353292 := by
    simpa [prefixWord, tailWord_3353292, baseEnd_3353292] using wordTrace_append hprefix tailTrace_3353292
  have hstable : (prefixWord ++ tailWord_3353292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353292).length < 2 ^ (prefixWord ++ tailWord_3353292).sum := by decide
  have hdescent : baseEnd_3353292 < baseStart_3353292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353328 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3]
def baseStart_3353328 : Nat := 118140960795 + 3353328 * 2 ^ 59
def prefixEnd_3353328 : Nat := 4983230072969 + 3 ^ 40 * 3353328 * 2
def baseEnd_3353328 : Nat := 1721869056180161322478331

theorem tailTrace_3353328 : CollatzResearch.WordTrace tailWord_3353328 prefixEnd_3353328 1721869056180161322478331 := by
  unfold tailWord_3353328
  simp only [CollatzResearch.WordTrace]
  refine ⟨61152959997736416836154319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81537279996981889114872425 61152959997736416836154319)
  ·
    refine ⟨91729439996604625254231479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61152959997736416836154319 91729439996604625254231479)
    ·
      refine ⟨137594159994906937881347219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91729439996604625254231479 137594159994906937881347219)
      ·
        refine ⟨206391239992360406822020829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137594159994906937881347219 206391239992360406822020829)
        ·
          refine ⟨77396714997135152558257811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206391239992360406822020829 77396714997135152558257811)
          ·
            refine ⟨116095072495702728837386717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77396714997135152558257811 116095072495702728837386717)
            ·
              refine ⟨43535652185888523314020019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116095072495702728837386717 43535652185888523314020019)
              ·
                refine ⟨65303478278832784971030029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43535652185888523314020019 65303478278832784971030029)
                ·
                  refine ⟨24488804354562294364136261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65303478278832784971030029 24488804354562294364136261)
                  ·
                    refine ⟨4591650816480430193275549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24488804354562294364136261 4591650816480430193275549)
                    ·
                      refine ⟨1721869056180161322478331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4591650816480430193275549 1721869056180161322478331)
                      ·
                        rfl

theorem cell23_3353328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 3, 4, 3].length) (baseStart_3353328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353328 prefixEnd_3353328 := by exact prefixLift 3353328
  have htrace : WordTrace (prefixWord ++ tailWord_3353328) baseStart_3353328 baseEnd_3353328 := by
    simpa [prefixWord, tailWord_3353328, baseEnd_3353328] using wordTrace_append hprefix tailTrace_3353328
  have hstable : (prefixWord ++ tailWord_3353328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353328).length < 2 ^ (prefixWord ++ tailWord_3353328).sum := by decide
  have hdescent : baseEnd_3353328 < baseStart_3353328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353345 : List Nat := [1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_3353345 : Nat := 118140960795 + 3353345 * 2 ^ 59
def prefixEnd_3353345 : Nat := 4983230072969 + 3 ^ 40 * 3353345 * 2
def baseEnd_3353345 : Nat := 1721877785351287755965753

theorem tailTrace_3353345 : CollatzResearch.WordTrace tailWord_3353345 prefixEnd_3353345 1721877785351287755965753 := by
  unfold tailWord_3353345
  simp only [CollatzResearch.WordTrace]
  refine ⟨122306540036411245575677489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81537693357607497050451659 122306540036411245575677489)
  ·
    refine ⟨91729905027308434181758117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122306540036411245575677489 91729905027308434181758117)
    ·
      refine ⟨17199357192620331409079647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91729905027308434181758117 17199357192620331409079647)
      ·
        refine ⟨25799035788930497113619471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17199357192620331409079647 25799035788930497113619471)
        ·
          refine ⟨38698553683395745670429207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25799035788930497113619471 38698553683395745670429207)
          ·
            refine ⟨58047830525093618505643811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38698553683395745670429207 58047830525093618505643811)
            ·
              refine ⟨87071745787640427758465717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58047830525093618505643811 87071745787640427758465717)
              ·
                refine ⟨8162976167591290102356161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87071745787640427758465717 8162976167591290102356161)
                ·
                  refine ⟨6122232125693467576767121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8162976167591290102356161 6122232125693467576767121)
                  ·
                    refine ⟨4591674094270100682575341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6122232125693467576767121 4591674094270100682575341)
                    ·
                      refine ⟨1721877785351287755965753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4591674094270100682575341 1721877785351287755965753)
                      ·
                        rfl

theorem cell23_3353345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_3353345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353345 prefixEnd_3353345 := by exact prefixLift 3353345
  have htrace : WordTrace (prefixWord ++ tailWord_3353345) baseStart_3353345 baseEnd_3353345 := by
    simpa [prefixWord, tailWord_3353345, baseEnd_3353345] using wordTrace_append hprefix tailTrace_3353345
  have hstable : (prefixWord ++ tailWord_3353345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353345).length < 2 ^ (prefixWord ++ tailWord_3353345).sum := by decide
  have hdescent : baseEnd_3353345 < baseStart_3353345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353348 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 10]
def baseStart_3353348 : Nat := 118140960795 + 3353348 * 2 ^ 59
def prefixEnd_3353348 : Nat := 4983230072969 + 3 ^ 40 * 3353348 * 2
def baseEnd_3353348 : Nat := 191319925088139027136471

theorem tailTrace_3353348 : CollatzResearch.WordTrace tailWord_3353348 prefixEnd_3353348 191319925088139027136471 := by
  unfold tailWord_3353348
  simp only [CollatzResearch.WordTrace]
  refine ⟨61153324727700188544018349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81537766303600251392024465 61153324727700188544018349)
  ·
    refine ⟨22932496772887570704006881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61153324727700188544018349 22932496772887570704006881)
    ·
      refine ⟨17199372579665678028005161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22932496772887570704006881 17199372579665678028005161)
      ·
        refine ⟨12899529434749258521003871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17199372579665678028005161 12899529434749258521003871)
        ·
          refine ⟨19349294152123887781505807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12899529434749258521003871 19349294152123887781505807)
          ·
            refine ⟨29023941228185831672258711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19349294152123887781505807 29023941228185831672258711)
            ·
              refine ⟨43535911842278747508388067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29023941228185831672258711 43535911842278747508388067)
              ·
                refine ⟨65303867763418121262582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43535911842278747508388067 65303867763418121262582101)
                ·
                  refine ⟨191319925088139027136471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65303867763418121262582101 191319925088139027136471)
                  ·
                    rfl

theorem cell23_3353348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_3353348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353348 prefixEnd_3353348 := by exact prefixLift 3353348
  have htrace : WordTrace (prefixWord ++ tailWord_3353348) baseStart_3353348 baseEnd_3353348 := by
    simpa [prefixWord, tailWord_3353348, baseEnd_3353348] using wordTrace_append hprefix tailTrace_3353348
  have hstable : (prefixWord ++ tailWord_3353348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353348).length < 2 ^ (prefixWord ++ tailWord_3353348).sum := by decide
  have hdescent : baseEnd_3353348 < baseStart_3353348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353395 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 3, 5]
def baseStart_3353395 : Nat := 118140960795 + 3353395 * 2 ^ 59
def prefixEnd_3353395 : Nat := 4983230072969 + 3 ^ 40 * 3353395 * 2
def baseEnd_3353395 : Nat := 573967819794670853446841

theorem tailTrace_3353395 : CollatzResearch.WordTrace tailWord_3353395 prefixEnd_3353395 573967819794670853446841 := by
  unfold tailWord_3353395
  simp only [CollatzResearch.WordTrace]
  refine ⟨122308363686230104114997639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81538909124153402743331759 122308363686230104114997639)
  ·
    refine ⟨183462545529345156172496459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122308363686230104114997639 183462545529345156172496459)
    ·
      refine ⟨275193818294017734258744689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183462545529345156172496459 275193818294017734258744689)
      ·
        refine ⟨206395363720513300694058517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275193818294017734258744689 206395363720513300694058517)
        ·
          refine ⟨9674782674399060970033993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206395363720513300694058517 9674782674399060970033993)
          ·
            refine ⟨7256087005799295727525495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9674782674399060970033993 7256087005799295727525495)
            ·
              refine ⟨10884130508698943591288243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256087005799295727525495 10884130508698943591288243)
              ·
                refine ⟨16326195763048415386932365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884130508698943591288243 16326195763048415386932365)
                ·
                  refine ⟨6122323411143155770099637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16326195763048415386932365 6122323411143155770099637)
                  ·
                    refine ⟨573967819794670853446841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6122323411143155770099637 573967819794670853446841)
                    ·
                      rfl

theorem cell23_3353395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 3, 5].length) (baseStart_3353395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353395 prefixEnd_3353395 := by exact prefixLift 3353395
  have htrace : WordTrace (prefixWord ++ tailWord_3353395) baseStart_3353395 baseEnd_3353395 := by
    simpa [prefixWord, tailWord_3353395, baseEnd_3353395] using wordTrace_append hprefix tailTrace_3353395
  have hstable : (prefixWord ++ tailWord_3353395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353395).length < 2 ^ (prefixWord ++ tailWord_3353395).sum := by decide
  have hdescent : baseEnd_3353395 < baseStart_3353395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353432 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2]
def baseStart_3353432 : Nat := 118140960795 + 3353432 * 2 ^ 59
def prefixEnd_3353432 : Nat := 4983230072969 + 3 ^ 40 * 3353432 * 2
def baseEnd_3353432 : Nat := 1721922458168228915577853

theorem tailTrace_3353432 : CollatzResearch.WordTrace tailWord_3353432 prefixEnd_3353432 1721922458168228915577853 := by
  unfold tailWord_3353432
  simp only [CollatzResearch.WordTrace]
  refine ⟨61154856593548029717047275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81539808791397372956063033 61154856593548029717047275)
  ·
    refine ⟨91732284890322044575570913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61154856593548029717047275 91732284890322044575570913)
    ·
      refine ⟨68799213667741533431678185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91732284890322044575570913 68799213667741533431678185)
      ·
        refine ⟨51599410250806150073758639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68799213667741533431678185 51599410250806150073758639)
        ·
          refine ⟨77399115376209225110637959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51599410250806150073758639 77399115376209225110637959)
          ·
            refine ⟨116098673064313837665956939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77399115376209225110637959 116098673064313837665956939)
            ·
              refine ⟨174148009596470756498935409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116098673064313837665956939 174148009596470756498935409)
              ·
                refine ⟨130611007197353067374201557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174148009596470756498935409 130611007197353067374201557)
                ·
                  refine ⟨3061195481187962516582849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 130611007197353067374201557 3061195481187962516582849)
                  ·
                    refine ⟨2295896610890971887437137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061195481187962516582849 2295896610890971887437137)
                    ·
                      refine ⟨1721922458168228915577853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295896610890971887437137 1721922458168228915577853)
                      ·
                        rfl

theorem cell23_3353432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_3353432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353432 prefixEnd_3353432 := by exact prefixLift 3353432
  have htrace : WordTrace (prefixWord ++ tailWord_3353432) baseStart_3353432 baseEnd_3353432 := by
    simpa [prefixWord, tailWord_3353432, baseEnd_3353432] using wordTrace_append hprefix tailTrace_3353432
  have hstable : (prefixWord ++ tailWord_3353432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353432).length < 2 ^ (prefixWord ++ tailWord_3353432).sum := by decide
  have hdescent : baseEnd_3353432 < baseStart_3353432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353445 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_3353445 : Nat := 118140960795 + 3353445 * 2 ^ 59
def prefixEnd_3353445 : Nat := 4983230072969 + 3 ^ 40 * 3353445 * 2
def baseEnd_3353445 : Nat := 1721929133416737364715293

theorem tailTrace_3353445 : CollatzResearch.WordTrace tailWord_3353445 prefixEnd_3353445 1721929133416737364715293 := by
  unfold tailWord_3353445
  simp only [CollatzResearch.WordTrace]
  refine ⟨122310187336048962654317789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81540124890699308436211859 122310187336048962654317789)
  ·
    refine ⟨45866320251018360995369171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122310187336048962654317789 45866320251018360995369171)
    ·
      refine ⟨68799480376527541493053757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45866320251018360995369171 68799480376527541493053757)
      ·
        refine ⟨25799805141197828059895159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68799480376527541493053757 25799805141197828059895159)
        ·
          refine ⟨38699707711796742089842739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25799805141197828059895159 38699707711796742089842739)
          ·
            refine ⟨58049561567695113134764109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38699707711796742089842739 58049561567695113134764109)
            ·
              refine ⟨21768585587885667425536541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58049561567695113134764109 21768585587885667425536541)
              ·
                refine ⟨8163219595457125284576203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21768585587885667425536541 8163219595457125284576203)
                ·
                  refine ⟨12244829393185687926864305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8163219595457125284576203 12244829393185687926864305)
                  ·
                    refine ⟨9183622044889265945148229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12244829393185687926864305 9183622044889265945148229)
                    ·
                      refine ⟨1721929133416737364715293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9183622044889265945148229 1721929133416737364715293)
                      ·
                        rfl

theorem cell23_3353445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_3353445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353445 prefixEnd_3353445 := by exact prefixLift 3353445
  have htrace : WordTrace (prefixWord ++ tailWord_3353445) baseStart_3353445 baseEnd_3353445 := by
    simpa [prefixWord, tailWord_3353445, baseEnd_3353445] using wordTrace_append hprefix tailTrace_3353445
  have hstable : (prefixWord ++ tailWord_3353445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353445).length < 2 ^ (prefixWord ++ tailWord_3353445).sum := by decide
  have hdescent : baseEnd_3353445 < baseStart_3353445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353452 : List Nat := [2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 3]
def baseStart_3353452 : Nat := 118140960795 + 3353452 * 2 ^ 59
def prefixEnd_3353452 : Nat := 4983230072969 + 3 ^ 40 * 3353452 * 2
def baseEnd_3353452 : Nat := 1721932727781318837327761

theorem tailTrace_3353452 : CollatzResearch.WordTrace tailWord_3353452 prefixEnd_3353452 1721932727781318837327761 := by
  unfold tailWord_3353452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61155221323511801424911305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81540295098015735233215073 61155221323511801424911305)
  ·
    refine ⟨45866415992633851068683479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61155221323511801424911305 45866415992633851068683479)
    ·
      refine ⟨68799623988950776603025219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45866415992633851068683479 68799623988950776603025219)
      ·
        refine ⟨103199435983426164904537829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68799623988950776603025219 103199435983426164904537829)
        ·
          refine ⟨19349894246892405919600843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103199435983426164904537829 19349894246892405919600843)
          ·
            refine ⟨29024841370338608879401265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19349894246892405919600843 29024841370338608879401265)
            ·
              refine ⟨21768631027753956659550949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29024841370338608879401265 21768631027753956659550949)
              ·
                refine ⟨4081618317703866873665803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21768631027753956659550949 4081618317703866873665803)
                ·
                  refine ⟨6122427476555800310498705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081618317703866873665803 6122427476555800310498705)
                  ·
                    refine ⟨4591820607416850232874029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6122427476555800310498705 4591820607416850232874029)
                    ·
                      refine ⟨1721932727781318837327761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4591820607416850232874029 1721932727781318837327761)
                      ·
                        rfl

theorem cell23_3353452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_3353452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353452 prefixEnd_3353452 := by exact prefixLift 3353452
  have htrace : WordTrace (prefixWord ++ tailWord_3353452) baseStart_3353452 baseEnd_3353452 := by
    simpa [prefixWord, tailWord_3353452, baseEnd_3353452] using wordTrace_append hprefix tailTrace_3353452
  have hstable : (prefixWord ++ tailWord_3353452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353452).length < 2 ^ (prefixWord ++ tailWord_3353452).sum := by decide
  have hdescent : baseEnd_3353452 < baseStart_3353452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353469 : List Nat := [1, 4, 1, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_3353469 : Nat := 118140960795 + 3353469 * 2 ^ 59
def prefixEnd_3353469 : Nat := 4983230072969 + 3 ^ 40 * 3353469 * 2
def baseEnd_3353469 : Nat := 1721941456952445270815183

theorem tailTrace_3353469 : CollatzResearch.WordTrace tailWord_3353469 prefixEnd_3353469 1721941456952445270815183 := by
  unfold tailWord_3353469
  simp only [CollatzResearch.WordTrace]
  refine ⟨122311062687962014753191461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81540708458641343168794307 122311062687962014753191461)
  ·
    refine ⟨22933324253992877766223399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122311062687962014753191461 22933324253992877766223399)
    ·
      refine ⟨34399986380989316649335099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22933324253992877766223399 34399986380989316649335099)
      ·
        refine ⟨51599979571483974974002649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34399986380989316649335099 51599979571483974974002649)
        ·
          refine ⟨38699984678612981230501987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51599979571483974974002649 38699984678612981230501987)
          ·
            refine ⟨58049977017919471845752981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38699984678612981230501987 58049977017919471845752981)
            ·
              refine ⟨2721092672714975242769671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58049977017919471845752981 2721092672714975242769671)
              ·
                refine ⟨4081639009072462864154507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721092672714975242769671 4081639009072462864154507)
                ·
                  refine ⟨6122458513608694296231761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081639009072462864154507 6122458513608694296231761)
                  ·
                    refine ⟨4591843885206520722173821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6122458513608694296231761 4591843885206520722173821)
                    ·
                      refine ⟨1721941456952445270815183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4591843885206520722173821 1721941456952445270815183)
                      ·
                        rfl

theorem cell23_3353469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_3353469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353469 prefixEnd_3353469 := by exact prefixLift 3353469
  have htrace : WordTrace (prefixWord ++ tailWord_3353469) baseStart_3353469 baseEnd_3353469 := by
    simpa [prefixWord, tailWord_3353469, baseEnd_3353469] using wordTrace_append hprefix tailTrace_3353469
  have hstable : (prefixWord ++ tailWord_3353469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353469).length < 2 ^ (prefixWord ++ tailWord_3353469).sum := by decide
  have hdescent : baseEnd_3353469 < baseStart_3353469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10]
def baseStart_3353488 : Nat := 118140960795 + 3353488 * 2 ^ 59
def prefixEnd_3353488 : Nat := 4983230072969 + 3 ^ 40 * 3353488 * 2
def baseEnd_3353488 : Nat := 1721951213084880696477595

theorem tailTrace_3353488 : CollatzResearch.WordTrace tailWord_3353488 prefixEnd_3353488 1721951213084880696477595 := by
  unfold tailWord_3353488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61155877837446590499066559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81541170449928787332088745 61155877837446590499066559)
  ·
    refine ⟨91733816756169885748599839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61155877837446590499066559 91733816756169885748599839)
    ·
      refine ⟨137600725134254828622899759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91733816756169885748599839 137600725134254828622899759)
      ·
        refine ⟨206401087701382242934349639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137600725134254828622899759 206401087701382242934349639)
        ·
          refine ⟨309601631552073364401524459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206401087701382242934349639 309601631552073364401524459)
          ·
            refine ⟨464402447328110046602286689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309601631552073364401524459 464402447328110046602286689)
            ·
              refine ⟨348301835496082534951715017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464402447328110046602286689 348301835496082534951715017)
              ·
                refine ⟨261226376622061901213786263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348301835496082534951715017 261226376622061901213786263)
                ·
                  refine ⟨391839564933092851820679395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261226376622061901213786263 391839564933092851820679395)
                  ·
                    refine ⟨587759347399639277731019093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 391839564933092851820679395 587759347399639277731019093)
                    ·
                      refine ⟨1721951213084880696477595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 587759347399639277731019093 1721951213084880696477595)
                      ·
                        rfl

theorem cell23_3353488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_3353488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353488 prefixEnd_3353488 := by exact prefixLift 3353488
  have htrace : WordTrace (prefixWord ++ tailWord_3353488) baseStart_3353488 baseEnd_3353488 := by
    simpa [prefixWord, tailWord_3353488, baseEnd_3353488] using wordTrace_append hprefix tailTrace_3353488
  have hstable : (prefixWord ++ tailWord_3353488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353488).length < 2 ^ (prefixWord ++ tailWord_3353488).sum := by decide
  have hdescent : baseEnd_3353488 < baseStart_3353488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353517 : List Nat := [1, 5, 2, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_3353517 : Nat := 118140960795 + 3353517 * 2 ^ 59
def prefixEnd_3353517 : Nat := 4983230072969 + 3 ^ 40 * 3353517 * 2
def baseEnd_3353517 : Nat := 1721966104023861083014963

theorem tailTrace_3353517 : CollatzResearch.WordTrace tailWord_3353517 prefixEnd_3353517 1721966104023861083014963 := by
  unfold tailWord_3353517
  simp only [CollatzResearch.WordTrace]
  refine ⟨122312813391788118950938805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81541875594525412633959203 122312813391788118950938805)
  ·
    refine ⟨11466826255480136151650513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122312813391788118950938805 11466826255480136151650513)
    ·
      refine ⟨8600119691610102113737885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11466826255480136151650513 8600119691610102113737885)
      ·
        refine ⟨3225044884353788292651707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8600119691610102113737885 3225044884353788292651707)
        ·
          refine ⟨4837567326530682438977561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225044884353788292651707 4837567326530682438977561)
          ·
            refine ⟨3628175494898011829233171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4837567326530682438977561 3628175494898011829233171)
            ·
              refine ⟨5442263242347017743849757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628175494898011829233171 5442263242347017743849757)
              ·
                refine ⟨2040848715880131653943659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5442263242347017743849757 2040848715880131653943659)
                ·
                  refine ⟨3061273073820197480915489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040848715880131653943659 3061273073820197480915489)
                  ·
                    refine ⟨2295954805365148110686617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3061273073820197480915489 2295954805365148110686617)
                    ·
                      refine ⟨1721966104023861083014963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2295954805365148110686617 1721966104023861083014963)
                      ·
                        rfl

theorem cell23_3353517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_3353517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353517 prefixEnd_3353517 := by exact prefixLift 3353517
  have htrace : WordTrace (prefixWord ++ tailWord_3353517) baseStart_3353517 baseEnd_3353517 := by
    simpa [prefixWord, tailWord_3353517, baseEnd_3353517] using wordTrace_append hprefix tailTrace_3353517
  have hstable : (prefixWord ++ tailWord_3353517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353517).length < 2 ^ (prefixWord ++ tailWord_3353517).sum := by decide
  have hdescent : baseEnd_3353517 < baseStart_3353517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353535 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4]
def baseStart_3353535 : Nat := 118140960795 + 3353535 * 2 ^ 59
def prefixEnd_3353535 : Nat := 4983230072969 + 3 ^ 40 * 3353535 * 2
def baseEnd_3353535 : Nat := 1721975346675642012589879

theorem tailTrace_3353535 : CollatzResearch.WordTrace tailWord_3353535 prefixEnd_3353535 1721975346675642012589879 := by
  unfold tailWord_3353535
  simp only [CollatzResearch.WordTrace]
  refine ⟨122313469905722908025094059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81542313270481938683396039 122313469905722908025094059)
  ·
    refine ⟨183470204858584362037641089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122313469905722908025094059 183470204858584362037641089)
    ·
      refine ⟨137602653643938271528230817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183470204858584362037641089 137602653643938271528230817)
      ·
        refine ⟨103201990232953703646173113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137602653643938271528230817 103201990232953703646173113)
        ·
          refine ⟨77401492674715277734629835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103201990232953703646173113 77401492674715277734629835)
          ·
            refine ⟨116102239012072916601944753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77401492674715277734629835 116102239012072916601944753)
            ·
              refine ⟨87076679259054687451458565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116102239012072916601944753 87076679259054687451458565)
              ·
                refine ⟨16326877361072753897148481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87076679259054687451458565 16326877361072753897148481)
                ·
                  refine ⟨12245158020804565422861361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16326877361072753897148481 12245158020804565422861361)
                  ·
                    refine ⟨9183868515603424067146021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12245158020804565422861361 9183868515603424067146021)
                    ·
                      refine ⟨1721975346675642012589879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9183868515603424067146021 1721975346675642012589879)
                      ·
                        rfl

theorem cell23_3353535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 2, 2, 4].length) (baseStart_3353535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353535 prefixEnd_3353535 := by exact prefixLift 3353535
  have htrace : WordTrace (prefixWord ++ tailWord_3353535) baseStart_3353535 baseEnd_3353535 := by
    simpa [prefixWord, tailWord_3353535, baseEnd_3353535] using wordTrace_append hprefix tailTrace_3353535
  have hstable : (prefixWord ++ tailWord_3353535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353535).length < 2 ^ (prefixWord ++ tailWord_3353535).sum := by decide
  have hdescent : baseEnd_3353535 < baseStart_3353535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353595 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4]
def baseStart_3353595 : Nat := 118140960795 + 3353595 * 2 ^ 59
def prefixEnd_3353595 : Nat := 4983230072969 + 3 ^ 40 * 3353595 * 2
def baseEnd_3353595 : Nat := 1722006155514911777839603

theorem tailTrace_3353595 : CollatzResearch.WordTrace tailWord_3353595 prefixEnd_3353595 1722006155514911777839603 := by
  unfold tailWord_3353595
  simp only [CollatzResearch.WordTrace]
  refine ⟨122315658285505538272278239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81543772190337025514852159 122315658285505538272278239)
  ·
    refine ⟨183473487428258307408417359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122315658285505538272278239 183473487428258307408417359)
    ·
      refine ⟨275210231142387461112626039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183473487428258307408417359 275210231142387461112626039)
      ·
        refine ⟨412815346713581191668939059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275210231142387461112626039 412815346713581191668939059)
        ·
          refine ⟨619223020070371787503408589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412815346713581191668939059 619223020070371787503408589)
          ·
            refine ⟨232208632526389420313778221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619223020070371787503408589 232208632526389420313778221)
            ·
              refine ⟨87078237197396032617666833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232208632526389420313778221 87078237197396032617666833)
              ·
                refine ⟨65308677898047024463250125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87078237197396032617666833 65308677898047024463250125)
                ·
                  refine ⟨24490754211767634173718797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65308677898047024463250125 24490754211767634173718797)
                  ·
                    refine ⟨9184032829412862815144549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24490754211767634173718797 9184032829412862815144549)
                    ·
                      refine ⟨1722006155514911777839603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9184032829412862815144549 1722006155514911777839603)
                      ·
                        rfl

theorem cell23_3353595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 3, 3, 4].length) (baseStart_3353595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353595 prefixEnd_3353595 := by exact prefixLift 3353595
  have htrace : WordTrace (prefixWord ++ tailWord_3353595) baseStart_3353595 baseEnd_3353595 := by
    simpa [prefixWord, tailWord_3353595, baseEnd_3353595] using wordTrace_append hprefix tailTrace_3353595
  have hstable : (prefixWord ++ tailWord_3353595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353595).length < 2 ^ (prefixWord ++ tailWord_3353595).sum := by decide
  have hdescent : baseEnd_3353595 < baseStart_3353595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353596 : List Nat := [2, 2, 2, 1, 2, 5, 2, 2, 5]
def baseStart_3353596 : Nat := 118140960795 + 3353596 * 2 ^ 59
def prefixEnd_3353596 : Nat := 4983230072969 + 3 ^ 40 * 3353596 * 2
def baseEnd_3353596 : Nat := 191334074332840697103011

theorem tailTrace_3353596 : CollatzResearch.WordTrace tailWord_3353596 prefixEnd_3353596 191334074332840697103011 := by
  unfold tailWord_3353596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61157847379250957721532321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81543796505667943628709761 61157847379250957721532321)
  ·
    refine ⟨45868385534438218291149241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61157847379250957721532321 45868385534438218291149241)
    ·
      refine ⟨34401289150828663718361931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45868385534438218291149241 34401289150828663718361931)
      ·
        refine ⟨51601933726242995577542897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34401289150828663718361931 51601933726242995577542897)
        ·
          refine ⟨38701450294682246683157173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51601933726242995577542897 38701450294682246683157173)
          ·
            refine ⟨3628260965126460626545985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38701450294682246683157173 3628260965126460626545985)
            ·
              refine ⟨2721195723844845469909489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628260965126460626545985 2721195723844845469909489)
              ·
                refine ⟨2040896792883634102432117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721195723844845469909489 2040896792883634102432117)
                ·
                  refine ⟨191334074332840697103011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2040896792883634102432117 191334074332840697103011)
                  ·
                    rfl

theorem cell23_3353596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_3353596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353596 prefixEnd_3353596 := by exact prefixLift 3353596
  have htrace : WordTrace (prefixWord ++ tailWord_3353596) baseStart_3353596 baseEnd_3353596 := by
    simpa [prefixWord, tailWord_3353596, baseEnd_3353596] using wordTrace_append hprefix tailTrace_3353596
  have hstable : (prefixWord ++ tailWord_3353596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353596).length < 2 ^ (prefixWord ++ tailWord_3353596).sum := by decide
  have hdescent : baseEnd_3353596 < baseStart_3353596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353629 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3353629 : Nat := 118140960795 + 3353629 * 2 ^ 59
def prefixEnd_3353629 : Nat := 4983230072969 + 3 ^ 40 * 3353629 * 2
def baseEnd_3353629 : Nat := 1722023613857164644814447

theorem tailTrace_3353629 : CollatzResearch.WordTrace tailWord_3353629 prefixEnd_3353629 1722023613857164644814447 := by
  unfold tailWord_3353629
  simp only [CollatzResearch.WordTrace]
  refine ⟨122316898367382362079015941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81544598911588241386010627 122316898367382362079015941)
  ·
    refine ⟨22934418443884192889815489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122316898367382362079015941 22934418443884192889815489)
    ·
      refine ⟨17200813832913144667361617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22934418443884192889815489 17200813832913144667361617)
      ·
        refine ⟨12900610374684858500521213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17200813832913144667361617 12900610374684858500521213)
        ·
          refine ⟨4837728890506821937695455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12900610374684858500521213 4837728890506821937695455)
          ·
            refine ⟨7256593335760232906543183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837728890506821937695455 7256593335760232906543183)
            ·
              refine ⟨10884890003640349359814775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256593335760232906543183 10884890003640349359814775)
              ·
                refine ⟨16327335005460524039722163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10884890003640349359814775 16327335005460524039722163)
                ·
                  refine ⟨24491002508190786059583245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16327335005460524039722163 24491002508190786059583245)
                  ·
                    refine ⟨9184125940571544772343717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24491002508190786059583245 9184125940571544772343717)
                    ·
                      refine ⟨1722023613857164644814447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9184125940571544772343717 1722023613857164644814447)
                      ·
                        rfl

theorem cell23_3353629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3353629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353629 prefixEnd_3353629 := by exact prefixLift 3353629
  have htrace : WordTrace (prefixWord ++ tailWord_3353629) baseStart_3353629 baseEnd_3353629 := by
    simpa [prefixWord, tailWord_3353629, baseEnd_3353629] using wordTrace_append hprefix tailTrace_3353629
  have hstable : (prefixWord ++ tailWord_3353629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353629).length < 2 ^ (prefixWord ++ tailWord_3353629).sum := by decide
  have hdescent : baseEnd_3353629 < baseStart_3353629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353656 : List Nat := [2, 1, 2, 1, 5, 1, 2, 4, 1, 4]
def baseStart_3353656 : Nat := 118140960795 + 3353656 * 2 ^ 59
def prefixEnd_3353656 : Nat := 4983230072969 + 3 ^ 40 * 3353656 * 2
def baseEnd_3353656 : Nat := 574012492611612013058941

theorem tailTrace_3353656 : CollatzResearch.WordTrace tailWord_3353656 prefixEnd_3353656 574012492611612013058941 := by
  unfold tailWord_3353656
  simp only [CollatzResearch.WordTrace]
  refine ⟨61158941569142272845124411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81545255425523030460165881 61158941569142272845124411)
  ·
    refine ⟨91738412353713409267686617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61158941569142272845124411 91738412353713409267686617)
    ·
      refine ⟨68803809265285056950764963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91738412353713409267686617 68803809265285056950764963)
      ·
        refine ⟨103205713897927585426147445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68803809265285056950764963 103205713897927585426147445)
        ·
          refine ⟨9675535677930711133701323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103205713897927585426147445 9675535677930711133701323)
          ·
            refine ⟨14513303516896066700551985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9675535677930711133701323 14513303516896066700551985)
            ·
              refine ⟨10884977637672050025413989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14513303516896066700551985 10884977637672050025413989)
              ·
                refine ⟨2040933307063509379765123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10884977637672050025413989 2040933307063509379765123)
                ·
                  refine ⟨3061399960595264069647685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2040933307063509379765123 3061399960595264069647685)
                  ·
                    refine ⟨574012492611612013058941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3061399960595264069647685 574012492611612013058941)
                    ·
                      rfl

theorem cell23_3353656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 4, 1, 4].length) (baseStart_3353656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353656 prefixEnd_3353656 := by exact prefixLift 3353656
  have htrace : WordTrace (prefixWord ++ tailWord_3353656) baseStart_3353656 baseEnd_3353656 := by
    simpa [prefixWord, tailWord_3353656, baseEnd_3353656] using wordTrace_append hprefix tailTrace_3353656
  have hstable : (prefixWord ++ tailWord_3353656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353656).length < 2 ^ (prefixWord ++ tailWord_3353656).sum := by decide
  have hdescent : baseEnd_3353656 < baseStart_3353656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353706 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_3353706 : Nat := 118140960795 + 3353706 * 2 ^ 59
def prefixEnd_3353706 : Nat := 4983230072969 + 3 ^ 40 * 3353706 * 2
def baseEnd_3353706 : Nat := 1722063151867560843551593

theorem tailTrace_3353706 : CollatzResearch.WordTrace tailWord_3353706 prefixEnd_3353706 1722063151867560843551593 := by
  unfold tailWord_3353706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30579926697025851057392243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81546471192068936153045981 30579926697025851057392243)
  ·
    refine ⟨45869890045538776586088365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30579926697025851057392243 45869890045538776586088365)
    ·
      refine ⟨17201208767077041219783137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45869890045538776586088365 17201208767077041219783137)
      ·
        refine ⟨12900906575307780914837353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17201208767077041219783137 12900906575307780914837353)
        ·
          refine ⟨9675679931480835686128015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12900906575307780914837353 9675679931480835686128015)
          ·
            refine ⟨14513519897221253529192023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9675679931480835686128015 14513519897221253529192023)
            ·
              refine ⟨21770279845831880293788035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14513519897221253529192023 21770279845831880293788035)
              ·
                refine ⟨32655419768747820440682053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21770279845831880293788035 32655419768747820440682053)
                ·
                  refine ⟨6122891206640216332627885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32655419768747820440682053 6122891206640216332627885)
                  ·
                    refine ⟨2296084202490081124735457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6122891206640216332627885 2296084202490081124735457)
                    ·
                      refine ⟨1722063151867560843551593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296084202490081124735457 1722063151867560843551593)
                      ·
                        rfl

theorem cell23_3353706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_3353706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353706 prefixEnd_3353706 := by exact prefixLift 3353706
  have htrace : WordTrace (prefixWord ++ tailWord_3353706) baseStart_3353706 baseEnd_3353706 := by
    simpa [prefixWord, tailWord_3353706, baseEnd_3353706] using wordTrace_append hprefix tailTrace_3353706
  have hstable : (prefixWord ++ tailWord_3353706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353706).length < 2 ^ (prefixWord ++ tailWord_3353706).sum := by decide
  have hdescent : baseEnd_3353706 < baseStart_3353706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353733 : List Nat := [1, 3, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_3353733 : Nat := 118140960795 + 3353733 * 2 ^ 59
def prefixEnd_3353733 : Nat := 4983230072969 + 3 ^ 40 * 3353733 * 2
def baseEnd_3353733 : Nat := 574025671948410745971323

theorem tailTrace_3353733 : CollatzResearch.WordTrace tailWord_3353733 prefixEnd_3353733 574025671948410745971323 := by
  unfold tailWord_3353733
  simp only [CollatzResearch.WordTrace]
  refine ⟨122320691559005587840801853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81547127706003725227201235 122320691559005587840801853)
  ·
    refine ⟨45870259334627095440300695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122320691559005587840801853 45870259334627095440300695)
    ·
      refine ⟨68805389001940643160451043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45870259334627095440300695 68805389001940643160451043)
      ·
        refine ⟨103208083502910964740676565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68805389001940643160451043 103208083502910964740676565)
        ·
          refine ⟨2418939457099475736109607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 103208083502910964740676565 2418939457099475736109607)
          ·
            refine ⟨3628409185649213604164411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418939457099475736109607 3628409185649213604164411)
            ·
              refine ⟨5442613778473820406246617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628409185649213604164411 5442613778473820406246617)
              ·
                refine ⟨4081960333855365304684963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5442613778473820406246617 4081960333855365304684963)
                ·
                  refine ⟨6122940500783047957027445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4081960333855365304684963 6122940500783047957027445)
                  ·
                    refine ⟨574025671948410745971323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6122940500783047957027445 574025671948410745971323)
                    ·
                      rfl

theorem cell23_3353733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_3353733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353733 prefixEnd_3353733 := by exact prefixLift 3353733
  have htrace : WordTrace (prefixWord ++ tailWord_3353733) baseStart_3353733 baseEnd_3353733 := by
    simpa [prefixWord, tailWord_3353733, baseEnd_3353733] using wordTrace_append hprefix tailTrace_3353733
  have hstable : (prefixWord ++ tailWord_3353733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353733).length < 2 ^ (prefixWord ++ tailWord_3353733).sum := by decide
  have hdescent : baseEnd_3353733 < baseStart_3353733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353736 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3353736 : Nat := 118140960795 + 3353736 * 2 ^ 59
def prefixEnd_3353736 : Nat := 4983230072969 + 3 ^ 40 * 3353736 * 2
def baseEnd_3353736 : Nat := 1722078556287195726176455

theorem tailTrace_3353736 : CollatzResearch.WordTrace tailWord_3353736 prefixEnd_3353736 1722078556287195726176455 := by
  unfold tailWord_3353736
  simp only [CollatzResearch.WordTrace]
  refine ⟨61160400488997359676580531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81547200651996479568774041 61160400488997359676580531)
  ·
    refine ⟨91740600733496039514870797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61160400488997359676580531 91740600733496039514870797)
    ·
      refine ⟨34402725275061014818076549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91740600733496039514870797 34402725275061014818076549)
      ·
        refine ⟨6450510989073940278389353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34402725275061014818076549 6450510989073940278389353)
        ·
          refine ⟨4837883241805455208792015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450510989073940278389353 4837883241805455208792015)
          ·
            refine ⟨7256824862708182813188023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837883241805455208792015 7256824862708182813188023)
            ·
              refine ⟨10885237294062274219782035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256824862708182813188023 10885237294062274219782035)
              ·
                refine ⟨16327855941093411329673053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10885237294062274219782035 16327855941093411329673053)
                ·
                  refine ⟨6122945977910029248627395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16327855941093411329673053 6122945977910029248627395)
                  ·
                    refine ⟨9184418966865043872941093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6122945977910029248627395 9184418966865043872941093)
                    ·
                      refine ⟨1722078556287195726176455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9184418966865043872941093 1722078556287195726176455)
                      ·
                        rfl

theorem cell23_3353736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3353736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353736 prefixEnd_3353736 := by exact prefixLift 3353736
  have htrace : WordTrace (prefixWord ++ tailWord_3353736) baseStart_3353736 baseEnd_3353736 := by
    simpa [prefixWord, tailWord_3353736, baseEnd_3353736] using wordTrace_append hprefix tailTrace_3353736
  have hstable : (prefixWord ++ tailWord_3353736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353736).length < 2 ^ (prefixWord ++ tailWord_3353736).sum := by decide
  have hdescent : baseEnd_3353736 < baseStart_3353736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353756 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3353756 : Nat := 118140960795 + 3353756 * 2 ^ 59
def prefixEnd_3353756 : Nat := 4983230072969 + 3 ^ 40 * 3353756 * 2
def baseEnd_3353756 : Nat := 1722088825900285647926363

theorem tailTrace_3353756 : CollatzResearch.WordTrace tailWord_3353756 prefixEnd_3353756 1722088825900285647926363 := by
  unfold tailWord_3353756
  simp only [CollatzResearch.WordTrace]
  refine ⟨61160765218961131384444561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81547686958614841845926081 61160765218961131384444561)
  ·
    refine ⟨45870573914220848538333421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61160765218961131384444561 45870573914220848538333421)
    ·
      refine ⟨17201465217832818201875033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45870573914220848538333421 17201465217832818201875033)
      ·
        refine ⟨12901098913374613651406275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17201465217832818201875033 12901098913374613651406275)
        ·
          refine ⟨19351648370061920477109413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12901098913374613651406275 19351648370061920477109413)
          ·
            refine ⟨3628434069386610089458015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19351648370061920477109413 3628434069386610089458015)
            ·
              refine ⟨5442651104079915134187023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628434069386610089458015 5442651104079915134187023)
              ·
                refine ⟨8163976656119872701280535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5442651104079915134187023 8163976656119872701280535)
                ·
                  refine ⟨12245964984179809051920803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8163976656119872701280535 12245964984179809051920803)
                  ·
                    refine ⟨18368947476269713577881205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12245964984179809051920803 18368947476269713577881205)
                    ·
                      refine ⟨1722088825900285647926363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18368947476269713577881205 1722088825900285647926363)
                      ·
                        rfl

theorem cell23_3353756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3353756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353756 prefixEnd_3353756 := by exact prefixLift 3353756
  have htrace : WordTrace (prefixWord ++ tailWord_3353756) baseStart_3353756 baseEnd_3353756 := by
    simpa [prefixWord, tailWord_3353756, baseEnd_3353756] using wordTrace_append hprefix tailTrace_3353756
  have hstable : (prefixWord ++ tailWord_3353756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353756).length < 2 ^ (prefixWord ++ tailWord_3353756).sum := by decide
  have hdescent : baseEnd_3353756 < baseStart_3353756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353759 : List Nat := [1, 1, 2, 6, 3, 10]
def baseStart_3353759 : Nat := 118140960795 + 3353759 * 2 ^ 59
def prefixEnd_3353759 : Nat := 4983230072969 + 3 ^ 40 * 3353759 * 2
def baseEnd_3353759 : Nat := 7086791631038062288843

theorem tailTrace_3353759 : CollatzResearch.WordTrace tailWord_3353759 prefixEnd_3353759 7086791631038062288843 := by
  unfold tailWord_3353759
  simp only [CollatzResearch.WordTrace]
  refine ⟨122321639856911394281248331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81547759904607596187498887 122321639856911394281248331)
  ·
    refine ⟨183482459785367091421872497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122321639856911394281248331 183482459785367091421872497)
    ·
      refine ⟨137611844839025318566404373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183482459785367091421872497 137611844839025318566404373)
      ·
        refine ⟨6450555226829311807800205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137611844839025318566404373 6450555226829311807800205)
        ·
          refine ⟨2418958210060991927925077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6450555226829311807800205 2418958210060991927925077)
          ·
            refine ⟨7086791631038062288843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2418958210060991927925077 7086791631038062288843)
            ·
              rfl

theorem cell23_3353759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 10].length) (baseStart_3353759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353759 prefixEnd_3353759 := by exact prefixLift 3353759
  have htrace : WordTrace (prefixWord ++ tailWord_3353759) baseStart_3353759 baseEnd_3353759 := by
    simpa [prefixWord, tailWord_3353759, baseEnd_3353759] using wordTrace_append hprefix tailTrace_3353759
  have hstable : (prefixWord ++ tailWord_3353759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353759).length < 2 ^ (prefixWord ++ tailWord_3353759).sum := by decide
  have hdescent : baseEnd_3353759 < baseStart_3353759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353843 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 1, 4, 2]
def baseStart_3353843 : Nat := 118140960795 + 3353843 * 2 ^ 59
def prefixEnd_3353843 : Nat := 4983230072969 + 3 ^ 40 * 3353843 * 2
def baseEnd_3353843 : Nat := 1722133498717226807538463

theorem tailTrace_3353843 : CollatzResearch.WordTrace tailWord_3353843 prefixEnd_3353843 1722133498717226807538463 := by
  unfold tailWord_3353843
  simp only [CollatzResearch.WordTrace]
  refine ⟨122324703588607076627306183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81549802392404717751537455 122324703588607076627306183)
  ·
    refine ⟨183487055382910614940959275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122324703588607076627306183 183487055382910614940959275)
    ·
      refine ⟨275230583074365922411438913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183487055382910614940959275 275230583074365922411438913)
      ·
        refine ⟨206422937305774441808579185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275230583074365922411438913 206422937305774441808579185)
        ·
          refine ⟨154817202979330831356434389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206422937305774441808579185 154817202979330831356434389)
          ·
            refine ⟨3628528194828066359916431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 154817202979330831356434389 3628528194828066359916431)
            ·
              refine ⟨5442792292242099539874647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628528194828066359916431 5442792292242099539874647)
              ·
                refine ⟨8164188438363149309811971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5442792292242099539874647 8164188438363149309811971)
                ·
                  refine ⟨12246282657544723964717957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8164188438363149309811971 12246282657544723964717957)
                  ·
                    refine ⟨2296177998289635743384617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12246282657544723964717957 2296177998289635743384617)
                    ·
                      refine ⟨1722133498717226807538463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296177998289635743384617 1722133498717226807538463)
                      ·
                        rfl

theorem cell23_3353843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 4, 2].length) (baseStart_3353843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353843 prefixEnd_3353843 := by exact prefixLift 3353843
  have htrace : WordTrace (prefixWord ++ tailWord_3353843) baseStart_3353843 baseEnd_3353843 := by
    simpa [prefixWord, tailWord_3353843, baseEnd_3353843] using wordTrace_append hprefix tailTrace_3353843
  have hstable : (prefixWord ++ tailWord_3353843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353843).length < 2 ^ (prefixWord ++ tailWord_3353843).sum := by decide
  have hdescent : baseEnd_3353843 < baseStart_3353843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353913 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_3353913 : Nat := 118140960795 + 3353913 * 2 ^ 59
def prefixEnd_3353913 : Nat := 4983230072969 + 3 ^ 40 * 3353913 * 2
def baseEnd_3353913 : Nat := 574056480787680511221047

theorem tailTrace_3353913 : CollatzResearch.WordTrace tailWord_3353913 prefixEnd_3353913 574056480787680511221047 := by
  unfold tailWord_3353913
  simp only [CollatzResearch.WordTrace]
  refine ⟨122327256698353478582354393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81551504465568985721569595 122327256698353478582354393)
  ·
    refine ⟨91745442523765108936765795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122327256698353478582354393 91745442523765108936765795)
    ·
      refine ⟨137618163785647663405148693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91745442523765108936765795 137618163785647663405148693)
      ·
        refine ⟨6450851427452234222116345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137618163785647663405148693 6450851427452234222116345)
        ·
          refine ⟨4838138570589175666587259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450851427452234222116345 4838138570589175666587259)
          ·
            refine ⟨7257207855883763499880889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838138570589175666587259 7257207855883763499880889)
            ·
              refine ⟨5442905891912822624910667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7257207855883763499880889 5442905891912822624910667)
              ·
                refine ⟨8164358837869233937366001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5442905891912822624910667 8164358837869233937366001)
                ·
                  refine ⟨6123269128401925453024501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8164358837869233937366001 6123269128401925453024501)
                  ·
                    refine ⟨574056480787680511221047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6123269128401925453024501 574056480787680511221047)
                    ·
                      rfl

theorem cell23_3353913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_3353913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353913 prefixEnd_3353913 := by exact prefixLift 3353913
  have htrace : WordTrace (prefixWord ++ tailWord_3353913) baseStart_3353913 baseEnd_3353913 := by
    simpa [prefixWord, tailWord_3353913, baseEnd_3353913] using wordTrace_append hprefix tailTrace_3353913
  have hstable : (prefixWord ++ tailWord_3353913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353913).length < 2 ^ (prefixWord ++ tailWord_3353913).sum := by decide
  have hdescent : baseEnd_3353913 < baseStart_3353913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353916 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_3353916 : Nat := 118140960795 + 3353916 * 2 ^ 59
def prefixEnd_3353916 : Nat := 4983230072969 + 3 ^ 40 * 3353916 * 2
def baseEnd_3353916 : Nat := 1722170982805005021925627

theorem tailTrace_3353916 : CollatzResearch.WordTrace tailWord_3353916 prefixEnd_3353916 1722170982805005021925627 := by
  unfold tailWord_3353916
  simp only [CollatzResearch.WordTrace]
  refine ⟨61163683058671305047356801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81551577411561740063142401 61163683058671305047356801)
  ·
    refine ⟨45872762294003478785517601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61163683058671305047356801 45872762294003478785517601)
    ·
      refine ⟨34404571720502609089138201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45872762294003478785517601 34404571720502609089138201)
      ·
        refine ⟨25803428790376956816853651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34404571720502609089138201 25803428790376956816853651)
        ·
          refine ⟨38705143185565435225280477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25803428790376956816853651 38705143185565435225280477)
          ·
            refine ⟨14514428694587038209480179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38705143185565435225280477 14514428694587038209480179)
            ·
              refine ⟨21771643041880557314220269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14514428694587038209480179 21771643041880557314220269)
              ·
                refine ⟨8164366140705208992832601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21771643041880557314220269 8164366140705208992832601)
                ·
                  refine ⟨6123274605528906744624451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8164366140705208992832601 6123274605528906744624451)
                  ·
                    refine ⟨9184911908293360116936677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6123274605528906744624451 9184911908293360116936677)
                    ·
                      refine ⟨1722170982805005021925627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9184911908293360116936677 1722170982805005021925627)
                      ·
                        rfl

theorem cell23_3353916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_3353916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353916 prefixEnd_3353916 := by exact prefixLift 3353916
  have htrace : WordTrace (prefixWord ++ tailWord_3353916) baseStart_3353916 baseEnd_3353916 := by
    simpa [prefixWord, tailWord_3353916, baseEnd_3353916] using wordTrace_append hprefix tailTrace_3353916
  have hstable : (prefixWord ++ tailWord_3353916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353916).length < 2 ^ (prefixWord ++ tailWord_3353916).sum := by decide
  have hdescent : baseEnd_3353916 < baseStart_3353916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353936 : List Nat := [2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_3353936 : Nat := 118140960795 + 3353936 * 2 ^ 59
def prefixEnd_3353936 : Nat := 4983230072969 + 3 ^ 40 * 3353936 * 2
def baseEnd_3353936 : Nat := 1722181252418094943675535

theorem tailTrace_3353936 : CollatzResearch.WordTrace tailWord_3353936 prefixEnd_3353936 1722181252418094943675535 := by
  unfold tailWord_3353936
  simp only [CollatzResearch.WordTrace]
  refine ⟨61164047788635076755220831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81552063718180102340294441 61164047788635076755220831)
  ·
    refine ⟨91746071682952615132831247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61164047788635076755220831 91746071682952615132831247)
    ·
      refine ⟨137619107524428922699246871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91746071682952615132831247 137619107524428922699246871)
      ·
        refine ⟨206428661286643384048870307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137619107524428922699246871 206428661286643384048870307)
        ·
          refine ⟨309642991929965076073305461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206428661286643384048870307 309642991929965076073305461)
          ·
            refine ⟨29029030493434225881872387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309642991929965076073305461 29029030493434225881872387)
            ·
              refine ⟨43543545740151338822808581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29029030493434225881872387 43543545740151338822808581)
              ·
                refine ⟨8164414826278376029276609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43543545740151338822808581 8164414826278376029276609)
                ·
                  refine ⟨6123311119708782021957457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8164414826278376029276609 6123311119708782021957457)
                  ·
                    refine ⟨4592483339781586516468093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6123311119708782021957457 4592483339781586516468093)
                    ·
                      refine ⟨1722181252418094943675535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4592483339781586516468093 1722181252418094943675535)
                      ·
                        rfl

theorem cell23_3353936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_3353936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353936 prefixEnd_3353936 := by exact prefixLift 3353936
  have htrace : WordTrace (prefixWord ++ tailWord_3353936) baseStart_3353936 baseEnd_3353936 := by
    simpa [prefixWord, tailWord_3353936, baseEnd_3353936] using wordTrace_append hprefix tailTrace_3353936
  have hstable : (prefixWord ++ tailWord_3353936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353936).length < 2 ^ (prefixWord ++ tailWord_3353936).sum := by decide
  have hdescent : baseEnd_3353936 < baseStart_3353936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3353956 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 6]
def baseStart_3353956 : Nat := 118140960795 + 3353956 * 2 ^ 59
def prefixEnd_3353956 : Nat := 4983230072969 + 3 ^ 40 * 3353956 * 2
def baseEnd_3353956 : Nat := 191354613559020540602827

theorem tailTrace_3353956 : CollatzResearch.WordTrace tailWord_3353956 prefixEnd_3353956 191354613559020540602827 := by
  unfold tailWord_3353956
  simp only [CollatzResearch.WordTrace]
  refine ⟨61164412518598848463084861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81552550024798464617446481 61164412518598848463084861)
  ·
    refine ⟨22936654694474568173656823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61164412518598848463084861 22936654694474568173656823)
    ·
      refine ⟨34404982041711852260485235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22936654694474568173656823 34404982041711852260485235)
      ·
        refine ⟨51607473062567778390727853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34404982041711852260485235 51607473062567778390727853)
        ·
          refine ⟨19352802398462916896522945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51607473062567778390727853 19352802398462916896522945)
          ·
            refine ⟨14514601798847187672392209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19352802398462916896522945 14514601798847187672392209)
            ·
              refine ⟨10885951349135390754294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14514601798847187672392209 10885951349135390754294157)
              ·
                refine ⟨4082231755925771532860309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10885951349135390754294157 4082231755925771532860309)
                ·
                  refine ⟨191354613559020540602827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4082231755925771532860309 191354613559020540602827)
                  ·
                    rfl

theorem cell23_3353956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_3353956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3353956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3353956 prefixEnd_3353956 := by exact prefixLift 3353956
  have htrace : WordTrace (prefixWord ++ tailWord_3353956) baseStart_3353956 baseEnd_3353956 := by
    simpa [prefixWord, tailWord_3353956, baseEnd_3353956] using wordTrace_append hprefix tailTrace_3353956
  have hstable : (prefixWord ++ tailWord_3353956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3353956).length < 2 ^ (prefixWord ++ tailWord_3353956).sum := by decide
  have hdescent : baseEnd_3353956 < baseStart_3353956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3353956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354023 : List Nat := [1, 1, 6, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_3354023 : Nat := 118140960795 + 3354023 * 2 ^ 59
def prefixEnd_3354023 : Nat := 4983230072969 + 3 ^ 40 * 3354023 * 2
def baseEnd_3354023 : Nat := 1722225925235036103287635

theorem tailTrace_3354023 : CollatzResearch.WordTrace tailWord_3354023 prefixEnd_3354023 1722225925235036103287635 := by
  unfold tailWord_3354023
  simp only [CollatzResearch.WordTrace]
  refine ⟨122331268727954967368858723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81554179151969978245905815 122331268727954967368858723)
  ·
    refine ⟨183496903091932451053288085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122331268727954967368858723 183496903091932451053288085)
    ·
      refine ⟨8601417332434333643122879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183496903091932451053288085 8601417332434333643122879)
      ·
        refine ⟨12902125998651500464684319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601417332434333643122879 12902125998651500464684319)
        ·
          refine ⟨19353188997977250697026479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12902125998651500464684319 19353188997977250697026479)
          ·
            refine ⟨29029783496965876045539719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19353188997977250697026479 29029783496965876045539719)
            ·
              refine ⟨43544675245448814068309579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29029783496965876045539719 43544675245448814068309579)
              ·
                refine ⟨65317012868173221102464369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43544675245448814068309579 65317012868173221102464369)
                ·
                  refine ⟨48987759651129915826848277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65317012868173221102464369 48987759651129915826848277)
                  ·
                    refine ⟨2296301233646714804383513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48987759651129915826848277 2296301233646714804383513)
                    ·
                      refine ⟨1722225925235036103287635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296301233646714804383513 1722225925235036103287635)
                      ·
                        rfl

theorem cell23_3354023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_3354023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354023 prefixEnd_3354023 := by exact prefixLift 3354023
  have htrace : WordTrace (prefixWord ++ tailWord_3354023) baseStart_3354023 baseEnd_3354023 := by
    simpa [prefixWord, tailWord_3354023, baseEnd_3354023] using wordTrace_append hprefix tailTrace_3354023
  have hstable : (prefixWord ++ tailWord_3354023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354023).length < 2 ^ (prefixWord ++ tailWord_3354023).sum := by decide
  have hdescent : baseEnd_3354023 < baseStart_3354023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354077 : List Nat := [1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3354077 : Nat := 118140960795 + 3354077 * 2 ^ 59
def prefixEnd_3354077 : Nat := 4983230072969 + 3 ^ 40 * 3354077 * 2
def baseEnd_3354077 : Nat := 1722253653190378892012387

theorem tailTrace_3354077 : CollatzResearch.WordTrace tailWord_3354077 prefixEnd_3354077 1722253653190378892012387 := by
  unfold tailWord_3354077
  simp only [CollatzResearch.WordTrace]
  refine ⟨122333238269759334591324485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81555492179839556394216323 122333238269759334591324485)
  ·
    refine ⟨22937482175579875235873341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122333238269759334591324485 22937482175579875235873341)
    ·
      refine ⟨8601555815842453213452503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22937482175579875235873341 8601555815842453213452503)
      ·
        refine ⟨12902333723763679820178755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8601555815842453213452503 12902333723763679820178755)
        ·
          refine ⟨19353500585645519730268133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12902333723763679820178755 19353500585645519730268133)
          ·
            refine ⟨3628781359808534949425275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19353500585645519730268133 3628781359808534949425275)
            ·
              refine ⟨5443172039712802424137913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628781359808534949425275 5443172039712802424137913)
              ·
                refine ⟨4082379029784601818103435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5443172039712802424137913 4082379029784601818103435)
                ·
                  refine ⟨6123568544676902727155153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082379029784601818103435 6123568544676902727155153)
                  ·
                    refine ⟨4592676408507677045366365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6123568544676902727155153 4592676408507677045366365)
                    ·
                      refine ⟨1722253653190378892012387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4592676408507677045366365 1722253653190378892012387)
                      ·
                        rfl

theorem cell23_3354077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3354077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354077 prefixEnd_3354077 := by exact prefixLift 3354077
  have htrace : WordTrace (prefixWord ++ tailWord_3354077) baseStart_3354077 baseEnd_3354077 := by
    simpa [prefixWord, tailWord_3354077, baseEnd_3354077] using wordTrace_append hprefix tailTrace_3354077
  have hstable : (prefixWord ++ tailWord_3354077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354077).length < 2 ^ (prefixWord ++ tailWord_3354077).sum := by decide
  have hdescent : baseEnd_3354077 < baseStart_3354077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354090 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3354090 : Nat := 118140960795 + 3354090 * 2 ^ 59
def prefixEnd_3354090 : Nat := 4983230072969 + 3 ^ 40 * 3354090 * 2
def baseEnd_3354090 : Nat := 1722260328438887341149827

theorem tailTrace_3354090 : CollatzResearch.WordTrace tailWord_3354090 prefixEnd_3354090 1722260328438887341149827 := by
  unfold tailWord_3354090
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583428104678059452886931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81555808279141491874365149 30583428104678059452886931)
  ·
    refine ⟨45875142157017089179330397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30583428104678059452886931 45875142157017089179330397)
    ·
      refine ⟨17203178308881408442248899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45875142157017089179330397 17203178308881408442248899)
      ·
        refine ⟨25804767463322112663373349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17203178308881408442248899 25804767463322112663373349)
        ·
          refine ⟨4838393899372896124382503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25804767463322112663373349 4838393899372896124382503)
          ·
            refine ⟨7257590849059344186573755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838393899372896124382503 7257590849059344186573755)
            ·
              refine ⟨10886386273589016279860633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257590849059344186573755 10886386273589016279860633)
              ·
                refine ⟨8164789705191762209895475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10886386273589016279860633 8164789705191762209895475)
                ·
                  refine ⟨12247184557787643314843213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8164789705191762209895475 12247184557787643314843213)
                  ·
                    refine ⟨4592694209170366243066205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12247184557787643314843213 4592694209170366243066205)
                    ·
                      refine ⟨1722260328438887341149827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4592694209170366243066205 1722260328438887341149827)
                      ·
                        rfl

theorem cell23_3354090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3354090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354090 prefixEnd_3354090 := by exact prefixLift 3354090
  have htrace : WordTrace (prefixWord ++ tailWord_3354090) baseStart_3354090 baseEnd_3354090 := by
    simpa [prefixWord, tailWord_3354090, baseEnd_3354090] using wordTrace_append hprefix tailTrace_3354090
  have hstable : (prefixWord ++ tailWord_3354090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354090).length < 2 ^ (prefixWord ++ tailWord_3354090).sum := by decide
  have hdescent : baseEnd_3354090 < baseStart_3354090 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354106 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_3354106 : Nat := 118140960795 + 3354106 * 2 ^ 59
def prefixEnd_3354106 : Nat := 4983230072969 + 3 ^ 40 * 3354106 * 2
def baseEnd_3354106 : Nat := 574089514709786426183251

theorem tailTrace_3354106 : CollatzResearch.WordTrace tailWord_3354106 prefixEnd_3354106 574089514709786426183251 := by
  unfold tailWord_3354106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30583573996663568136032543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81556197324436181696086781 30583573996663568136032543)
  ·
    refine ⟨45875360994995352204048815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30583573996663568136032543 45875360994995352204048815)
    ·
      refine ⟨68813041492493028306073223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45875360994995352204048815 68813041492493028306073223)
      ·
        refine ⟨103219562238739542459109835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68813041492493028306073223 103219562238739542459109835)
        ·
          refine ⟨154829343358109313688664753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103219562238739542459109835 154829343358109313688664753)
          ·
            refine ⟨116122007518581985266498565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154829343358109313688664753 116122007518581985266498565)
            ·
              refine ⟨21772876409734122237468481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116122007518581985266498565 21772876409734122237468481)
              ·
                refine ⟨16329657307300591678101361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21772876409734122237468481 16329657307300591678101361)
                ·
                  refine ⟨12247242980475443758576021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16329657307300591678101361 12247242980475443758576021)
                  ·
                    refine ⟨574089514709786426183251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12247242980475443758576021 574089514709786426183251)
                    ·
                      rfl

theorem cell23_3354106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_3354106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354106 prefixEnd_3354106 := by exact prefixLift 3354106
  have htrace : WordTrace (prefixWord ++ tailWord_3354106) baseStart_3354106 baseEnd_3354106 := by
    simpa [prefixWord, tailWord_3354106, baseEnd_3354106] using wordTrace_append hprefix tailTrace_3354106
  have hstable : (prefixWord ++ tailWord_3354106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354106).length < 2 ^ (prefixWord ++ tailWord_3354106).sum := by decide
  have hdescent : baseEnd_3354106 < baseStart_3354106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354123 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 2, 6]
def baseStart_3354123 : Nat := 118140960795 + 3354123 * 2 ^ 59
def prefixEnd_3354123 : Nat := 4983230072969 + 3 ^ 40 * 3354123 * 2
def baseEnd_3354123 : Nat := 574092424433495237345725

theorem tailTrace_3354123 : CollatzResearch.WordTrace tailWord_3354123 prefixEnd_3354123 574092424433495237345725 := by
  unfold tailWord_3354123
  simp only [CollatzResearch.WordTrace]
  refine ⟨122334916027592684447499023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81556610685061789631666015 122334916027592684447499023)
  ·
    refine ⟨183502374041389026671248535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122334916027592684447499023 183502374041389026671248535)
    ·
      refine ⟨275253561062083540006872803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183502374041389026671248535 275253561062083540006872803)
      ·
        refine ⟨412880341593125310010309205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275253561062083540006872803 412880341593125310010309205)
        ·
          refine ⟨4838441503044437226683311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 412880341593125310010309205 4838441503044437226683311)
          ·
            refine ⟨7257662254566655840024967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838441503044437226683311 7257662254566655840024967)
            ·
              refine ⟨10886493381849983760037451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7257662254566655840024967 10886493381849983760037451)
              ·
                refine ⟨16329740072774975640056177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10886493381849983760037451 16329740072774975640056177)
                ·
                  refine ⟨12247305054581231730042133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16329740072774975640056177 12247305054581231730042133)
                  ·
                    refine ⟨574092424433495237345725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12247305054581231730042133 574092424433495237345725)
                    ·
                      rfl

theorem cell23_3354123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 2, 6].length) (baseStart_3354123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354123 prefixEnd_3354123 := by exact prefixLift 3354123
  have htrace : WordTrace (prefixWord ++ tailWord_3354123) baseStart_3354123 baseEnd_3354123 := by
    simpa [prefixWord, tailWord_3354123, baseEnd_3354123] using wordTrace_append hprefix tailTrace_3354123
  have hstable : (prefixWord ++ tailWord_3354123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354123).length < 2 ^ (prefixWord ++ tailWord_3354123).sum := by decide
  have hdescent : baseEnd_3354123 < baseStart_3354123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354163 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3]
def baseStart_3354163 : Nat := 118140960795 + 3354163 * 2 ^ 59
def prefixEnd_3354163 : Nat := 4983230072969 + 3 ^ 40 * 3354163 * 2
def baseEnd_3354163 : Nat := 1722297812526665555536991

theorem tailTrace_3354163 : CollatzResearch.WordTrace tailWord_3354163 prefixEnd_3354163 1722297812526665555536991 := by
  unfold tailWord_3354163
  simp only [CollatzResearch.WordTrace]
  refine ⟨122336374947447771278955143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81557583298298514185970095 122336374947447771278955143)
  ·
    refine ⟨183504562421171656918432715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122336374947447771278955143 183504562421171656918432715)
    ·
      refine ⟨275256843631757485377649073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183504562421171656918432715 275256843631757485377649073)
      ·
        refine ⟨206442632723818114033236805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275256843631757485377649073 206442632723818114033236805)
        ·
          refine ⟨38707993635715896381231901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206442632723818114033236805 38707993635715896381231901)
          ·
            refine ⟨14515497613393461142961963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38707993635715896381231901 14515497613393461142961963)
            ·
              refine ⟨21773246420090191714442945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14515497613393461142961963 21773246420090191714442945)
              ·
                refine ⟨16329934815067643785832209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21773246420090191714442945 16329934815067643785832209)
                ·
                  refine ⟨12247451111300732839374157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16329934815067643785832209 12247451111300732839374157)
                  ·
                    refine ⟨4592794166737774814765309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12247451111300732839374157 4592794166737774814765309)
                    ·
                      refine ⟨1722297812526665555536991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4592794166737774814765309 1722297812526665555536991)
                      ·
                        rfl

theorem cell23_3354163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 3, 3].length) (baseStart_3354163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354163 prefixEnd_3354163 := by exact prefixLift 3354163
  have htrace : WordTrace (prefixWord ++ tailWord_3354163) baseStart_3354163 baseEnd_3354163 := by
    simpa [prefixWord, tailWord_3354163, baseEnd_3354163] using wordTrace_append hprefix tailTrace_3354163
  have hstable : (prefixWord ++ tailWord_3354163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354163).length < 2 ^ (prefixWord ++ tailWord_3354163).sum := by decide
  have hdescent : baseEnd_3354163 < baseStart_3354163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354176 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_3354176 : Nat := 118140960795 + 3354176 * 2 ^ 59
def prefixEnd_3354176 : Nat := 4983230072969 + 3 ^ 40 * 3354176 * 2
def baseEnd_3354176 : Nat := 1722304487775174004674431

theorem tailTrace_3354176 : CollatzResearch.WordTrace tailWord_3354176 prefixEnd_3354176 1722304487775174004674431 := by
  unfold tailWord_3354176
  simp only [CollatzResearch.WordTrace]
  refine ⟨61168424548200337249589191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81557899397600449666118921 61168424548200337249589191)
  ·
    refine ⟨91752636822300505874383787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61168424548200337249589191 91752636822300505874383787)
    ·
      refine ⟨137628955233450758811575681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91752636822300505874383787 137628955233450758811575681)
      ·
        refine ⟨103221716425088069108681761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137628955233450758811575681 103221716425088069108681761)
        ·
          refine ⟨77416287318816051831511321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103221716425088069108681761 77416287318816051831511321)
          ·
            refine ⟨58062215489112038873633491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77416287318816051831511321 58062215489112038873633491)
            ·
              refine ⟨87093323233668058310450237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58062215489112038873633491 87093323233668058310450237)
              ·
                refine ⟨32659996212625521866418839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87093323233668058310450237 32659996212625521866418839)
                ·
                  refine ⟨48989994318938282799628259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32659996212625521866418839 48989994318938282799628259)
                  ·
                    refine ⟨73484991478407424199442389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48989994318938282799628259 73484991478407424199442389)
                    ·
                      refine ⟨1722304487775174004674431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73484991478407424199442389 1722304487775174004674431)
                      ·
                        rfl

theorem cell23_3354176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_3354176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354176 prefixEnd_3354176 := by exact prefixLift 3354176
  have htrace : WordTrace (prefixWord ++ tailWord_3354176) baseStart_3354176 baseEnd_3354176 := by
    simpa [prefixWord, tailWord_3354176, baseEnd_3354176] using wordTrace_append hprefix tailTrace_3354176
  have hstable : (prefixWord ++ tailWord_3354176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354176).length < 2 ^ (prefixWord ++ tailWord_3354176).sum := by decide
  have hdescent : baseEnd_3354176 < baseStart_3354176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354323 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4]
def baseStart_3354323 : Nat := 118140960795 + 3354323 * 2 ^ 59
def prefixEnd_3354323 : Nat := 4983230072969 + 3 ^ 40 * 3354323 * 2
def baseEnd_3354323 : Nat := 1722379969431384929536255

theorem tailTrace_3354323 : CollatzResearch.WordTrace tailWord_3354323 prefixEnd_3354323 1722379969431384929536255 := by
  unfold tailWord_3354323
  simp only [CollatzResearch.WordTrace]
  refine ⟨122342210626868118604779623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81561473751245412403186415 122342210626868118604779623)
  ·
    refine ⟨183513315940302177907169435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122342210626868118604779623 183513315940302177907169435)
    ·
      refine ⟨275269973910453266860754153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183513315940302177907169435 275269973910453266860754153)
      ·
        refine ⟨206452480432839950145565615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275269973910453266860754153 206452480432839950145565615)
        ·
          refine ⟨309678720649259925218348423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206452480432839950145565615 309678720649259925218348423)
          ·
            refine ⟨464518080973889887827522635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309678720649259925218348423 464518080973889887827522635)
            ·
              refine ⟨696777121460834831741283953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464518080973889887827522635 696777121460834831741283953)
              ·
                refine ⟨522582841095626123805962965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 696777121460834831741283953 522582841095626123805962965)
                ·
                  refine ⟨12248035338178737276702257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 522582841095626123805962965 12248035338178737276702257)
                  ·
                    refine ⟨9186026503634052957526693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12248035338178737276702257 9186026503634052957526693)
                    ·
                      refine ⟨1722379969431384929536255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9186026503634052957526693 1722379969431384929536255)
                      ·
                        rfl

theorem cell23_3354323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 7, 2, 4].length) (baseStart_3354323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354323 prefixEnd_3354323 := by exact prefixLift 3354323
  have htrace : WordTrace (prefixWord ++ tailWord_3354323) baseStart_3354323 baseEnd_3354323 := by
    simpa [prefixWord, tailWord_3354323, baseEnd_3354323] using wordTrace_append hprefix tailTrace_3354323
  have hstable : (prefixWord ++ tailWord_3354323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354323).length < 2 ^ (prefixWord ++ tailWord_3354323).sum := by decide
  have hdescent : baseEnd_3354323 < baseStart_3354323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354324 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_3354324 : Nat := 118140960795 + 3354324 * 2 ^ 59
def prefixEnd_3354324 : Nat := 4983230072969 + 3 ^ 40 * 3354324 * 2
def baseEnd_3354324 : Nat := 574126827637346475207917

theorem tailTrace_3354324 : CollatzResearch.WordTrace tailWord_3354324 prefixEnd_3354324 574126827637346475207917 := by
  unfold tailWord_3354324
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171123549932247887783013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81561498066576330517044017 61171123549932247887783013)
  ·
    refine ⟨11469585665612296478959315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61171123549932247887783013 11469585665612296478959315)
    ·
      refine ⟨17204378498418444718438973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469585665612296478959315 17204378498418444718438973)
      ·
        refine ⟨6451641936906916769414615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17204378498418444718438973 6451641936906916769414615)
        ·
          refine ⟨9677462905360375154121923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6451641936906916769414615 9677462905360375154121923)
          ·
            refine ⟨14516194358040562731182885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9677462905360375154121923 14516194358040562731182885)
            ·
              refine ⟨2721786442132605512096791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14516194358040562731182885 2721786442132605512096791)
              ·
                refine ⟨4082679663198908268145187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721786442132605512096791 4082679663198908268145187)
                ·
                  refine ⟨6124019494798362402217781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4082679663198908268145187 6124019494798362402217781)
                  ·
                    refine ⟨574126827637346475207917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6124019494798362402217781 574126827637346475207917)
                    ·
                      rfl

theorem cell23_3354324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_3354324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354324 prefixEnd_3354324 := by exact prefixLift 3354324
  have htrace : WordTrace (prefixWord ++ tailWord_3354324) baseStart_3354324 baseEnd_3354324 := by
    simpa [prefixWord, tailWord_3354324, baseEnd_3354324] using wordTrace_append hprefix tailTrace_3354324
  have hstable : (prefixWord ++ tailWord_3354324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354324).length < 2 ^ (prefixWord ++ tailWord_3354324).sum := by decide
  have hdescent : baseEnd_3354324 < baseStart_3354324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354327 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 5, 2, 2]
def baseStart_3354327 : Nat := 118140960795 + 3354327 * 2 ^ 59
def prefixEnd_3354327 : Nat := 4983230072969 + 3 ^ 40 * 3354327 * 2
def baseEnd_3354327 : Nat := 1722382023354002913886237

theorem tailTrace_3354327 : CollatzResearch.WordTrace tailWord_3354327 prefixEnd_3354327 1722382023354002913886237 := by
  unfold tailWord_3354327
  simp only [CollatzResearch.WordTrace]
  refine ⟨122342356518853627287925235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81561571012569084858616823 122342356518853627287925235)
  ·
    refine ⟨183513534778280440931887853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122342356518853627287925235 183513534778280440931887853)
    ·
      refine ⟨68817575541855165349457945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183513534778280440931887853 68817575541855165349457945)
      ·
        refine ⟨51613181656391374012093459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68817575541855165349457945 51613181656391374012093459)
        ·
          refine ⟨77419772484587061018140189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51613181656391374012093459 77419772484587061018140189)
          ·
            refine ⟨29032414681720147881802571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77419772484587061018140189 29032414681720147881802571)
            ·
              refine ⟨43548622022580221822703857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29032414681720147881802571 43548622022580221822703857)
              ·
                refine ⟨32661466516935166367027893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43548622022580221822703857 32661466516935166367027893)
                ·
                  refine ⟨3062012485962671846908865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32661466516935166367027893 3062012485962671846908865)
                  ·
                    refine ⟨2296509364472003885181649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3062012485962671846908865 2296509364472003885181649)
                    ·
                      refine ⟨1722382023354002913886237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296509364472003885181649 1722382023354002913886237)
                      ·
                        rfl

theorem cell23_3354327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 2, 2].length) (baseStart_3354327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354327 prefixEnd_3354327 := by exact prefixLift 3354327
  have htrace : WordTrace (prefixWord ++ tailWord_3354327) baseStart_3354327 baseEnd_3354327 := by
    simpa [prefixWord, tailWord_3354327, baseEnd_3354327] using wordTrace_append hprefix tailTrace_3354327
  have hstable : (prefixWord ++ tailWord_3354327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354327).length < 2 ^ (prefixWord ++ tailWord_3354327).sum := by decide
  have hdescent : baseEnd_3354327 < baseStart_3354327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354337 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_3354337 : Nat := 118140960795 + 3354337 * 2 ^ 59
def prefixEnd_3354337 : Nat := 4983230072969 + 3 ^ 40 * 3354337 * 2
def baseEnd_3354337 : Nat := 574129052720182624920397

theorem tailTrace_3354337 : CollatzResearch.WordTrace tailWord_3354337 prefixEnd_3354337 574129052720182624920397 := by
  unfold tailWord_3354337
  simp only [CollatzResearch.WordTrace]
  refine ⟨122342721248817398995789265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81561814165878265997192843 122342721248817398995789265)
  ·
    refine ⟨91757040936613049246841949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122342721248817398995789265 91757040936613049246841949)
    ·
      refine ⟨34408890351229893467565731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91757040936613049246841949 34408890351229893467565731)
      ·
        refine ⟨51613335526844840201348597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34408890351229893467565731 51613335526844840201348597)
        ·
          refine ⟨4838750205641703768876431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51613335526844840201348597 4838750205641703768876431)
          ·
            refine ⟨7258125308462555653314647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838750205641703768876431 7258125308462555653314647)
            ·
              refine ⟨10887187962693833479971971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7258125308462555653314647 10887187962693833479971971)
              ·
                refine ⟨16330781944040750219957957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10887187962693833479971971 16330781944040750219957957)
                ·
                  refine ⟨3062021614507640666242117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16330781944040750219957957 3062021614507640666242117)
                  ·
                    refine ⟨574129052720182624920397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062021614507640666242117 574129052720182624920397)
                    ·
                      rfl

theorem cell23_3354337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_3354337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354337 prefixEnd_3354337 := by exact prefixLift 3354337
  have htrace : WordTrace (prefixWord ++ tailWord_3354337) baseStart_3354337 baseEnd_3354337 := by
    simpa [prefixWord, tailWord_3354337, baseEnd_3354337] using wordTrace_append hprefix tailTrace_3354337
  have hstable : (prefixWord ++ tailWord_3354337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354337).length < 2 ^ (prefixWord ++ tailWord_3354337).sum := by decide
  have hdescent : baseEnd_3354337 < baseStart_3354337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354344 : List Nat := [2, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_3354344 : Nat := 118140960795 + 3354344 * 2 ^ 59
def prefixEnd_3354344 : Nat := 4983230072969 + 3 ^ 40 * 3354344 * 2
def baseEnd_3354344 : Nat := 1722390752525129347373659

theorem tailTrace_3354344 : CollatzResearch.WordTrace tailWord_3354344 prefixEnd_3354344 1722390752525129347373659 := by
  unfold tailWord_3354344
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171488279896019595647043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81561984373194692794196057 61171488279896019595647043)
  ·
    refine ⟨91757232419844029393470565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61171488279896019595647043 91757232419844029393470565)
    ·
      refine ⟨17204481078720755511275731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91757232419844029393470565 17204481078720755511275731)
      ·
        refine ⟨25806721618081133266913597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17204481078720755511275731 25806721618081133266913597)
        ·
          refine ⟨9677520606780424975092599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25806721618081133266913597 9677520606780424975092599)
          ·
            refine ⟨14516280910170637462638899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9677520606780424975092599 14516280910170637462638899)
            ·
              refine ⟨21774421365255956193958349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14516280910170637462638899 21774421365255956193958349)
              ·
                refine ⟨8165408011970983572734381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21774421365255956193958349 8165408011970983572734381)
                ·
                  refine ⟨3062028004489118839775393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8165408011970983572734381 3062028004489118839775393)
                  ·
                    refine ⟨2296521003366839129831545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3062028004489118839775393 2296521003366839129831545)
                    ·
                      refine ⟨1722390752525129347373659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296521003366839129831545 1722390752525129347373659)
                      ·
                        rfl

theorem cell23_3354344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_3354344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354344 prefixEnd_3354344 := by exact prefixLift 3354344
  have htrace : WordTrace (prefixWord ++ tailWord_3354344) baseStart_3354344 baseEnd_3354344 := by
    simpa [prefixWord, tailWord_3354344, baseEnd_3354344] using wordTrace_append hprefix tailTrace_3354344
  have hstable : (prefixWord ++ tailWord_3354344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354344).length < 2 ^ (prefixWord ++ tailWord_3354344).sum := by decide
  have hdescent : baseEnd_3354344 < baseStart_3354344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354354 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3354354 : Nat := 118140960795 + 3354354 * 2 ^ 59
def prefixEnd_3354354 : Nat := 4983230072969 + 3 ^ 40 * 3354354 * 2
def baseEnd_3354354 : Nat := 574131962443891436082871

theorem tailTrace_3354354 : CollatzResearch.WordTrace tailWord_3354354 prefixEnd_3354354 574131962443891436082871 := by
  unfold tailWord_3354354
  simp only [CollatzResearch.WordTrace]
  refine ⟨30585835322438952724789529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81562227526503873932772077 30585835322438952724789529)
  ·
    refine ⟨22939376491829214543592147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30585835322438952724789529 22939376491829214543592147)
    ·
      refine ⟨34409064737743821815388221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22939376491829214543592147 34409064737743821815388221)
      ·
        refine ⟨12903399276653933180770583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34409064737743821815388221 12903399276653933180770583)
        ·
          refine ⟨19355098914980899771155875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12903399276653933180770583 19355098914980899771155875)
          ·
            refine ⟨29032648372471349656733813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355098914980899771155875 29032648372471349656733813)
            ·
              refine ⟨2721810784919189030318795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29032648372471349656733813 2721810784919189030318795)
              ·
                refine ⟨4082716177378783545478193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721810784919189030318795 4082716177378783545478193)
                ·
                  refine ⟨3062037133034087659108645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4082716177378783545478193 3062037133034087659108645)
                  ·
                    refine ⟨574131962443891436082871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062037133034087659108645 574131962443891436082871)
                    ·
                      rfl

theorem cell23_3354354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3354354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354354 prefixEnd_3354354 := by exact prefixLift 3354354
  have htrace : WordTrace (prefixWord ++ tailWord_3354354) baseStart_3354354 baseEnd_3354354 := by
    simpa [prefixWord, tailWord_3354354, baseEnd_3354354] using wordTrace_append hprefix tailTrace_3354354
  have hstable : (prefixWord ++ tailWord_3354354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354354).length < 2 ^ (prefixWord ++ tailWord_3354354).sum := by decide
  have hdescent : baseEnd_3354354 < baseStart_3354354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354360 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_3354360 : Nat := 118140960795 + 3354360 * 2 ^ 59
def prefixEnd_3354360 : Nat := 4983230072969 + 3 ^ 40 * 3354360 * 2
def baseEnd_3354360 : Nat := 1722398968215601284773585

theorem tailTrace_3354360 : CollatzResearch.WordTrace tailWord_3354360 prefixEnd_3354360 1722398968215601284773585 := by
  unfold tailWord_3354360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171780063867036961938267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81562373418489382615917689 61171780063867036961938267)
  ·
    refine ⟨91757670095800555442907401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61171780063867036961938267 91757670095800555442907401)
    ·
      refine ⟨68818252571850416582180551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91757670095800555442907401 68818252571850416582180551)
      ·
        refine ⟨103227378857775624873270827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68818252571850416582180551 103227378857775624873270827)
        ·
          refine ⟨154841068286663437309906241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103227378857775624873270827 154841068286663437309906241)
          ·
            refine ⟨116130801214997577982429681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154841068286663437309906241 116130801214997577982429681)
            ·
              refine ⟨87098100911248183486822261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116130801214997577982429681 87098100911248183486822261)
              ·
                refine ⟨8165446960429517201889587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87098100911248183486822261 8165446960429517201889587)
                ·
                  refine ⟨12248170440644275802834381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8165446960429517201889587 12248170440644275802834381)
                  ·
                    refine ⟨4593063915241603426062893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12248170440644275802834381 4593063915241603426062893)
                    ·
                      refine ⟨1722398968215601284773585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4593063915241603426062893 1722398968215601284773585)
                      ·
                        rfl

theorem cell23_3354360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_3354360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354360 prefixEnd_3354360 := by exact prefixLift 3354360
  have htrace : WordTrace (prefixWord ++ tailWord_3354360) baseStart_3354360 baseEnd_3354360 := by
    simpa [prefixWord, tailWord_3354360, baseEnd_3354360] using wordTrace_append hprefix tailTrace_3354360
  have hstable : (prefixWord ++ tailWord_3354360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354360).length < 2 ^ (prefixWord ++ tailWord_3354360).sum := by decide
  have hdescent : baseEnd_3354360 < baseStart_3354360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354378 : List Nat := [3, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2]
def baseStart_3354378 : Nat := 118140960795 + 3354378 * 2 ^ 59
def prefixEnd_3354378 : Nat := 4983230072969 + 3 ^ 40 * 3354378 * 2
def baseEnd_3354378 : Nat := 1722408210867382214348503

theorem tailTrace_3354378 : CollatzResearch.WordTrace tailWord_3354378 prefixEnd_3354378 1722408210867382214348503 := by
  unfold tailWord_3354378
  simp only [CollatzResearch.WordTrace]
  refine ⟨30586054160417215749507947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81562811094445908665354525 30586054160417215749507947)
  ·
    refine ⟨45879081240625823624261921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30586054160417215749507947 45879081240625823624261921)
    ·
      refine ⟨34409310930469367718196441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45879081240625823624261921 34409310930469367718196441)
      ·
        refine ⟨25806983197852025788647331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34409310930469367718196441 25806983197852025788647331)
        ·
          refine ⟨38710474796778038682970997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25806983197852025788647331 38710474796778038682970997)
          ·
            refine ⟨3629107012197941126528531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38710474796778038682970997 3629107012197941126528531)
            ·
              refine ⟨5443660518296911689792797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629107012197941126528531 5443660518296911689792797)
              ·
                refine ⟨2041372694361341883672299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5443660518296911689792797 2041372694361341883672299)
                ·
                  refine ⟨3062059041542012825508449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041372694361341883672299 3062059041542012825508449)
                  ·
                    refine ⟨2296544281156509619131337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3062059041542012825508449 2296544281156509619131337)
                    ·
                      refine ⟨1722408210867382214348503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296544281156509619131337 1722408210867382214348503)
                      ·
                        rfl

theorem cell23_3354378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_3354378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354378 prefixEnd_3354378 := by exact prefixLift 3354378
  have htrace : WordTrace (prefixWord ++ tailWord_3354378) baseStart_3354378 baseEnd_3354378 := by
    simpa [prefixWord, tailWord_3354378, baseEnd_3354378] using wordTrace_append hprefix tailTrace_3354378
  have hstable : (prefixWord ++ tailWord_3354378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354378).length < 2 ^ (prefixWord ++ tailWord_3354378).sum := by decide
  have hdescent : baseEnd_3354378 < baseStart_3354378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354400 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3354400 : Nat := 118140960795 + 3354400 * 2 ^ 59
def prefixEnd_3354400 : Nat := 4983230072969 + 3 ^ 40 * 3354400 * 2
def baseEnd_3354400 : Nat := 1722419507441781128273401

theorem tailTrace_3354400 : CollatzResearch.WordTrace tailWord_3354400 prefixEnd_3354400 1722419507441781128273401 := by
  unfold tailWord_3354400
  simp only [CollatzResearch.WordTrace]
  refine ⟨61172509523794580377666327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81563346031726107170221769 61172509523794580377666327)
  ·
    refine ⟨91758764285691870566499491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61172509523794580377666327 91758764285691870566499491)
    ·
      refine ⟨137638146428537805849749237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91758764285691870566499491 137638146428537805849749237)
      ·
        refine ⟨12903576227675419298413991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137638146428537805849749237 12903576227675419298413991)
        ·
          refine ⟨19355364341513128947620987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12903576227675419298413991 19355364341513128947620987)
          ·
            refine ⟨29033046512269693421431481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19355364341513128947620987 29033046512269693421431481)
            ·
              refine ⟨21774784884202270066073611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29033046512269693421431481 21774784884202270066073611)
              ·
                refine ⟨32662177326303405099110417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21774784884202270066073611 32662177326303405099110417)
                ·
                  refine ⟨24496632994727553824332813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32662177326303405099110417 24496632994727553824332813)
                  ·
                    refine ⟨9186237373022832684124805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24496632994727553824332813 9186237373022832684124805)
                    ·
                      refine ⟨1722419507441781128273401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9186237373022832684124805 1722419507441781128273401)
                      ·
                        rfl

theorem cell23_3354400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3354400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354400 prefixEnd_3354400 := by exact prefixLift 3354400
  have htrace : WordTrace (prefixWord ++ tailWord_3354400) baseStart_3354400 baseEnd_3354400 := by
    simpa [prefixWord, tailWord_3354400, baseEnd_3354400] using wordTrace_append hprefix tailTrace_3354400
  have hstable : (prefixWord ++ tailWord_3354400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354400).length < 2 ^ (prefixWord ++ tailWord_3354400).sum := by decide
  have hdescent : baseEnd_3354400 < baseStart_3354400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354457 : List Nat := [1, 2, 1, 2, 2, 3, 3, 4, 5]
def baseStart_3354457 : Nat := 118140960795 + 3354457 * 2 ^ 59
def prefixEnd_3354457 : Nat := 4983230072969 + 3 ^ 40 * 3354457 * 2
def baseEnd_3354457 : Nat := 191383197315454156140071

theorem tailTrace_3354457 : CollatzResearch.WordTrace tailWord_3354457 prefixEnd_3354457 191383197315454156140071 := by
  unfold tailWord_3354457
  simp only [CollatzResearch.WordTrace]
  refine ⟨122347098008382659490157625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81564732005588439660105083 122347098008382659490157625)
  ·
    refine ⟨91760323506286994617618219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122347098008382659490157625 91760323506286994617618219)
    ·
      refine ⟨137640485259430491926427329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91760323506286994617618219 137640485259430491926427329)
      ·
        refine ⟨103230363944572868944820497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137640485259430491926427329 103230363944572868944820497)
        ·
          refine ⟨77422772958429651708615373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103230363944572868944820497 77422772958429651708615373)
          ·
            refine ⟨29033539859411119390730765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77422772958429651708615373 29033539859411119390730765)
            ·
              refine ⟨10887577447279169771524037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29033539859411119390730765 10887577447279169771524037)
              ·
                refine ⟨2041420771364844332160757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10887577447279169771524037 2041420771364844332160757)
                ·
                  refine ⟨191383197315454156140071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2041420771364844332160757 191383197315454156140071)
                  ·
                    rfl

theorem cell23_3354457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 5].length) (baseStart_3354457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354457 prefixEnd_3354457 := by exact prefixLift 3354457
  have htrace : WordTrace (prefixWord ++ tailWord_3354457) baseStart_3354457 baseEnd_3354457 := by
    simpa [prefixWord, tailWord_3354457, baseEnd_3354457] using wordTrace_append hprefix tailTrace_3354457
  have hstable : (prefixWord ++ tailWord_3354457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354457).length < 2 ^ (prefixWord ++ tailWord_3354457).sum := by decide
  have hdescent : baseEnd_3354457 < baseStart_3354457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354474 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 7]
def baseStart_3354474 : Nat := 118140960795 + 3354474 * 2 ^ 59
def prefixEnd_3354474 : Nat := 4983230072969 + 3 ^ 40 * 3354474 * 2
def baseEnd_3354474 : Nat := 191384167223357093194229

theorem tailTrace_3354474 : CollatzResearch.WordTrace tailWord_3354474 prefixEnd_3354474 191384167223357093194229 := by
  unfold tailWord_3354474
  simp only [CollatzResearch.WordTrace]
  refine ⟨30586929512330267848381619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81565145366214047595684317 30586929512330267848381619)
  ·
    refine ⟨45880394268495401772572429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30586929512330267848381619 45880394268495401772572429)
    ·
      refine ⟨17205147850685775664714661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45880394268495401772572429 17205147850685775664714661)
      ·
        refine ⟨3225965222003582937133999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17205147850685775664714661 3225965222003582937133999)
        ·
          refine ⟨4838947833005374405700999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225965222003582937133999 4838947833005374405700999)
          ·
            refine ⟨7258421749508061608551499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838947833005374405700999 7258421749508061608551499)
            ·
              refine ⟨10887632624262092412827249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7258421749508061608551499 10887632624262092412827249)
              ·
                refine ⟨8165724468196569309620437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10887632624262092412827249 8165724468196569309620437)
                ·
                  refine ⟨191384167223357093194229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8165724468196569309620437 191384167223357093194229)
                  ·
                    rfl

theorem cell23_3354474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 7].length) (baseStart_3354474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354474 prefixEnd_3354474 := by exact prefixLift 3354474
  have htrace : WordTrace (prefixWord ++ tailWord_3354474) baseStart_3354474 baseEnd_3354474 := by
    simpa [prefixWord, tailWord_3354474, baseEnd_3354474] using wordTrace_append hprefix tailTrace_3354474
  have hstable : (prefixWord ++ tailWord_3354474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354474).length < 2 ^ (prefixWord ++ tailWord_3354474).sum := by decide
  have hdescent : baseEnd_3354474 < baseStart_3354474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354542 : List Nat := [4, 1, 5, 1, 2, 1, 1, 3, 5]
def baseStart_3354542 : Nat := 118140960795 + 3354542 * 2 ^ 59
def prefixEnd_3354542 : Nat := 4983230072969 + 3 ^ 40 * 3354542 * 2
def baseEnd_3354542 : Nat := 191388046854968841410861

theorem tailTrace_3354542 : CollatzResearch.WordTrace tailWord_3354542 prefixEnd_3354542 191388046854968841410861 := by
  unfold tailWord_3354542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15293774776634339875875235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81566798808716479338001253 15293774776634339875875235)
  ·
    refine ⟨22940662164951509813812853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15293774776634339875875235 22940662164951509813812853)
    ·
      refine ⟨2150687077964204045044955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22940662164951509813812853 2150687077964204045044955)
      ·
        refine ⟨3226030616946306067567433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150687077964204045044955 3226030616946306067567433)
        ·
          refine ⟨2419522962709729550675575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3226030616946306067567433 2419522962709729550675575)
          ·
            refine ⟨3629284444064594326013363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419522962709729550675575 3629284444064594326013363)
            ·
              refine ⟨5443926666096891489020045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629284444064594326013363 5443926666096891489020045)
              ·
                refine ⟨2041472499786334308382517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5443926666096891489020045 2041472499786334308382517)
                ·
                  refine ⟨191388046854968841410861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2041472499786334308382517 191388046854968841410861)
                  ·
                    rfl

theorem cell23_3354542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_3354542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354542 prefixEnd_3354542 := by exact prefixLift 3354542
  have htrace : WordTrace (prefixWord ++ tailWord_3354542) baseStart_3354542 baseEnd_3354542 := by
    simpa [prefixWord, tailWord_3354542, baseEnd_3354542] using wordTrace_append hprefix tailTrace_3354542
  have hstable : (prefixWord ++ tailWord_3354542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354542).length < 2 ^ (prefixWord ++ tailWord_3354542).sum := by decide
  have hdescent : baseEnd_3354542 < baseStart_3354542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354568 : List Nat := [2, 1, 3, 1, 4, 2, 3, 2, 1, 4]
def baseStart_3354568 : Nat := 118140960795 + 3354568 * 2 ^ 59
def prefixEnd_3354568 : Nat := 4983230072969 + 3 ^ 40 * 3354568 * 2
def baseEnd_3354568 : Nat := 574168590730578823657543

theorem tailTrace_3354568 : CollatzResearch.WordTrace tailWord_3354568 prefixEnd_3354568 574168590730578823657543 := by
  unfold tailWord_3354568
  simp only [CollatzResearch.WordTrace]
  refine ⟨61175573255490262723724179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81567431007320350298298905 61175573255490262723724179)
  ·
    refine ⟨91763359883235394085586269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61175573255490262723724179 91763359883235394085586269)
    ·
      refine ⟨34411259956213272782094851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91763359883235394085586269 34411259956213272782094851)
      ·
        refine ⟨51616889934319909173142277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34411259956213272782094851 51616889934319909173142277)
        ·
          refine ⟨9678166862684982969964177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51616889934319909173142277 9678166862684982969964177)
          ·
            refine ⟨7258625147013737227473133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9678166862684982969964177 7258625147013737227473133)
            ·
              refine ⟨2721984430130151460302425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7258625147013737227473133 2721984430130151460302425)
              ·
                refine ⟨2041488322597613595226819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721984430130151460302425 2041488322597613595226819)
                ·
                  refine ⟨3062232483896420392840229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041488322597613595226819 3062232483896420392840229)
                  ·
                    refine ⟨574168590730578823657543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062232483896420392840229 574168590730578823657543)
                    ·
                      rfl

theorem cell23_3354568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_3354568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354568 prefixEnd_3354568 := by exact prefixLift 3354568
  have htrace : WordTrace (prefixWord ++ tailWord_3354568) baseStart_3354568 baseEnd_3354568 := by
    simpa [prefixWord, tailWord_3354568, baseEnd_3354568] using wordTrace_append hprefix tailTrace_3354568
  have hstable : (prefixWord ++ tailWord_3354568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354568).length < 2 ^ (prefixWord ++ tailWord_3354568).sum := by decide
  have hdescent : baseEnd_3354568 < baseStart_3354568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354581 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 6]
def baseStart_3354581 : Nat := 118140960795 + 3354581 * 2 ^ 59
def prefixEnd_3354581 : Nat := 4983230072969 + 3 ^ 40 * 3354581 * 2
def baseEnd_3354581 : Nat := 191390271937804991123341

theorem tailTrace_3354581 : CollatzResearch.WordTrace tailWord_3354581 prefixEnd_3354581 191390271937804991123341 := by
  unfold tailWord_3354581
  simp only [CollatzResearch.WordTrace]
  refine ⟨122351620659933428667671597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81567747106622285778447731 122351620659933428667671597)
  ·
    refine ⟨45881857747475035750376849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122351620659933428667671597 45881857747475035750376849)
    ·
      refine ⟨34411393310606276812782637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45881857747475035750376849 34411393310606276812782637)
      ·
        refine ⟨12904272491477353804793489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34411393310606276812782637 12904272491477353804793489)
        ·
          refine ⟨9678204368608015353595117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12904272491477353804793489 9678204368608015353595117)
          ·
            refine ⟨3629326638228005757598169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9678204368608015353595117 3629326638228005757598169)
            ·
              refine ⟨2721994978671004318198627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3629326638228005757598169 2721994978671004318198627)
              ·
                refine ⟨4082992468006506477297941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2721994978671004318198627 4082992468006506477297941)
                ·
                  refine ⟨191390271937804991123341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4082992468006506477297941 191390271937804991123341)
                  ·
                    rfl

theorem cell23_3354581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_3354581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354581 prefixEnd_3354581 := by exact prefixLift 3354581
  have htrace : WordTrace (prefixWord ++ tailWord_3354581) baseStart_3354581 baseEnd_3354581 := by
    simpa [prefixWord, tailWord_3354581, baseEnd_3354581] using wordTrace_append hprefix tailTrace_3354581
  have hstable : (prefixWord ++ tailWord_3354581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354581).length < 2 ^ (prefixWord ++ tailWord_3354581).sum := by decide
  have hdescent : baseEnd_3354581 < baseStart_3354581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354584 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_3354584 : Nat := 118140960795 + 3354584 * 2 ^ 59
def prefixEnd_3354584 : Nat := 4983230072969 + 3 ^ 40 * 3354584 * 2
def baseEnd_3354584 : Nat := 1722513987882208408372555

theorem tailTrace_3354584 : CollatzResearch.WordTrace tailWord_3354584 prefixEnd_3354584 1722513987882208408372555 := by
  unfold tailWord_3354584
  simp only [CollatzResearch.WordTrace]
  refine ⟨61175865039461280090015403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81567820052615040120020537 61175865039461280090015403)
  ·
    refine ⟨91763797559191920135023105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61175865039461280090015403 91763797559191920135023105)
    ·
      refine ⟨68822848169393940101267329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91763797559191920135023105 68822848169393940101267329)
      ·
        refine ⟨51617136127045455075950497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68822848169393940101267329 51617136127045455075950497)
        ·
          refine ⟨38712852095284091306962873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51617136127045455075950497 38712852095284091306962873)
          ·
            refine ⟨29034639071463068480222155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38712852095284091306962873 29034639071463068480222155)
            ·
              refine ⟨43551958607194602720333233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29034639071463068480222155 43551958607194602720333233)
              ·
                refine ⟨32663968955395952040249925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43551958607194602720333233 32663968955395952040249925)
                ·
                  refine ⟨6124494179136741007546861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32663968955395952040249925 6124494179136741007546861)
                  ·
                    refine ⟨2296685317176277877830073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6124494179136741007546861 2296685317176277877830073)
                    ·
                      refine ⟨1722513987882208408372555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296685317176277877830073 1722513987882208408372555)
                      ·
                        rfl

theorem cell23_3354584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_3354584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354584 prefixEnd_3354584 := by exact prefixLift 3354584
  have htrace : WordTrace (prefixWord ++ tailWord_3354584) baseStart_3354584 baseEnd_3354584 := by
    simpa [prefixWord, tailWord_3354584, baseEnd_3354584] using wordTrace_append hprefix tailTrace_3354584
  have hstable : (prefixWord ++ tailWord_3354584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354584).length < 2 ^ (prefixWord ++ tailWord_3354584).sum := by decide
  have hdescent : baseEnd_3354584 < baseStart_3354584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354607 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 1, 6]
def baseStart_3354607 : Nat := 118140960795 + 3354607 * 2 ^ 59
def prefixEnd_3354607 : Nat := 4983230072969 + 3 ^ 40 * 3354607 * 2
def baseEnd_3354607 : Nat := 574175265979087272794983

theorem tailTrace_3354607 : CollatzResearch.WordTrace tailWord_3354607 prefixEnd_3354607 574175265979087272794983 := by
  unfold tailWord_3354607
  simp only [CollatzResearch.WordTrace]
  refine ⟨122352568957839235108118075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81568379305226156738745383 122352568957839235108118075)
  ·
    refine ⟨183528853436758852662177113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122352568957839235108118075 183528853436758852662177113)
    ·
      refine ⟨137646640077569139496632835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183528853436758852662177113 137646640077569139496632835)
      ·
        refine ⟨206469960116353709244949253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137646640077569139496632835 206469960116353709244949253)
        ·
          refine ⟨38713117521816320483427985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206469960116353709244949253 38713117521816320483427985)
          ·
            refine ⟨29034838141362240362570989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38713117521816320483427985 29034838141362240362570989)
            ·
              refine ⟨10888064303010840135964121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29034838141362240362570989 10888064303010840135964121)
              ·
                refine ⟨8166048227258130101973091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10888064303010840135964121 8166048227258130101973091)
                ·
                  refine ⟨12249072340887195152959637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166048227258130101973091 12249072340887195152959637)
                  ·
                    refine ⟨574175265979087272794983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12249072340887195152959637 574175265979087272794983)
                    ·
                      rfl

theorem cell23_3354607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 1, 6].length) (baseStart_3354607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354607 prefixEnd_3354607 := by exact prefixLift 3354607
  have htrace : WordTrace (prefixWord ++ tailWord_3354607) baseStart_3354607 baseEnd_3354607 := by
    simpa [prefixWord, tailWord_3354607, baseEnd_3354607] using wordTrace_append hprefix tailTrace_3354607
  have hstable : (prefixWord ++ tailWord_3354607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354607).length < 2 ^ (prefixWord ++ tailWord_3354607).sum := by decide
  have hdescent : baseEnd_3354607 < baseStart_3354607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354687 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4]
def baseStart_3354687 : Nat := 118140960795 + 3354687 * 2 ^ 59
def prefixEnd_3354687 : Nat := 4983230072969 + 3 ^ 40 * 3354687 * 2
def baseEnd_3354687 : Nat := 1722566876389621505384581

theorem tailTrace_3354687 : CollatzResearch.WordTrace tailWord_3354687 prefixEnd_3354687 1722566876389621505384581 := by
  unfold tailWord_3354687
  simp only [CollatzResearch.WordTrace]
  refine ⟨122355486797549408771030315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81570324531699605847353543 122355486797549408771030315)
  ·
    refine ⟨183533230196324113156545473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122355486797549408771030315 183533230196324113156545473)
    ·
      refine ⟨137649922647243084867409105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183533230196324113156545473 137649922647243084867409105)
      ·
        refine ⟨103237441985432313650556829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137649922647243084867409105 103237441985432313650556829)
        ·
          refine ⟨38714040744537117618958811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103237441985432313650556829 38714040744537117618958811)
          ·
            refine ⟨58071061116805676428438217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38714040744537117618958811 58071061116805676428438217)
            ·
              refine ⟨43553295837604257321328663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58071061116805676428438217 43553295837604257321328663)
              ·
                refine ⟨65329943756406385981992995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43553295837604257321328663 65329943756406385981992995)
                ·
                  refine ⟨97994915634609578972989493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65329943756406385981992995 97994915634609578972989493)
                  ·
                    refine ⟨9187023340744648028717765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97994915634609578972989493 9187023340744648028717765)
                    ·
                      refine ⟨1722566876389621505384581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9187023340744648028717765 1722566876389621505384581)
                      ·
                        rfl

theorem cell23_3354687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 4].length) (baseStart_3354687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354687 prefixEnd_3354687 := by exact prefixLift 3354687
  have htrace : WordTrace (prefixWord ++ tailWord_3354687) baseStart_3354687 baseEnd_3354687 := by
    simpa [prefixWord, tailWord_3354687, baseEnd_3354687] using wordTrace_append hprefix tailTrace_3354687
  have hstable : (prefixWord ++ tailWord_3354687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354687).length < 2 ^ (prefixWord ++ tailWord_3354687).sum := by decide
  have hdescent : baseEnd_3354687 < baseStart_3354687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354697 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_3354697 : Nat := 118140960795 + 3354697 * 2 ^ 59
def prefixEnd_3354697 : Nat := 4983230072969 + 3 ^ 40 * 3354697 * 2
def baseEnd_3354697 : Nat := 574190670398722155419845

theorem tailTrace_3354697 : CollatzResearch.WordTrace tailWord_3354697 prefixEnd_3354697 574190670398722155419845 := by
  unfold tailWord_3354697
  simp only [CollatzResearch.WordTrace]
  refine ⟨122355851527513180478894345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81570567685008786985929563 122355851527513180478894345)
  ·
    refine ⟨91766888645634885359170759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122355851527513180478894345 91766888645634885359170759)
    ·
      refine ⟨137650332968452328038756139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91766888645634885359170759 137650332968452328038756139)
      ·
        refine ⟨206475499452678492058134209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137650332968452328038756139 206475499452678492058134209)
        ·
          refine ⟨154856624589508869043600657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206475499452678492058134209 154856624589508869043600657)
          ·
            refine ⟨116142468442131651782700493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154856624589508869043600657 116142468442131651782700493)
            ·
              refine ⟨43553425665799369418512685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116142468442131651782700493 43553425665799369418512685)
              ·
                refine ⟨16332534624674763531942257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43553425665799369418512685 16332534624674763531942257)
                ·
                  refine ⟨12249400968506072648956693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16332534624674763531942257 12249400968506072648956693)
                  ·
                    refine ⟨574190670398722155419845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12249400968506072648956693 574190670398722155419845)
                    ·
                      rfl

theorem cell23_3354697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_3354697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354697 prefixEnd_3354697 := by exact prefixLift 3354697
  have htrace : WordTrace (prefixWord ++ tailWord_3354697) baseStart_3354697 baseEnd_3354697 := by
    simpa [prefixWord, tailWord_3354697, baseEnd_3354697] using wordTrace_append hprefix tailTrace_3354697
  have hstable : (prefixWord ++ tailWord_3354697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354697).length < 2 ^ (prefixWord ++ tailWord_3354697).sum := by decide
  have hdescent : baseEnd_3354697 < baseStart_3354697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354737 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3354737 : Nat := 118140960795 + 3354737 * 2 ^ 59
def prefixEnd_3354737 : Nat := 4983230072969 + 3 ^ 40 * 3354737 * 2
def baseEnd_3354737 : Nat := 1722592550422346309759351

theorem tailTrace_3354737 : CollatzResearch.WordTrace tailWord_3354737 prefixEnd_3354737 1722592550422346309759351 := by
  unfold tailWord_3354737
  simp only [CollatzResearch.WordTrace]
  refine ⟨122357310447368267310350465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81571540298245511540233643 122357310447368267310350465)
  ·
    refine ⟨91767982835526200482762849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122357310447368267310350465 91767982835526200482762849)
    ·
      refine ⟨68825987126644650362072137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91767982835526200482762849 68825987126644650362072137)
      ·
        refine ⟨51619490344983487771554103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68825987126644650362072137 51619490344983487771554103)
        ·
          refine ⟨77429235517475231657331155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51619490344983487771554103 77429235517475231657331155)
          ·
            refine ⟨116143853276212847485996733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77429235517475231657331155 116143853276212847485996733)
            ·
              refine ⟨43553944978579817807248775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116143853276212847485996733 43553944978579817807248775)
              ·
                refine ⟨65330917467869726710873163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43553944978579817807248775 65330917467869726710873163)
                ·
                  refine ⟨97996376201804590066309745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65330917467869726710873163 97996376201804590066309745)
                  ·
                    refine ⟨73497282151353442549732309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97996376201804590066309745 73497282151353442549732309)
                    ·
                      refine ⟨1722592550422346309759351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73497282151353442549732309 1722592550422346309759351)
                      ·
                        rfl

theorem cell23_3354737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3354737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354737 prefixEnd_3354737 := by exact prefixLift 3354737
  have htrace : WordTrace (prefixWord ++ tailWord_3354737) baseStart_3354737 baseEnd_3354737 := by
    simpa [prefixWord, tailWord_3354737, baseEnd_3354737] using wordTrace_append hprefix tailTrace_3354737
  have hstable : (prefixWord ++ tailWord_3354737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354737).length < 2 ^ (prefixWord ++ tailWord_3354737).sum := by decide
  have hdescent : baseEnd_3354737 < baseStart_3354737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354738 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 4, 2, 2]
def baseStart_3354738 : Nat := 118140960795 + 3354738 * 2 ^ 59
def prefixEnd_3354738 : Nat := 4983230072969 + 3 ^ 40 * 3354738 * 2
def baseEnd_3354738 : Nat := 1722593063903000805846847

theorem tailTrace_3354738 : CollatzResearch.WordTrace tailWord_3354738 prefixEnd_3354738 1722593063903000805846847 := by
  unfold tailWord_3354738
  simp only [CollatzResearch.WordTrace]
  refine ⟨30589336730091161120284217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81571564613576429654091245 30589336730091161120284217)
  ·
    refine ⟨22942002547568370840213163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30589336730091161120284217 22942002547568370840213163)
    ·
      refine ⟨34413003821352556260319745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22942002547568370840213163 34413003821352556260319745)
      ·
        refine ⟨25809752866014417195239809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34413003821352556260319745 25809752866014417195239809)
        ·
          refine ⟨19357314649510812896429857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25809752866014417195239809 19357314649510812896429857)
          ·
            refine ⟨14517985987133109672322393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19357314649510812896429857 14517985987133109672322393)
            ·
              refine ⟨10888489490349832254241795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14517985987133109672322393 10888489490349832254241795)
              ·
                refine ⟨16332734235524748381362693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10888489490349832254241795 16332734235524748381362693)
                ·
                  refine ⟨3062387669160890321505505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16332734235524748381362693 3062387669160890321505505)
                  ·
                    refine ⟨2296790751870667741129129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3062387669160890321505505 2296790751870667741129129)
                    ·
                      refine ⟨1722593063903000805846847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296790751870667741129129 1722593063903000805846847)
                      ·
                        rfl

theorem cell23_3354738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_3354738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354738 prefixEnd_3354738 := by exact prefixLift 3354738
  have htrace : WordTrace (prefixWord ++ tailWord_3354738) baseStart_3354738 baseEnd_3354738 := by
    simpa [prefixWord, tailWord_3354738, baseEnd_3354738] using wordTrace_append hprefix tailTrace_3354738
  have hstable : (prefixWord ++ tailWord_3354738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354738).length < 2 ^ (prefixWord ++ tailWord_3354738).sum := by decide
  have hdescent : baseEnd_3354738 < baseStart_3354738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354755 : List Nat := [1, 1, 1, 3, 3, 3, 4, 1, 2, 2, 2]
def baseStart_3354755 : Nat := 118140960795 + 3354755 * 2 ^ 59
def prefixEnd_3354755 : Nat := 4983230072969 + 3 ^ 40 * 3354755 * 2
def baseEnd_3354755 : Nat := 1722601793074127239334269

theorem tailTrace_3354755 : CollatzResearch.WordTrace tailWord_3354755 prefixEnd_3354755 1722601793074127239334269 := by
  unfold tailWord_3354755
  simp only [CollatzResearch.WordTrace]
  refine ⟨122357966961303056384505719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81571977974202037589670479 122357966961303056384505719)
  ·
    refine ⟨183536950441954584576758579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122357966961303056384505719 183536950441954584576758579)
    ·
      refine ⟨275305425662931876865137869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183536950441954584576758579 275305425662931876865137869)
      ·
        refine ⟨103239534623599453824426701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275305425662931876865137869 103239534623599453824426701)
        ·
          refine ⟨38714825483849795184160013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103239534623599453824426701 38714825483849795184160013)
          ·
            refine ⟨14518059556443673194060005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38714825483849795184160013 14518059556443673194060005)
            ·
              refine ⟨2722136166833188723886251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14518059556443673194060005 2722136166833188723886251)
              ·
                refine ⟨4083204250249783085829377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722136166833188723886251 4083204250249783085829377)
                ·
                  refine ⟨3062403187687337314372033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083204250249783085829377 3062403187687337314372033)
                  ·
                    refine ⟨2296802390765502985779025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3062403187687337314372033 2296802390765502985779025)
                    ·
                      refine ⟨1722601793074127239334269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296802390765502985779025 1722601793074127239334269)
                      ·
                        rfl

theorem cell23_3354755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 1, 2, 2, 2].length) (baseStart_3354755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354755 prefixEnd_3354755 := by exact prefixLift 3354755
  have htrace : WordTrace (prefixWord ++ tailWord_3354755) baseStart_3354755 baseEnd_3354755 := by
    simpa [prefixWord, tailWord_3354755, baseEnd_3354755] using wordTrace_append hprefix tailTrace_3354755
  have hstable : (prefixWord ++ tailWord_3354755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354755).length < 2 ^ (prefixWord ++ tailWord_3354755).sum := by decide
  have hdescent : baseEnd_3354755 < baseStart_3354755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354784 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3354784 : Nat := 118140960795 + 3354784 * 2 ^ 59
def prefixEnd_3354784 : Nat := 4983230072969 + 3 ^ 40 * 3354784 * 2
def baseEnd_3354784 : Nat := 1722616684013107625871635

theorem tailTrace_3354784 : CollatzResearch.WordTrace tailWord_3354784 prefixEnd_3354784 1722616684013107625871635 := by
  unfold tailWord_3354784
  simp only [CollatzResearch.WordTrace]
  refine ⟨61179512339098997168655703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81572683118798662891540937 61179512339098997168655703)
  ·
    refine ⟨91769268508648495752983555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61179512339098997168655703 91769268508648495752983555)
    ·
      refine ⟨137653902762972743629475333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91769268508648495752983555 137653902762972743629475333)
      ·
        refine ⟨25810106768057389430526625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137653902762972743629475333 25810106768057389430526625)
        ·
          refine ⟨19357580076043042072894969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25810106768057389430526625 19357580076043042072894969)
          ·
            refine ⟨14518185057032281554671227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19357580076043042072894969 14518185057032281554671227)
            ·
              refine ⟨21777277585548422332006841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14518185057032281554671227 21777277585548422332006841)
              ·
                refine ⟨16332958189161316749005131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21777277585548422332006841 16332958189161316749005131)
                ·
                  refine ⟨24499437283741975123507697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16332958189161316749005131 24499437283741975123507697)
                  ·
                    refine ⟨18374577962806481342630773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24499437283741975123507697 18374577962806481342630773)
                    ·
                      refine ⟨1722616684013107625871635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18374577962806481342630773 1722616684013107625871635)
                      ·
                        rfl

theorem cell23_3354784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3354784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354784 prefixEnd_3354784 := by exact prefixLift 3354784
  have htrace : WordTrace (prefixWord ++ tailWord_3354784) baseStart_3354784 baseEnd_3354784 := by
    simpa [prefixWord, tailWord_3354784, baseEnd_3354784] using wordTrace_append hprefix tailTrace_3354784
  have hstable : (prefixWord ++ tailWord_3354784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354784).length < 2 ^ (prefixWord ++ tailWord_3354784).sum := by decide
  have hdescent : baseEnd_3354784 < baseStart_3354784 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354811 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 2, 4, 2]
def baseStart_3354811 : Nat := 118140960795 + 3354811 * 2 ^ 59
def prefixEnd_3354811 : Nat := 4983230072969 + 3 ^ 40 * 3354811 * 2
def baseEnd_3354811 : Nat := 1722630547990779020234011

theorem tailTrace_3354811 : CollatzResearch.WordTrace tailWord_3354811 prefixEnd_3354811 1722630547990779020234011 := by
  unfold tailWord_3354811
  simp only [CollatzResearch.WordTrace]
  refine ⟨122360009449100177948544287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81573339632733451965696191 122360009449100177948544287)
  ·
    refine ⟨183540014173650266922816431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122360009449100177948544287 183540014173650266922816431)
    ·
      refine ⟨275310021260475400384224647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183540014173650266922816431 275310021260475400384224647)
      ·
        refine ⟨412965031890713100576336971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275310021260475400384224647 412965031890713100576336971)
        ·
          refine ⟨619447547836069650864505457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412965031890713100576336971 619447547836069650864505457)
          ·
            refine ⟨464585660877052238148379093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619447547836069650864505457 464585660877052238148379093)
            ·
              refine ⟨10888726426805911831602635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 464585660877052238148379093 10888726426805911831602635)
              ·
                refine ⟨16333089640208867747403953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10888726426805911831602635 16333089640208867747403953)
                ·
                  refine ⟨12249817230156650810552965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16333089640208867747403953 12249817230156650810552965)
                  ·
                    refine ⟨2296840730654372026978681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12249817230156650810552965 2296840730654372026978681)
                    ·
                      refine ⟨1722630547990779020234011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296840730654372026978681 1722630547990779020234011)
                      ·
                        rfl

theorem cell23_3354811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 4, 2].length) (baseStart_3354811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354811 prefixEnd_3354811 := by exact prefixLift 3354811
  have htrace : WordTrace (prefixWord ++ tailWord_3354811) baseStart_3354811 baseEnd_3354811 := by
    simpa [prefixWord, tailWord_3354811, baseEnd_3354811] using wordTrace_append hprefix tailTrace_3354811
  have hstable : (prefixWord ++ tailWord_3354811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354811).length < 2 ^ (prefixWord ++ tailWord_3354811).sum := by decide
  have hdescent : baseEnd_3354811 < baseStart_3354811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354828 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 1, 3, 4]
def baseStart_3354828 : Nat := 118140960795 + 3354828 * 2 ^ 59
def prefixEnd_3354828 : Nat := 4983230072969 + 3 ^ 40 * 3354828 * 2
def baseEnd_3354828 : Nat := 1722639277161905453721433

theorem tailTrace_3354828 : CollatzResearch.WordTrace tailWord_3354828 prefixEnd_3354828 1722639277161905453721433 := by
  unfold tailWord_3354828
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180314745019294925956569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81573752993359059901275425 61180314745019294925956569)
  ·
    refine ⟨45885236058764471194467427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61180314745019294925956569 45885236058764471194467427)
    ·
      refine ⟨68827854088146706791701141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45885236058764471194467427 68827854088146706791701141)
      ·
        refine ⟨3226305660381876880860991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68827854088146706791701141 3226305660381876880860991)
        ·
          refine ⟨4839458490572815321291487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226305660381876880860991 4839458490572815321291487)
          ·
            refine ⟨7259187735859222981937231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4839458490572815321291487 7259187735859222981937231)
            ·
              refine ⟨10888781603788834472905847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259187735859222981937231 10888781603788834472905847)
              ·
                refine ⟨16333172405683251709358771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10888781603788834472905847 16333172405683251709358771)
                ·
                  refine ⟨24499758608524877564038157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16333172405683251709358771 24499758608524877564038157)
                  ·
                    refine ⟨9187409478196829086514309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24499758608524877564038157 9187409478196829086514309)
                    ·
                      refine ⟨1722639277161905453721433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9187409478196829086514309 1722639277161905453721433)
                      ·
                        rfl

theorem cell23_3354828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_3354828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354828 prefixEnd_3354828 := by exact prefixLift 3354828
  have htrace : WordTrace (prefixWord ++ tailWord_3354828) baseStart_3354828 baseEnd_3354828 := by
    simpa [prefixWord, tailWord_3354828, baseEnd_3354828] using wordTrace_append hprefix tailTrace_3354828
  have hstable : (prefixWord ++ tailWord_3354828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354828).length < 2 ^ (prefixWord ++ tailWord_3354828).sum := by decide
  have hdescent : baseEnd_3354828 < baseStart_3354828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354855 : List Nat := [1, 1, 5, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3354855 : Nat := 118140960795 + 3354855 * 2 ^ 59
def prefixEnd_3354855 : Nat := 4983230072969 + 3 ^ 40 * 3354855 * 2
def baseEnd_3354855 : Nat := 574217713713192282694603

theorem tailTrace_3354855 : CollatzResearch.WordTrace tailWord_3354855 prefixEnd_3354855 574217713713192282694603 := by
  unfold tailWord_3354855
  simp only [CollatzResearch.WordTrace]
  refine ⟨122361614260940773463146019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81574409507293848975430679 122361614260940773463146019)
  ·
    refine ⟨183542421391411160194719029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122361614260940773463146019 183542421391411160194719029)
    ·
      refine ⟨17207102005444796268254909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183542421391411160194719029 17207102005444796268254909)
      ·
        refine ⟨6452663252041798600595591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17207102005444796268254909 6452663252041798600595591)
        ·
          refine ⟨9678994878062697900893387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452663252041798600595591 9678994878062697900893387)
          ·
            refine ⟨14518492317094046851340081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9678994878062697900893387 14518492317094046851340081)
            ·
              refine ⟨10888869237820535138505061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14518492317094046851340081 10888869237820535138505061)
              ·
                refine ⟨2041662982091350338469699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10888869237820535138505061 2041662982091350338469699)
                ·
                  refine ⟨3062494473137025507704549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2041662982091350338469699 3062494473137025507704549)
                  ·
                    refine ⟨574217713713192282694603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062494473137025507704549 574217713713192282694603)
                    ·
                      rfl

theorem cell23_3354855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3354855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354855 prefixEnd_3354855 := by exact prefixLift 3354855
  have htrace : WordTrace (prefixWord ++ tailWord_3354855) baseStart_3354855 baseEnd_3354855 := by
    simpa [prefixWord, tailWord_3354855, baseEnd_3354855] using wordTrace_append hprefix tailTrace_3354855
  have hstable : (prefixWord ++ tailWord_3354855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354855).length < 2 ^ (prefixWord ++ tailWord_3354855).sum := by decide
  have hdescent : baseEnd_3354855 < baseStart_3354855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354864 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_3354864 : Nat := 118140960795 + 3354864 * 2 ^ 59
def prefixEnd_3354864 : Nat := 4983230072969 + 3 ^ 40 * 3354864 * 2
def baseEnd_3354864 : Nat := 574219254155155770957089

theorem tailTrace_3354864 : CollatzResearch.WordTrace tailWord_3354864 prefixEnd_3354864 574219254155155770957089 := by
  unfold tailWord_3354864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61180971258954084000111823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81574628345272112000149097 61180971258954084000111823)
  ·
    refine ⟨91771456888431126000167735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61180971258954084000111823 91771456888431126000167735)
    ·
      refine ⟨137657185332646689000251603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91771456888431126000167735 137657185332646689000251603)
      ·
        refine ⟨206485777998970033500377405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137657185332646689000251603 206485777998970033500377405)
        ·
          refine ⟨77432166749613762562641527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206485777998970033500377405 77432166749613762562641527)
          ·
            refine ⟨116148250124420643843962291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77432166749613762562641527 116148250124420643843962291)
            ·
              refine ⟨174222375186630965765943437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116148250124420643843962291 174222375186630965765943437)
              ·
                refine ⟨65333390694986612162228789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174222375186630965765943437 65333390694986612162228789)
                ·
                  refine ⟨6125005377654994890208949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65333390694986612162228789 6125005377654994890208949)
                  ·
                    refine ⟨574219254155155770957089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6125005377654994890208949 574219254155155770957089)
                    ·
                      rfl

theorem cell23_3354864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_3354864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354864 prefixEnd_3354864 := by exact prefixLift 3354864
  have htrace : WordTrace (prefixWord ++ tailWord_3354864) baseStart_3354864 baseEnd_3354864 := by
    simpa [prefixWord, tailWord_3354864, baseEnd_3354864] using wordTrace_append hprefix tailTrace_3354864
  have hstable : (prefixWord ++ tailWord_3354864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354864).length < 2 ^ (prefixWord ++ tailWord_3354864).sum := by decide
  have hdescent : baseEnd_3354864 < baseStart_3354864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354888 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_3354888 : Nat := 118140960795 + 3354888 * 2 ^ 59
def prefixEnd_3354888 : Nat := 4983230072969 + 3 ^ 40 * 3354888 * 2
def baseEnd_3354888 : Nat := 1722670086001175218971157

theorem tailTrace_3354888 : CollatzResearch.WordTrace tailWord_3354888 prefixEnd_3354888 1722670086001175218971157 := by
  unfold tailWord_3354888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61181408934910610049548659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81575211913214146732731545 61181408934910610049548659)
  ·
    refine ⟨91772113402365915074322989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61181408934910610049548659 91772113402365915074322989)
    ·
      refine ⟨34414542525887218152871121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91772113402365915074322989 34414542525887218152871121)
      ·
        refine ⟨25810906894415413614653341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34414542525887218152871121 25810906894415413614653341)
        ·
          refine ⟨9679090085405780105495003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25810906894415413614653341 9679090085405780105495003)
          ·
            refine ⟨14518635128108670158242505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679090085405780105495003 14518635128108670158242505)
            ·
              refine ⟨10888976346081502618681879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14518635128108670158242505 10888976346081502618681879)
              ·
                refine ⟨16333464519122253928022819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10888976346081502618681879 16333464519122253928022819)
                ·
                  refine ⟨24500196778683380892034229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16333464519122253928022819 24500196778683380892034229)
                  ·
                    refine ⟨2296893448001566958628209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24500196778683380892034229 2296893448001566958628209)
                    ·
                      refine ⟨1722670086001175218971157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2296893448001566958628209 1722670086001175218971157)
                      ·
                        rfl

theorem cell23_3354888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_3354888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354888 prefixEnd_3354888 := by exact prefixLift 3354888
  have htrace : WordTrace (prefixWord ++ tailWord_3354888) baseStart_3354888 baseEnd_3354888 := by
    simpa [prefixWord, tailWord_3354888, baseEnd_3354888] using wordTrace_append hprefix tailTrace_3354888
  have hstable : (prefixWord ++ tailWord_3354888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354888).length < 2 ^ (prefixWord ++ tailWord_3354888).sum := by decide
  have hdescent : baseEnd_3354888 < baseStart_3354888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354919 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 6]
def baseStart_3354919 : Nat := 118140960795 + 3354919 * 2 ^ 59
def prefixEnd_3354919 : Nat := 4983230072969 + 3 ^ 40 * 3354919 * 2
def baseEnd_3354919 : Nat := 191409555989051621964835

theorem tailTrace_3354919 : CollatzResearch.WordTrace tailWord_3354919 prefixEnd_3354919 191409555989051621964835 := by
  unfold tailWord_3354919
  simp only [CollatzResearch.WordTrace]
  refine ⟨122363948532708912393475811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81575965688472608262317207 122363948532708912393475811)
  ·
    refine ⟨183545922799063368590213717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122363948532708912393475811 183545922799063368590213717)
    ·
      refine ⟨2150928782801523850666567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 183545922799063368590213717 2150928782801523850666567)
      ·
        refine ⟨3226393174202285775999851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150928782801523850666567 3226393174202285775999851)
        ·
          refine ⟨4839589761303428663999777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3226393174202285775999851 4839589761303428663999777)
          ·
            refine ⟨3629692320977571497999833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839589761303428663999777 3629692320977571497999833)
            ·
              refine ⟨2722269240733178623499875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3629692320977571497999833 2722269240733178623499875)
              ·
                refine ⟨4083403861099767935249813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722269240733178623499875 4083403861099767935249813)
                ·
                  refine ⟨191409555989051621964835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4083403861099767935249813 191409555989051621964835)
                  ·
                    rfl

theorem cell23_3354919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 6].length) (baseStart_3354919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354919 prefixEnd_3354919 := by exact prefixLift 3354919
  have htrace : WordTrace (prefixWord ++ tailWord_3354919) baseStart_3354919 baseEnd_3354919 := by
    simpa [prefixWord, tailWord_3354919, baseEnd_3354919] using wordTrace_append hprefix tailTrace_3354919
  have hstable : (prefixWord ++ tailWord_3354919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354919).length < 2 ^ (prefixWord ++ tailWord_3354919).sum := by decide
  have hdescent : baseEnd_3354919 < baseStart_3354919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354924 : List Nat := [2, 2, 1, 1, 1, 3, 3, 10]
def baseStart_3354924 : Nat := 118140960795 + 3354924 * 2 ^ 59
def prefixEnd_3354924 : Nat := 4983230072969 + 3 ^ 40 * 3354924 * 2
def baseEnd_3354924 : Nat := 63803280418693965856333

theorem tailTrace_3354924 : CollatzResearch.WordTrace tailWord_3354924 prefixEnd_3354924 63803280418693965856333 := by
  unfold tailWord_3354924
  simp only [CollatzResearch.WordTrace]
  refine ⟨61182065448845399123703913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81576087265127198831605217 61182065448845399123703913)
  ·
    refine ⟨45886549086634049342777935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61182065448845399123703913 45886549086634049342777935)
    ·
      refine ⟨68829823629951074014166903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45886549086634049342777935 68829823629951074014166903)
      ·
        refine ⟨103244735444926611021250355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68829823629951074014166903 103244735444926611021250355)
        ·
          refine ⟨154867103167389916531875533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103244735444926611021250355 154867103167389916531875533)
          ·
            refine ⟨58075163687771218699453325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154867103167389916531875533 58075163687771218699453325)
            ·
              refine ⟨21778186382914207012294997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58075163687771218699453325 21778186382914207012294997)
              ·
                refine ⟨63803280418693965856333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21778186382914207012294997 63803280418693965856333)
                ·
                  rfl

theorem cell23_3354924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 10].length) (baseStart_3354924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354924 prefixEnd_3354924 := by exact prefixLift 3354924
  have htrace : WordTrace (prefixWord ++ tailWord_3354924) baseStart_3354924 baseEnd_3354924 := by
    simpa [prefixWord, tailWord_3354924, baseEnd_3354924] using wordTrace_append hprefix tailTrace_3354924
  have hstable : (prefixWord ++ tailWord_3354924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354924).length < 2 ^ (prefixWord ++ tailWord_3354924).sum := by decide
  have hdescent : baseEnd_3354924 < baseStart_3354924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354931 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4]
def baseStart_3354931 : Nat := 118140960795 + 3354931 * 2 ^ 59
def prefixEnd_3354931 : Nat := 4983230072969 + 3 ^ 40 * 3354931 * 2
def baseEnd_3354931 : Nat := 1722692165669318550733459

theorem tailTrace_3354931 : CollatzResearch.WordTrace tailWord_3354931 prefixEnd_3354931 1722692165669318550733459 := by
  unfold tailWord_3354931
  simp only [CollatzResearch.WordTrace]
  refine ⟨122364386208665438442912647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81576257472443625628608431 122364386208665438442912647)
  ·
    refine ⟨183546579312998157664368971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122364386208665438442912647 183546579312998157664368971)
    ·
      refine ⟨275319868969497236496553457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183546579312998157664368971 275319868969497236496553457)
      ·
        refine ⟨206489901727122927372415093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275319868969497236496553457 206489901727122927372415093)
        ·
          refine ⟨19358428286917774441163915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206489901727122927372415093 19358428286917774441163915)
          ·
            refine ⟨29037642430376661661745873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19358428286917774441163915 29037642430376661661745873)
            ·
              refine ⟨21778231822782496246309405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29037642430376661661745873 21778231822782496246309405)
              ·
                refine ⟨8166836933543436092366027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21778231822782496246309405 8166836933543436092366027)
                ·
                  refine ⟨12250255400315154138549041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8166836933543436092366027 12250255400315154138549041)
                  ·
                    refine ⟨9187691550236365603911781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12250255400315154138549041 9187691550236365603911781)
                    ·
                      refine ⟨1722692165669318550733459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9187691550236365603911781 1722692165669318550733459)
                      ·
                        rfl

theorem cell23_3354931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 4].length) (baseStart_3354931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354931 prefixEnd_3354931 := by exact prefixLift 3354931
  have htrace : WordTrace (prefixWord ++ tailWord_3354931) baseStart_3354931 baseEnd_3354931 := by
    simpa [prefixWord, tailWord_3354931, baseEnd_3354931] using wordTrace_append hprefix tailTrace_3354931
  have hstable : (prefixWord ++ tailWord_3354931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354931).length < 2 ^ (prefixWord ++ tailWord_3354931).sum := by decide
  have hdescent : baseEnd_3354931 < baseStart_3354931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3354938 : List Nat := [3, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3]
def baseStart_3354938 : Nat := 118140960795 + 3354938 * 2 ^ 59
def prefixEnd_3354938 : Nat := 4983230072969 + 3 ^ 40 * 3354938 * 2
def baseEnd_3354938 : Nat := 1722695760033900023345927

theorem tailTrace_3354938 : CollatzResearch.WordTrace tailWord_3354938 prefixEnd_3354938 1722695760033900023345927 := by
  unfold tailWord_3354938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30591160379910019659604367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81576427679760052425611645 30591160379910019659604367)
  ·
    refine ⟨45886740569865029489406551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30591160379910019659604367 45886740569865029489406551)
    ·
      refine ⟨68830110854797544234109827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45886740569865029489406551 68830110854797544234109827)
      ·
        refine ⟨103245166282196316351164741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68830110854797544234109827 103245166282196316351164741)
        ·
          refine ⟨19358468677911809315843389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103245166282196316351164741 19358468677911809315843389)
          ·
            refine ⟨7259425754216928493441271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19358468677911809315843389 7259425754216928493441271)
            ·
              refine ⟨10889138631325392740161907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259425754216928493441271 10889138631325392740161907)
              ·
                refine ⟨16333707946988089110242861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10889138631325392740161907 16333707946988089110242861)
                ·
                  refine ⟨6125140480120533416341073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16333707946988089110242861 6125140480120533416341073)
                  ·
                    refine ⟨4593855360090400062255805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6125140480120533416341073 4593855360090400062255805)
                    ·
                      refine ⟨1722695760033900023345927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4593855360090400062255805 1722695760033900023345927)
                      ·
                        rfl

theorem cell23_3354938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3].length) (baseStart_3354938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3354938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3354938 prefixEnd_3354938 := by exact prefixLift 3354938
  have htrace : WordTrace (prefixWord ++ tailWord_3354938) baseStart_3354938 baseEnd_3354938 := by
    simpa [prefixWord, tailWord_3354938, baseEnd_3354938] using wordTrace_append hprefix tailTrace_3354938
  have hstable : (prefixWord ++ tailWord_3354938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3354938).length < 2 ^ (prefixWord ++ tailWord_3354938).sum := by decide
  have hdescent : baseEnd_3354938 < baseStart_3354938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3354938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355031 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 7]
def baseStart_3355031 : Nat := 118140960795 + 3355031 * 2 ^ 59
def prefixEnd_3355031 : Nat := 4983230072969 + 3 ^ 40 * 3355031 * 2
def baseEnd_3355031 : Nat := 191415945970529795498111

theorem tailTrace_3355031 : CollatzResearch.WordTrace tailWord_3355031 prefixEnd_3355031 191415945970529795498111 := by
  unfold tailWord_3355031
  simp only [CollatzResearch.WordTrace]
  refine ⟨122368033508303155521552947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81578689005535437014368631 122368033508303155521552947)
  ·
    refine ⟨183552050262454733282329421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122368033508303155521552947 183552050262454733282329421)
    ·
      refine ⟨68832018848420524980873533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183552050262454733282329421 68832018848420524980873533)
      ·
        refine ⟨25812007068157696867827575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68832018848420524980873533 25812007068157696867827575)
        ·
          refine ⟨38718010602236545301741363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25812007068157696867827575 38718010602236545301741363)
          ·
            refine ⟨58077015903354817952612045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38718010602236545301741363 58077015903354817952612045)
            ·
              refine ⟨21778880963758056732229517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58077015903354817952612045 21778880963758056732229517)
              ·
                refine ⟨8167080361409271274586069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21778880963758056732229517 8167080361409271274586069)
                ·
                  refine ⟨191415945970529795498111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8167080361409271274586069 191415945970529795498111)
                  ·
                    rfl

theorem cell23_3355031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 7].length) (baseStart_3355031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355031 prefixEnd_3355031 := by exact prefixLift 3355031
  have htrace : WordTrace (prefixWord ++ tailWord_3355031) baseStart_3355031 baseEnd_3355031 := by
    simpa [prefixWord, tailWord_3355031, baseEnd_3355031] using wordTrace_append hprefix tailTrace_3355031
  have hstable : (prefixWord ++ tailWord_3355031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355031).length < 2 ^ (prefixWord ++ tailWord_3355031).sum := by decide
  have hdescent : baseEnd_3355031 < baseStart_3355031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355065 : List Nat := [1, 2, 1, 4, 3, 1, 3, 3, 5]
def baseStart_3355065 : Nat := 118140960795 + 3355065 * 2 ^ 59
def prefixEnd_3355065 : Nat := 4983230072969 + 3 ^ 40 * 3355065 * 2
def baseEnd_3355065 : Nat := 191417885786335669606427

theorem tailTrace_3355065 : CollatzResearch.WordTrace tailWord_3355065 prefixEnd_3355065 191417885786335669606427 := by
  unfold tailWord_3355065
  simp only [CollatzResearch.WordTrace]
  refine ⟨122369273590179979328290649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81579515726786652885527099 122369273590179979328290649)
  ·
    refine ⟨91776955192634984496217987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122369273590179979328290649 91776955192634984496217987)
    ·
      refine ⟨137665432788952476744326981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91776955192634984496217987 137665432788952476744326981)
      ·
        refine ⟨25812268647928589389561309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137665432788952476744326981 25812268647928589389561309)
        ·
          refine ⟨9679600742973221021085491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25812268647928589389561309 9679600742973221021085491)
          ·
            refine ⟨14519401114459831531628237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679600742973221021085491 14519401114459831531628237)
            ·
              refine ⟨5444775417922436824360589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14519401114459831531628237 5444775417922436824360589)
              ·
                refine ⟨2041790781720913809135221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5444775417922436824360589 2041790781720913809135221)
                ·
                  refine ⟨191417885786335669606427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2041790781720913809135221 191417885786335669606427)
                  ·
                    rfl

theorem cell23_3355065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 5].length) (baseStart_3355065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355065 prefixEnd_3355065 := by exact prefixLift 3355065
  have htrace : WordTrace (prefixWord ++ tailWord_3355065) baseStart_3355065 baseEnd_3355065 := by
    simpa [prefixWord, tailWord_3355065, baseEnd_3355065] using wordTrace_append hprefix tailTrace_3355065
  have hstable : (prefixWord ++ tailWord_3355065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355065).length < 2 ^ (prefixWord ++ tailWord_3355065).sum := by decide
  have hdescent : baseEnd_3355065 < baseStart_3355065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355098 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4]
def baseStart_3355098 : Nat := 118140960795 + 3355098 * 2 ^ 59
def prefixEnd_3355098 : Nat := 4983230072969 + 3 ^ 40 * 3355098 * 2
def baseEnd_3355098 : Nat := 1722777916938619397345191

theorem tailTrace_3355098 : CollatzResearch.WordTrace tailWord_3355098 prefixEnd_3355098 1722777916938619397345191 := by
  unfold tailWord_3355098
  simp only [CollatzResearch.WordTrace]
  refine ⟨30592619299765106491060487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81580318132706950642827965 30592619299765106491060487)
  ·
    refine ⟨45888928949647659736590731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30592619299765106491060487 45888928949647659736590731)
    ·
      refine ⟨68833393424471489604886097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45888928949647659736590731 68833393424471489604886097)
      ·
        refine ⟨51625045068353617203664573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68833393424471489604886097 51625045068353617203664573)
        ·
          refine ⟨19359391900632606451374215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51625045068353617203664573 19359391900632606451374215)
          ·
            refine ⟨29039087850948909677061323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19359391900632606451374215 29039087850948909677061323)
            ·
              refine ⟨43558631776423364515591985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29039087850948909677061323 43558631776423364515591985)
              ·
                refine ⟨32668973832317523386693989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43558631776423364515591985 32668973832317523386693989)
                ·
                  refine ⟨6125432593559535635005123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32668973832317523386693989 6125432593559535635005123)
                  ·
                    refine ⟨9188148890339303452507685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125432593559535635005123 9188148890339303452507685)
                    ·
                      refine ⟨1722777916938619397345191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9188148890339303452507685 1722777916938619397345191)
                      ·
                        rfl

theorem cell23_3355098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_3355098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355098 prefixEnd_3355098 := by exact prefixLift 3355098
  have htrace : WordTrace (prefixWord ++ tailWord_3355098) baseStart_3355098 baseEnd_3355098 := by
    simpa [prefixWord, tailWord_3355098, baseEnd_3355098] using wordTrace_append hprefix tailTrace_3355098
  have hstable : (prefixWord ++ tailWord_3355098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355098).length < 2 ^ (prefixWord ++ tailWord_3355098).sum := by decide
  have hdescent : baseEnd_3355098 < baseStart_3355098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355149 : List Nat := [1, 7, 1, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_3355149 : Nat := 118140960795 + 3355149 * 2 ^ 59
def prefixEnd_3355149 : Nat := 4983230072969 + 3 ^ 40 * 3355149 * 2
def baseEnd_3355149 : Nat := 1722804104451998697807457

theorem tailTrace_3355149 : CollatzResearch.WordTrace tailWord_3355149 prefixEnd_3355149 1722804104451998697807457 := by
  unfold tailWord_3355149
  simp only [CollatzResearch.WordTrace]
  refine ⟨122372337321875661674348501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81581558214583774449565667 122372337321875661674348501)
  ·
    refine ⟨2868101655981460820492543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 122372337321875661674348501 2868101655981460820492543)
    ·
      refine ⟨4302152483972191230738815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868101655981460820492543 4302152483972191230738815)
      ·
        refine ⟨6453228725958286846108223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302152483972191230738815 6453228725958286846108223)
        ·
          refine ⟨9679843088937430269162335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453228725958286846108223 9679843088937430269162335)
          ·
            refine ⟨14519764633406145403743503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9679843088937430269162335 14519764633406145403743503)
            ·
              refine ⟨21779646950109218105615255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14519764633406145403743503 21779646950109218105615255)
              ·
                refine ⟨32669470425163827158422883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21779646950109218105615255 32669470425163827158422883)
                ·
                  refine ⟨49004205637745740737634325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32669470425163827158422883 49004205637745740737634325)
                  ·
                    refine ⟨2297072139269331597076609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49004205637745740737634325 2297072139269331597076609)
                    ·
                      refine ⟨1722804104451998697807457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297072139269331597076609 1722804104451998697807457)
                      ·
                        rfl

theorem cell23_3355149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_3355149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355149 prefixEnd_3355149 := by exact prefixLift 3355149
  have htrace : WordTrace (prefixWord ++ tailWord_3355149) baseStart_3355149 baseEnd_3355149 := by
    simpa [prefixWord, tailWord_3355149, baseEnd_3355149] using wordTrace_append hprefix tailTrace_3355149
  have hstable : (prefixWord ++ tailWord_3355149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355149).length < 2 ^ (prefixWord ++ tailWord_3355149).sum := by decide
  have hdescent : baseEnd_3355149 < baseStart_3355149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355151 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 9]
def baseStart_3355151 : Nat := 118140960795 + 3355151 * 2 ^ 59
def prefixEnd_3355151 : Nat := 4983230072969 + 3 ^ 40 * 3355151 * 2
def baseEnd_3355151 : Nat := 574268377137769229994149

theorem tailTrace_3355151 : CollatzResearch.WordTrace tailWord_3355151 prefixEnd_3355151 574268377137769229994149 := by
  unfold tailWord_3355151
  simp only [CollatzResearch.WordTrace]
  refine ⟨122372410267868416015921307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81581606845245610677280871 122372410267868416015921307)
  ·
    refine ⟨183558615401802624023881961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122372410267868416015921307 183558615401802624023881961)
    ·
      refine ⟨137668961551351968017911471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183558615401802624023881961 137668961551351968017911471)
      ·
        refine ⟨206503442327027952026867207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137668961551351968017911471 206503442327027952026867207)
        ·
          refine ⟨309755163490541928040300811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206503442327027952026867207 309755163490541928040300811)
          ·
            refine ⟨464632745235812892060451217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309755163490541928040300811 464632745235812892060451217)
            ·
              refine ⟨348474558926859669045338413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464632745235812892060451217 348474558926859669045338413)
              ·
                refine ⟨130677959597572375892001905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 348474558926859669045338413 130677959597572375892001905)
                ·
                  refine ⟨98008469698179281919001429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130677959597572375892001905 98008469698179281919001429)
                  ·
                    refine ⟨574268377137769229994149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98008469698179281919001429 574268377137769229994149)
                    ·
                      rfl

theorem cell23_3355151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 9].length) (baseStart_3355151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355151 prefixEnd_3355151 := by exact prefixLift 3355151
  have htrace : WordTrace (prefixWord ++ tailWord_3355151) baseStart_3355151 baseEnd_3355151 := by
    simpa [prefixWord, tailWord_3355151, baseEnd_3355151] using wordTrace_append hprefix tailTrace_3355151
  have hstable : (prefixWord ++ tailWord_3355151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355151).length < 2 ^ (prefixWord ++ tailWord_3355151).sum := by decide
  have hdescent : baseEnd_3355151 < baseStart_3355151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355215 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 2, 4]
def baseStart_3355215 : Nat := 118140960795 + 3355215 * 2 ^ 59
def prefixEnd_3355215 : Nat := 4983230072969 + 3 ^ 40 * 3355215 * 2
def baseEnd_3355215 : Nat := 574279331391731813194051

theorem tailTrace_3355215 : CollatzResearch.WordTrace tailWord_3355215 prefixEnd_3355215 574279331391731813194051 := by
  unfold tailWord_3355215
  simp only [CollatzResearch.WordTrace]
  refine ⟨122374744539636554946251099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81583163026424369964167399 122374744539636554946251099)
  ·
    refine ⟨183562116809454832419376649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122374744539636554946251099 183562116809454832419376649)
    ·
      refine ⟨137671587607091124314532487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183562116809454832419376649 137671587607091124314532487)
      ·
        refine ⟨206507381410636686471798731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137671587607091124314532487 206507381410636686471798731)
        ·
          refine ⟨309761072115955029707698097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206507381410636686471798731 309761072115955029707698097)
          ·
            refine ⟨232320804086966272280773573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309761072115955029707698097 232320804086966272280773573)
            ·
              refine ⟨43560150766306176052645045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232320804086966272280773573 43560150766306176052645045)
              ·
                refine ⟨4083764134341204004935473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43560150766306176052645045 4083764134341204004935473)
                ·
                  refine ⟨3062823100755903003701605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083764134341204004935473 3062823100755903003701605)
                  ·
                    refine ⟨574279331391731813194051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3062823100755903003701605 574279331391731813194051)
                    ·
                      rfl

theorem cell23_3355215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 2, 4].length) (baseStart_3355215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355215 prefixEnd_3355215 := by exact prefixLift 3355215
  have htrace : WordTrace (prefixWord ++ tailWord_3355215) baseStart_3355215 baseEnd_3355215 := by
    simpa [prefixWord, tailWord_3355215, baseEnd_3355215] using wordTrace_append hprefix tailTrace_3355215
  have hstable : (prefixWord ++ tailWord_3355215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355215).length < 2 ^ (prefixWord ++ tailWord_3355215).sum := by decide
  have hdescent : baseEnd_3355215 < baseStart_3355215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355242 : List Nat := [3, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3355242 : Nat := 118140960795 + 3355242 * 2 ^ 59
def prefixEnd_3355242 : Nat := 4983230072969 + 3 ^ 40 * 3355242 * 2
def baseEnd_3355242 : Nat := 1722851858152866833944529

theorem tailTrace_3355242 : CollatzResearch.WordTrace tailWord_3355242 prefixEnd_3355242 1722851858152866833944529 := by
  unfold tailWord_3355242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30593932327634684639370995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81583819540359159038322653 30593932327634684639370995)
  ·
    refine ⟨45890898491452026959056493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30593932327634684639370995 45890898491452026959056493)
    ·
      refine ⟨17209086934294510109646185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45890898491452026959056493 17209086934294510109646185)
      ·
        refine ⟨12906815200720882582234639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17209086934294510109646185 12906815200720882582234639)
        ·
          refine ⟨19360222801081323873351959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12906815200720882582234639 19360222801081323873351959)
          ·
            refine ⟨29040334201621985810027939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19360222801081323873351959 29040334201621985810027939)
            ·
              refine ⟨43560501302432978715041909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29040334201621985810027939 43560501302432978715041909)
              ·
                refine ⟨4083796997103091754535179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43560501302432978715041909 4083796997103091754535179)
                ·
                  refine ⟨6125695495654637631802769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4083796997103091754535179 6125695495654637631802769)
                  ·
                    refine ⟨4594271621740978223852077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6125695495654637631802769 4594271621740978223852077)
                    ·
                      refine ⟨1722851858152866833944529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4594271621740978223852077 1722851858152866833944529)
                      ·
                        rfl

theorem cell23_3355242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3355242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355242 prefixEnd_3355242 := by exact prefixLift 3355242
  have htrace : WordTrace (prefixWord ++ tailWord_3355242) baseStart_3355242 baseEnd_3355242 := by
    simpa [prefixWord, tailWord_3355242, baseEnd_3355242] using wordTrace_append hprefix tailTrace_3355242
  have hstable : (prefixWord ++ tailWord_3355242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355242).length < 2 ^ (prefixWord ++ tailWord_3355242).sum := by decide
  have hdescent : baseEnd_3355242 < baseStart_3355242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355245 : List Nat := [1, 5, 1, 1, 3, 3, 9]
def baseStart_3355245 : Nat := 118140960795 + 3355245 * 2 ^ 59
def prefixEnd_3355245 : Nat := 4983230072969 + 3 ^ 40 * 3355245 * 2
def baseEnd_3355245 : Nat := 21269795044380621261815

theorem tailTrace_3355245 : CollatzResearch.WordTrace tailWord_3355245 prefixEnd_3355245 21269795044380621261815 := by
  unfold tailWord_3355245
  simp only [CollatzResearch.WordTrace]
  refine ⟨122375838729527870069843189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81583892486351913379895459 122375838729527870069843189)
  ·
    refine ⟨11472734880893237819047799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122375838729527870069843189 11472734880893237819047799)
    ·
      refine ⟨17209102321339856728571699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11472734880893237819047799 17209102321339856728571699)
      ·
        refine ⟨25813653482009785092857549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17209102321339856728571699 25813653482009785092857549)
        ·
          refine ⟨9680120055753669409821581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25813653482009785092857549 9680120055753669409821581)
          ·
            refine ⟨3630045020907626028683093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9680120055753669409821581 3630045020907626028683093)
            ·
              refine ⟨21269795044380621261815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3630045020907626028683093 21269795044380621261815)
              ·
                rfl

theorem cell23_3355245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 9].length) (baseStart_3355245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355245 prefixEnd_3355245 := by exact prefixLift 3355245
  have htrace : WordTrace (prefixWord ++ tailWord_3355245) baseStart_3355245 baseEnd_3355245 := by
    simpa [prefixWord, tailWord_3355245, baseEnd_3355245] using wordTrace_append hprefix tailTrace_3355245
  have hstable : (prefixWord ++ tailWord_3355245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355245).length < 2 ^ (prefixWord ++ tailWord_3355245).sum := by decide
  have hdescent : baseEnd_3355245 < baseStart_3355245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355315 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3]
def baseStart_3355315 : Nat := 118140960795 + 3355315 * 2 ^ 59
def prefixEnd_3355315 : Nat := 4983230072969 + 3 ^ 40 * 3355315 * 2
def baseEnd_3355315 : Nat := 1722889342240645048331693

theorem tailTrace_3355315 : CollatzResearch.WordTrace tailWord_3355315 prefixEnd_3355315 1722889342240645048331693 := by
  unfold tailWord_3355315
  simp only [CollatzResearch.WordTrace]
  refine ⟨122378391839274272024891399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81585594559516181349927599 122378391839274272024891399)
  ·
    refine ⟨183567587758911408037337099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122378391839274272024891399 183567587758911408037337099)
    ·
      refine ⟨275351381638367112056005649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183567587758911408037337099 275351381638367112056005649)
      ·
        refine ⟨206513536228775334042004237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275351381638367112056005649 206513536228775334042004237)
        ·
          refine ⟨77442576085790750265751589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206513536228775334042004237 77442576085790750265751589)
          ·
            refine ⟨14520483016085765674828423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77442576085790750265751589 14520483016085765674828423)
            ·
              refine ⟨21780724524128648512242635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520483016085765674828423 21780724524128648512242635)
              ·
                refine ⟨32671086786192972768363953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21780724524128648512242635 32671086786192972768363953)
                ·
                  refine ⟨24503315089644729576272965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32671086786192972768363953 24503315089644729576272965)
                  ·
                    refine ⟨4594371579308386795551181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24503315089644729576272965 4594371579308386795551181)
                    ·
                      refine ⟨1722889342240645048331693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4594371579308386795551181 1722889342240645048331693)
                      ·
                        rfl

theorem cell23_3355315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 3].length) (baseStart_3355315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355315 prefixEnd_3355315 := by exact prefixLift 3355315
  have htrace : WordTrace (prefixWord ++ tailWord_3355315) baseStart_3355315 baseEnd_3355315 := by
    simpa [prefixWord, tailWord_3355315, baseEnd_3355315] using wordTrace_append hprefix tailTrace_3355315
  have hstable : (prefixWord ++ tailWord_3355315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355315).length < 2 ^ (prefixWord ++ tailWord_3355315).sum := by decide
  have hdescent : baseEnd_3355315 < baseStart_3355315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355325 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_3355325 : Nat := 118140960795 + 3355325 * 2 ^ 59
def prefixEnd_3355325 : Nat := 4983230072969 + 3 ^ 40 * 3355325 * 2
def baseEnd_3355325 : Nat := 1722894477047190009206647

theorem tailTrace_3355325 : CollatzResearch.WordTrace tailWord_3355325 prefixEnd_3355325 1722894477047190009206647 := by
  unfold tailWord_3355325
  simp only [CollatzResearch.WordTrace]
  refine ⟨122378756569238043732755429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81585837712825362488503619 122378756569238043732755429)
  ·
    refine ⟨22946016856732133199891643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122378756569238043732755429 22946016856732133199891643)
    ·
      refine ⟨34419025285098199799837465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22946016856732133199891643 34419025285098199799837465)
      ·
        refine ⟨25814268963823649849878099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34419025285098199799837465 25814268963823649849878099)
        ·
          refine ⟨38721403445735474774817149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25814268963823649849878099 38721403445735474774817149)
          ·
            refine ⟨14520526292150803040556431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38721403445735474774817149 14520526292150803040556431)
            ·
              refine ⟨21780789438226204560834647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520526292150803040556431 21780789438226204560834647)
              ·
                refine ⟨32671184157339306841251971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21780789438226204560834647 32671184157339306841251971)
                ·
                  refine ⟨49006776236008960261877957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32671184157339306841251971 49006776236008960261877957)
                  ·
                    refine ⟨9188770544251680049102117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49006776236008960261877957 9188770544251680049102117)
                    ·
                      refine ⟨1722894477047190009206647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9188770544251680049102117 1722894477047190009206647)
                      ·
                        rfl

theorem cell23_3355325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_3355325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355325 prefixEnd_3355325 := by exact prefixLift 3355325
  have htrace : WordTrace (prefixWord ++ tailWord_3355325) baseStart_3355325 baseEnd_3355325 := by
    simpa [prefixWord, tailWord_3355325, baseEnd_3355325] using wordTrace_append hprefix tailTrace_3355325
  have hstable : (prefixWord ++ tailWord_3355325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355325).length < 2 ^ (prefixWord ++ tailWord_3355325).sum := by decide
  have hdescent : baseEnd_3355325 < baseStart_3355325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355345 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_3355345 : Nat := 118140960795 + 3355345 * 2 ^ 59
def prefixEnd_3355345 : Nat := 4983230072969 + 3 ^ 40 * 3355345 * 2
def baseEnd_3355345 : Nat := 1722904746660279930956555

theorem tailTrace_3355345 : CollatzResearch.WordTrace tailWord_3355345 prefixEnd_3355345 1722904746660279930956555 := by
  unfold tailWord_3355345
  simp only [CollatzResearch.WordTrace]
  refine ⟨122379486029165587148483489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81586324019443724765655659 122379486029165587148483489)
  ·
    refine ⟨91784614521874190361362617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122379486029165587148483489 91784614521874190361362617)
    ·
      refine ⟨68838460891405642771021963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91784614521874190361362617 68838460891405642771021963)
      ·
        refine ⟨103257691337108464156532945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68838460891405642771021963 103257691337108464156532945)
        ·
          refine ⟨77443268502831348117399709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103257691337108464156532945 77443268502831348117399709)
          ·
            refine ⟨29041225688561755544024891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77443268502831348117399709 29041225688561755544024891)
            ·
              refine ⟨43561838532842633316037337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29041225688561755544024891 43561838532842633316037337)
              ·
                refine ⟨32671378899631974987028003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43561838532842633316037337 32671378899631974987028003)
                ·
                  refine ⟨49007068349447962480542005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32671378899631974987028003 49007068349447962480542005)
                  ·
                    refine ⟨4594412657760746482550813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49007068349447962480542005 4594412657760746482550813)
                    ·
                      refine ⟨1722904746660279930956555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4594412657760746482550813 1722904746660279930956555)
                      ·
                        rfl

theorem cell23_3355345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_3355345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355345 prefixEnd_3355345 := by exact prefixLift 3355345
  have htrace : WordTrace (prefixWord ++ tailWord_3355345) baseStart_3355345 baseEnd_3355345 := by
    simpa [prefixWord, tailWord_3355345, baseEnd_3355345] using wordTrace_append hprefix tailTrace_3355345
  have hstable : (prefixWord ++ tailWord_3355345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355345).length < 2 ^ (prefixWord ++ tailWord_3355345).sum := by decide
  have hdescent : baseEnd_3355345 < baseStart_3355345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355352 : List Nat := [2, 1, 2, 2, 3, 2, 1, 5, 5]
def baseStart_3355352 : Nat := 118140960795 + 3355352 * 2 ^ 59
def prefixEnd_3355352 : Nat := 4983230072969 + 3 ^ 40 * 3355352 * 2
def baseEnd_3355352 : Nat := 191434260113873489285447

theorem tailTrace_3355352 : CollatzResearch.WordTrace tailWord_3355352 prefixEnd_3355352 191434260113873489285447 := by
  unfold tailWord_3355352
  simp only [CollatzResearch.WordTrace]
  refine ⟨61189870670070113671994155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81586494226760151562658873 61189870670070113671994155)
  ·
    refine ⟨91784806005105170507991233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61189870670070113671994155 91784806005105170507991233)
    ·
      refine ⟨68838604503828877880993425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91784806005105170507991233 68838604503828877880993425)
      ·
        refine ⟨51628953377871658410745069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68838604503828877880993425 51628953377871658410745069)
        ·
          refine ⟨19360857516701871904029401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51628953377871658410745069 19360857516701871904029401)
          ·
            refine ⟨14520643137526403928022051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19360857516701871904029401 14520643137526403928022051)
            ·
              refine ⟨21780964706289605892033077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14520643137526403928022051 21780964706289605892033077)
              ·
                refine ⟨2041965441214650552378101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21780964706289605892033077 2041965441214650552378101)
                ·
                  refine ⟨191434260113873489285447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2041965441214650552378101 191434260113873489285447)
                  ·
                    rfl

theorem cell23_3355352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 5, 5].length) (baseStart_3355352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355352 prefixEnd_3355352 := by exact prefixLift 3355352
  have htrace : WordTrace (prefixWord ++ tailWord_3355352) baseStart_3355352 baseEnd_3355352 := by
    simpa [prefixWord, tailWord_3355352, baseEnd_3355352] using wordTrace_append hprefix tailTrace_3355352
  have hstable : (prefixWord ++ tailWord_3355352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355352).length < 2 ^ (prefixWord ++ tailWord_3355352).sum := by decide
  have hdescent : baseEnd_3355352 < baseStart_3355352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355363 : List Nat := [1, 1, 1, 7, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3355363 : Nat := 118140960795 + 3355363 * 2 ^ 59
def prefixEnd_3355363 : Nat := 4983230072969 + 3 ^ 40 * 3355363 * 2
def baseEnd_3355363 : Nat := 1722913989312060860531473

theorem tailTrace_3355363 : CollatzResearch.WordTrace tailWord_3355363 prefixEnd_3355363 1722913989312060860531473 := by
  unfold tailWord_3355363
  simp only [CollatzResearch.WordTrace]
  refine ⟨122380142543100376222638743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81586761695400250815092495 122380142543100376222638743)
  ·
    refine ⟨183570213814650564333958115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122380142543100376222638743 183570213814650564333958115)
    ·
      refine ⟨275355320721975846500937173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183570213814650564333958115 275355320721975846500937173)
      ·
        refine ⟨6453640329421308902365715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 275355320721975846500937173 6453640329421308902365715)
        ·
          refine ⟨9680460494131963353548573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453640329421308902365715 9680460494131963353548573)
          ·
            refine ⟨3630172685299486257580715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9680460494131963353548573 3630172685299486257580715)
            ·
              refine ⟨5445259027949229386371073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630172685299486257580715 5445259027949229386371073)
              ·
                refine ⟨4083944270961922039778305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5445259027949229386371073 4083944270961922039778305)
                ·
                  refine ⟨3062958203221441529833729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4083944270961922039778305 3062958203221441529833729)
                  ·
                    refine ⟨2297218652416081147375297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3062958203221441529833729 2297218652416081147375297)
                    ·
                      refine ⟨1722913989312060860531473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297218652416081147375297 1722913989312060860531473)
                      ·
                        rfl

theorem cell23_3355363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3355363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355363 prefixEnd_3355363 := by exact prefixLift 3355363
  have htrace : WordTrace (prefixWord ++ tailWord_3355363) baseStart_3355363 baseEnd_3355363 := by
    simpa [prefixWord, tailWord_3355363, baseEnd_3355363] using wordTrace_append hprefix tailTrace_3355363
  have hstable : (prefixWord ++ tailWord_3355363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355363).length < 2 ^ (prefixWord ++ tailWord_3355363).sum := by decide
  have hdescent : baseEnd_3355363 < baseStart_3355363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355380 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3355380 : Nat := 118140960795 + 3355380 * 2 ^ 59
def prefixEnd_3355380 : Nat := 4983230072969 + 3 ^ 40 * 3355380 * 2
def baseEnd_3355380 : Nat := 1722922718483187294018895

theorem tailTrace_3355380 : CollatzResearch.WordTrace tailWord_3355380 prefixEnd_3355380 1722922718483187294018895 := by
  unfold tailWord_3355380
  simp only [CollatzResearch.WordTrace]
  refine ⟨61190381292019394063003797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81587175056025858750671729 61190381292019394063003797)
  ·
    refine ⟨2868299123063409096703303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61190381292019394063003797 2868299123063409096703303)
    ·
      refine ⟨4302448684595113645054955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868299123063409096703303 4302448684595113645054955)
      ·
        refine ⟨6453673026892670467582433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4302448684595113645054955 6453673026892670467582433)
        ·
          refine ⟨4840254770169502850686825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6453673026892670467582433 4840254770169502850686825)
          ·
            refine ⟨3630191077627127138015119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4840254770169502850686825 3630191077627127138015119)
            ·
              refine ⟨5445286616440690707022679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630191077627127138015119 5445286616440690707022679)
              ·
                refine ⟨8167929924661036060534019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445286616440690707022679 8167929924661036060534019)
                ·
                  refine ⟨12251894886991554090801029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8167929924661036060534019 12251894886991554090801029)
                  ·
                    refine ⟨2297230291310916392025193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12251894886991554090801029 2297230291310916392025193)
                    ·
                      refine ⟨1722922718483187294018895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297230291310916392025193 1722922718483187294018895)
                      ·
                        rfl

theorem cell23_3355380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3355380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355380 prefixEnd_3355380 := by exact prefixLift 3355380
  have htrace : WordTrace (prefixWord ++ tailWord_3355380) baseStart_3355380 baseEnd_3355380 := by
    simpa [prefixWord, tailWord_3355380, baseEnd_3355380] using wordTrace_append hprefix tailTrace_3355380
  have hstable : (prefixWord ++ tailWord_3355380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355380).length < 2 ^ (prefixWord ++ tailWord_3355380).sum := by decide
  have hdescent : baseEnd_3355380 < baseStart_3355380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355402 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4]
def baseStart_3355402 : Nat := 118140960795 + 3355402 * 2 ^ 59
def prefixEnd_3355402 : Nat := 4983230072969 + 3 ^ 40 * 3355402 * 2
def baseEnd_3355402 : Nat := 1722934015057586207943793

theorem tailTrace_3355402 : CollatzResearch.WordTrace tailWord_3355402 prefixEnd_3355402 1722934015057586207943793 := by
  unfold tailWord_3355402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30595391247489771470827115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81587709993306057255538973 30595391247489771470827115)
  ·
    refine ⟨45893086871234657206240673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30595391247489771470827115 45893086871234657206240673)
    ·
      refine ⟨34419815153425992904680505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45893086871234657206240673 34419815153425992904680505)
      ·
        refine ⟨25814861365069494678510379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34419815153425992904680505 25814861365069494678510379)
        ·
          refine ⟨38722292047604242017765569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25814861365069494678510379 38722292047604242017765569)
          ·
            refine ⟨29041719035703181513324177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38722292047604242017765569 29041719035703181513324177)
            ·
              refine ⟨21781289276777386134993133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29041719035703181513324177 21781289276777386134993133)
              ·
                refine ⟨8167983478791519800622425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21781289276777386134993133 8167983478791519800622425)
                ·
                  refine ⟨6125987609093639850466819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8167983478791519800622425 6125987609093639850466819)
                  ·
                    refine ⟨9188981413640459775700229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6125987609093639850466819 9188981413640459775700229)
                    ·
                      refine ⟨1722934015057586207943793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9188981413640459775700229 1722934015057586207943793)
                      ·
                        rfl

theorem cell23_3355402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_3355402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355402 prefixEnd_3355402 := by exact prefixLift 3355402
  have htrace : WordTrace (prefixWord ++ tailWord_3355402) baseStart_3355402 baseEnd_3355402 := by
    simpa [prefixWord, tailWord_3355402, baseEnd_3355402] using wordTrace_append hprefix tailTrace_3355402
  have hstable : (prefixWord ++ tailWord_3355402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355402).length < 2 ^ (prefixWord ++ tailWord_3355402).sum := by decide
  have hdescent : baseEnd_3355402 < baseStart_3355402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355425 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 8]
def baseStart_3355425 : Nat := 118140960795 + 3355425 * 2 ^ 59
def prefixEnd_3355425 : Nat := 4983230072969 + 3 ^ 40 * 3355425 * 2
def baseEnd_3355425 : Nat := 191438425012515513106243

theorem tailTrace_3355425 : CollatzResearch.WordTrace tailWord_3355425 prefixEnd_3355425 191438425012515513106243 := by
  unfold tailWord_3355425
  simp only [CollatzResearch.WordTrace]
  refine ⟨122382403868875760811395729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81588269245917173874263819 122382403868875760811395729)
  ·
    refine ⟨91786802901656820608546797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122382403868875760811395729 91786802901656820608546797)
    ·
      refine ⟨34420051088121307728205049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91786802901656820608546797 34420051088121307728205049)
      ·
        refine ⟨25815038316090980796153787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34420051088121307728205049 25815038316090980796153787)
        ·
          refine ⟨38722557474136471194230681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815038316090980796153787 38722557474136471194230681)
          ·
            refine ⟨29041918105602353395673011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38722557474136471194230681 29041918105602353395673011)
            ·
              refine ⟨43562877158403530093509517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29041918105602353395673011 43562877158403530093509517)
              ·
                refine ⟨16336078934401323785066069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43562877158403530093509517 16336078934401323785066069)
                ·
                  refine ⟨191438425012515513106243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16336078934401323785066069 191438425012515513106243)
                  ·
                    rfl

theorem cell23_3355425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_3355425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355425 prefixEnd_3355425 := by exact prefixLift 3355425
  have htrace : WordTrace (prefixWord ++ tailWord_3355425) baseStart_3355425 baseEnd_3355425 := by
    simpa [prefixWord, tailWord_3355425, baseEnd_3355425] using wordTrace_append hprefix tailTrace_3355425
  have hstable : (prefixWord ++ tailWord_3355425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355425).length < 2 ^ (prefixWord ++ tailWord_3355425).sum := by decide
  have hdescent : baseEnd_3355425 < baseStart_3355425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355442 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 6]
def baseStart_3355442 : Nat := 118140960795 + 3355442 * 2 ^ 59
def prefixEnd_3355442 : Nat := 4983230072969 + 3 ^ 40 * 3355442 * 2
def baseEnd_3355442 : Nat := 191439394920418450160401

theorem tailTrace_3355442 : CollatzResearch.WordTrace tailWord_3355442 prefixEnd_3355442 191439394920418450160401 := by
  unfold tailWord_3355442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30595755977453543178691145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81588682606542781809843053 30595755977453543178691145)
  ·
    refine ⟨22946816983090157384018359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30595755977453543178691145 22946816983090157384018359)
    ·
      refine ⟨34420225474635236076027539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22946816983090157384018359 34420225474635236076027539)
      ·
        refine ⟨51630338211952854114041309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34420225474635236076027539 51630338211952854114041309)
        ·
          refine ⟨19361376829482320292765491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51630338211952854114041309 19361376829482320292765491)
          ·
            refine ⟨29042065244223480439148237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19361376829482320292765491 29042065244223480439148237)
            ·
              refine ⟨10890774466583805164680589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29042065244223480439148237 10890774466583805164680589)
              ·
                refine ⟨4084040424968926936755221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10890774466583805164680589 4084040424968926936755221)
                ·
                  refine ⟨191439394920418450160401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4084040424968926936755221 191439394920418450160401)
                  ·
                    rfl

theorem cell23_3355442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_3355442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355442 prefixEnd_3355442 := by exact prefixLift 3355442
  have htrace : WordTrace (prefixWord ++ tailWord_3355442) baseStart_3355442 baseEnd_3355442 := by
    simpa [prefixWord, tailWord_3355442, baseEnd_3355442] using wordTrace_append hprefix tailTrace_3355442
  have hstable : (prefixWord ++ tailWord_3355442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355442).length < 2 ^ (prefixWord ++ tailWord_3355442).sum := by decide
  have hdescent : baseEnd_3355442 < baseStart_3355442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355472 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_3355472 : Nat := 118140960795 + 3355472 * 2 ^ 59
def prefixEnd_3355472 : Nat := 4983230072969 + 3 ^ 40 * 3355472 * 2
def baseEnd_3355472 : Nat := 574323319567800311356157

theorem tailTrace_3355472 : CollatzResearch.WordTrace tailWord_3355472 prefixEnd_3355472 574323319567800311356157 := by
  unfold tailWord_3355472
  simp only [CollatzResearch.WordTrace]
  refine ⟨61192059049852743919178335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81589412066470325225571113 61192059049852743919178335)
  ·
    refine ⟨91788088574779115878767503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61192059049852743919178335 91788088574779115878767503)
    ·
      refine ⟨137682132862168673818151255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91788088574779115878767503 137682132862168673818151255)
      ·
        refine ⟨206523199293253010727226883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137682132862168673818151255 206523199293253010727226883)
        ·
          refine ⟨309784798939879516090840325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206523199293253010727226883 309784798939879516090840325)
          ·
            refine ⟨58084649801227409267032561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309784798939879516090840325 58084649801227409267032561)
            ·
              refine ⟨43563487350920556950274421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58084649801227409267032561 43563487350920556950274421)
              ·
                refine ⟨4084076939148802214088227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43563487350920556950274421 4084076939148802214088227)
                ·
                  refine ⟨6126115408723203321132341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084076939148802214088227 6126115408723203321132341)
                  ·
                    refine ⟨574323319567800311356157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6126115408723203321132341 574323319567800311356157)
                    ·
                      rfl

theorem cell23_3355472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_3355472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355472 prefixEnd_3355472 := by exact prefixLift 3355472
  have htrace : WordTrace (prefixWord ++ tailWord_3355472) baseStart_3355472 baseEnd_3355472 := by
    simpa [prefixWord, tailWord_3355472, baseEnd_3355472] using wordTrace_append hprefix tailTrace_3355472
  have hstable : (prefixWord ++ tailWord_3355472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355472).length < 2 ^ (prefixWord ++ tailWord_3355472).sum := by decide
  have hdescent : baseEnd_3355472 < baseStart_3355472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355509 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3355509 : Nat := 118140960795 + 3355509 * 2 ^ 59
def prefixEnd_3355509 : Nat := 4983230072969 + 3 ^ 40 * 3355509 * 2
def baseEnd_3355509 : Nat := 1722988957487617289305801

theorem tailTrace_3355509 : CollatzResearch.WordTrace tailWord_3355509 prefixEnd_3355509 1722988957487617289305801 := by
  unfold tailWord_3355509
  simp only [CollatzResearch.WordTrace]
  refine ⟨122385467600571443157453581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81590311733714295438302387 122385467600571443157453581)
  ·
    refine ⟨45894550350214291184045093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122385467600571443157453581 45894550350214291184045093)
    ·
      refine ⟨8605228190665179597008455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45894550350214291184045093 8605228190665179597008455)
      ·
        refine ⟨12907842285997769395512683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8605228190665179597008455 12907842285997769395512683)
        ·
          refine ⟨19361763428996654093269025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12907842285997769395512683 19361763428996654093269025)
          ·
            refine ⟨14521322571747490569951769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19361763428996654093269025 14521322571747490569951769)
            ·
              refine ⟨10890991928810617927463827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14521322571747490569951769 10890991928810617927463827)
              ·
                refine ⟨16336487893215926891195741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10890991928810617927463827 16336487893215926891195741)
                ·
                  refine ⟨6126182959955972584198403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16336487893215926891195741 6126182959955972584198403)
                  ·
                    refine ⟨9189274439933958876297605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6126182959955972584198403 9189274439933958876297605)
                    ·
                      refine ⟨1722988957487617289305801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9189274439933958876297605 1722988957487617289305801)
                      ·
                        rfl

theorem cell23_3355509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3355509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355509 prefixEnd_3355509 := by exact prefixLift 3355509
  have htrace : WordTrace (prefixWord ++ tailWord_3355509) baseStart_3355509 baseEnd_3355509 := by
    simpa [prefixWord, tailWord_3355509, baseEnd_3355509] using wordTrace_append hprefix tailTrace_3355509
  have hstable : (prefixWord ++ tailWord_3355509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355509).length < 2 ^ (prefixWord ++ tailWord_3355509).sum := by decide
  have hdescent : baseEnd_3355509 < baseStart_3355509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355515 : List Nat := [1, 1, 1, 1, 1, 5, 2, 11]
def baseStart_3355515 : Nat := 118140960795 + 3355515 * 2 ^ 59
def prefixEnd_3355515 : Nat := 4983230072969 + 3 ^ 40 * 3355515 * 2
def baseEnd_3355515 : Nat := 63814519939686824660399

theorem tailTrace_3355515 : CollatzResearch.WordTrace tailWord_3355515 prefixEnd_3355515 63814519939686824660399 := by
  unfold tailWord_3355515
  simp only [CollatzResearch.WordTrace]
  refine ⟨122385686438549706182171999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81590457625699804121447999 122385686438549706182171999)
  ·
    refine ⟨183578529657824559273257999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122385686438549706182171999 183578529657824559273257999)
    ·
      refine ⟨275367794486736838909886999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183578529657824559273257999 275367794486736838909886999)
      ·
        refine ⟨413051691730105258364830499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275367794486736838909886999 413051691730105258364830499)
        ·
          refine ⟨619577537595157887547245749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413051691730105258364830499 619577537595157887547245749)
          ·
            refine ⟨58085394149546051957554289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 619577537595157887547245749 58085394149546051957554289)
            ·
              refine ⟨43564045612159538968165717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58085394149546051957554289 43564045612159538968165717)
              ·
                refine ⟨63814519939686824660399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 43564045612159538968165717 63814519939686824660399)
                ·
                  rfl

theorem cell23_3355515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 11].length) (baseStart_3355515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355515 prefixEnd_3355515 := by exact prefixLift 3355515
  have htrace : WordTrace (prefixWord ++ tailWord_3355515) baseStart_3355515 baseEnd_3355515 := by
    simpa [prefixWord, tailWord_3355515, baseEnd_3355515] using wordTrace_append hprefix tailTrace_3355515
  have hstable : (prefixWord ++ tailWord_3355515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355515).length < 2 ^ (prefixWord ++ tailWord_3355515).sum := by decide
  have hdescent : baseEnd_3355515 < baseStart_3355515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355543 : List Nat := [1, 1, 3, 3, 1, 2, 1, 6, 1, 2, 2]
def baseStart_3355543 : Nat := 118140960795 + 3355543 * 2 ^ 59
def prefixEnd_3355543 : Nat := 4983230072969 + 3 ^ 40 * 3355543 * 2
def baseEnd_3355543 : Nat := 1723006415829870156280645

theorem tailTrace_3355543 : CollatzResearch.WordTrace tailWord_3355543 prefixEnd_3355543 1723006415829870156280645 := by
  unfold tailWord_3355543
  simp only [CollatzResearch.WordTrace]
  refine ⟨122386707682448266964191283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81591138454965511309460855 122386707682448266964191283)
  ·
    refine ⟨183580061523672400446286925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122386707682448266964191283 183580061523672400446286925)
    ·
      refine ⟨68842523071377150167357597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183580061523672400446286925 68842523071377150167357597)
      ·
        refine ⟨25815946151766431312759099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68842523071377150167357597 25815946151766431312759099)
        ·
          refine ⟨38723919227649646969138649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25815946151766431312759099 38723919227649646969138649)
          ·
            refine ⟨29042939420737235226853987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38723919227649646969138649 29042939420737235226853987)
            ·
              refine ⟨43564409131105852840280981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29042939420737235226853987 43564409131105852840280981)
              ·
                refine ⟨2042081678020586851888171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43564409131105852840280981 2042081678020586851888171)
                ·
                  refine ⟨3063122517030880277832257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042081678020586851888171 3063122517030880277832257)
                  ·
                    refine ⟨2297341887773160208374193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3063122517030880277832257 2297341887773160208374193)
                    ·
                      refine ⟨1723006415829870156280645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297341887773160208374193 1723006415829870156280645)
                      ·
                        rfl

theorem cell23_3355543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_3355543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355543 prefixEnd_3355543 := by exact prefixLift 3355543
  have htrace : WordTrace (prefixWord ++ tailWord_3355543) baseStart_3355543 baseEnd_3355543 := by
    simpa [prefixWord, tailWord_3355543, baseEnd_3355543] using wordTrace_append hprefix tailTrace_3355543
  have hstable : (prefixWord ++ tailWord_3355543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355543).length < 2 ^ (prefixWord ++ tailWord_3355543).sum := by decide
  have hdescent : baseEnd_3355543 < baseStart_3355543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355553 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 2, 4]
def baseStart_3355553 : Nat := 118140960795 + 3355553 * 2 ^ 59
def prefixEnd_3355553 : Nat := 4983230072969 + 3 ^ 40 * 3355553 * 2
def baseEnd_3355553 : Nat := 574337183545471705718533

theorem tailTrace_3355553 : CollatzResearch.WordTrace tailWord_3355553 prefixEnd_3355553 574337183545471705718533 := by
  unfold tailWord_3355553
  simp only [CollatzResearch.WordTrace]
  refine ⟨122387072412412038672055313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81591381608274692448036875 122387072412412038672055313)
  ·
    refine ⟨91790304309309029004041485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122387072412412038672055313 91790304309309029004041485)
    ·
      refine ⟨34421364115990885876515557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91790304309309029004041485 34421364115990885876515557)
      ·
        refine ⟨6454005771748291101846667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34421364115990885876515557 6454005771748291101846667)
        ·
          refine ⟨9681008657622436652770001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454005771748291101846667 9681008657622436652770001)
          ·
            refine ⟨7260756493216827489577501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9681008657622436652770001 7260756493216827489577501)
            ·
              refine ⟨2722783684956310308591563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7260756493216827489577501 2722783684956310308591563)
              ·
                refine ⟨4084175527434465462887345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722783684956310308591563 4084175527434465462887345)
                ·
                  refine ⟨3063131645575849097165509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4084175527434465462887345 3063131645575849097165509)
                  ·
                    refine ⟨574337183545471705718533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063131645575849097165509 574337183545471705718533)
                    ·
                      rfl

theorem cell23_3355553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_3355553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355553 prefixEnd_3355553 := by exact prefixLift 3355553
  have htrace : WordTrace (prefixWord ++ tailWord_3355553) baseStart_3355553 baseEnd_3355553 := by
    simpa [prefixWord, tailWord_3355553, baseEnd_3355553] using wordTrace_append hprefix tailTrace_3355553
  have hstable : (prefixWord ++ tailWord_3355553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355553).length < 2 ^ (prefixWord ++ tailWord_3355553).sum := by decide
  have hdescent : baseEnd_3355553 < baseStart_3355553 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355610 : List Nat := [3, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3]
def baseStart_3355610 : Nat := 118140960795 + 3355610 * 2 ^ 59
def prefixEnd_3355610 : Nat := 4983230072969 + 3 ^ 40 * 3355610 * 2
def baseEnd_3355610 : Nat := 1723040819033721394142837

theorem tailTrace_3355610 : CollatzResearch.WordTrace tailWord_3355610 prefixEnd_3355610 1723040819033721394142837 := by
  unfold tailWord_3355610
  simp only [CollatzResearch.WordTrace]
  refine ⟨30597287843301384351720071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81592767582137024937920189 30597287843301384351720071)
  ·
    refine ⟨45895931764952076527580107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30597287843301384351720071 45895931764952076527580107)
    ·
      refine ⟨68843897647428114791370161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45895931764952076527580107 68843897647428114791370161)
      ·
        refine ⟨51632923235571086093527621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68843897647428114791370161 51632923235571086093527621)
        ·
          refine ⟨9681173106669578642536429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51632923235571086093527621 9681173106669578642536429)
          ·
            refine ⟨3630439915001091990951161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9681173106669578642536429 3630439915001091990951161)
            ·
              refine ⟨2722829936250818993213371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630439915001091990951161 2722829936250818993213371)
              ·
                refine ⟨4084244904376228489820057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722829936250818993213371 4084244904376228489820057)
                ·
                  refine ⟨3063183678282171367365043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4084244904376228489820057 3063183678282171367365043)
                  ·
                    refine ⟨4594775517423257051047565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3063183678282171367365043 4594775517423257051047565)
                    ·
                      refine ⟨1723040819033721394142837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4594775517423257051047565 1723040819033721394142837)
                      ·
                        rfl

theorem cell23_3355610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3].length) (baseStart_3355610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355610 prefixEnd_3355610 := by exact prefixLift 3355610
  have htrace : WordTrace (prefixWord ++ tailWord_3355610) baseStart_3355610 baseEnd_3355610 := by
    simpa [prefixWord, tailWord_3355610, baseEnd_3355610] using wordTrace_append hprefix tailTrace_3355610
  have hstable : (prefixWord ++ tailWord_3355610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355610).length < 2 ^ (prefixWord ++ tailWord_3355610).sum := by decide
  have hdescent : baseEnd_3355610 < baseStart_3355610 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355656 : List Nat := [2, 1, 3, 2, 1, 4, 1, 4, 5]
def baseStart_3355656 : Nat := 118140960795 + 3355656 * 2 ^ 59
def prefixEnd_3355656 : Nat := 4983230072969 + 3 ^ 40 * 3355656 * 2
def baseEnd_3355656 : Nat := 191451604349314246018625

theorem tailTrace_3355656 : CollatzResearch.WordTrace tailWord_3355656 prefixEnd_3355656 191451604349314246018625 := by
  unfold tailWord_3355656
  simp only [CollatzResearch.WordTrace]
  refine ⟨61195414565519443631527411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81593886087359258175369881 61195414565519443631527411)
  ·
    refine ⟨91793121848279165447291117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61195414565519443631527411 91793121848279165447291117)
    ·
      refine ⟨34422420693104687042734169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91793121848279165447291117 34422420693104687042734169)
      ·
        refine ⟨25816815519828515282050627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34422420693104687042734169 25816815519828515282050627)
        ·
          refine ⟨38725223279742772923075941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25816815519828515282050627 38725223279742772923075941)
          ·
            refine ⟨7260979364951769923076739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38725223279742772923075941 7260979364951769923076739)
            ·
              refine ⟨10891469047427654884615109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7260979364951769923076739 10891469047427654884615109)
              ·
                refine ⟨2042150446392685290865333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10891469047427654884615109 2042150446392685290865333)
                ·
                  refine ⟨191451604349314246018625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2042150446392685290865333 191451604349314246018625)
                  ·
                    rfl

theorem cell23_3355656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 5].length) (baseStart_3355656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355656 prefixEnd_3355656 := by exact prefixLift 3355656
  have htrace : WordTrace (prefixWord ++ tailWord_3355656) baseStart_3355656 baseEnd_3355656 := by
    simpa [prefixWord, tailWord_3355656, baseEnd_3355656] using wordTrace_append hprefix tailTrace_3355656
  have hstable : (prefixWord ++ tailWord_3355656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355656).length < 2 ^ (prefixWord ++ tailWord_3355656).sum := by decide
  have hdescent : baseEnd_3355656 < baseStart_3355656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355699 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 7, 4]
def baseStart_3355699 : Nat := 118140960795 + 3355699 * 2 ^ 59
def prefixEnd_3355699 : Nat := 4983230072969 + 3 ^ 40 * 3355699 * 2
def baseEnd_3355699 : Nat := 574362172937323848643309

theorem tailTrace_3355699 : CollatzResearch.WordTrace tailWord_3355699 prefixEnd_3355699 574362172937323848643309 := by
  unfold tailWord_3355699
  simp only [CollatzResearch.WordTrace]
  refine ⟨122392397469883105606870151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81594931646588737071246767 122392397469883105606870151)
  ·
    refine ⟨183588596204824658410305227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122392397469883105606870151 183588596204824658410305227)
    ·
      refine ⟨275382894307236987615457841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183588596204824658410305227 275382894307236987615457841)
      ·
        refine ⟨206537170730427740711593381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275382894307236987615457841 206537170730427740711593381)
        ·
          refine ⟨38725719511955201383423759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206537170730427740711593381 38725719511955201383423759)
          ·
            refine ⟨58088579267932802075135639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38725719511955201383423759 58088579267932802075135639)
            ·
              refine ⟨87132868901899203112703459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58088579267932802075135639 87132868901899203112703459)
              ·
                refine ⟨130699303352848804669055189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87132868901899203112703459 130699303352848804669055189)
                ·
                  refine ⟨3063264922332393859430981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 130699303352848804669055189 3063264922332393859430981)
                  ·
                    refine ⟨574362172937323848643309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063264922332393859430981 574362172937323848643309)
                    ·
                      rfl

theorem cell23_3355699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 7, 4].length) (baseStart_3355699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355699 prefixEnd_3355699 := by exact prefixLift 3355699
  have htrace : WordTrace (prefixWord ++ tailWord_3355699) baseStart_3355699 baseEnd_3355699 := by
    simpa [prefixWord, tailWord_3355699, baseEnd_3355699] using wordTrace_append hprefix tailTrace_3355699
  have hstable : (prefixWord ++ tailWord_3355699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355699).length < 2 ^ (prefixWord ++ tailWord_3355699).sum := by decide
  have hdescent : baseEnd_3355699 < baseStart_3355699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355706 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2]
def baseStart_3355706 : Nat := 118140960795 + 3355706 * 2 ^ 59
def prefixEnd_3355706 : Nat := 4983230072969 + 3 ^ 40 * 3355706 * 2
def baseEnd_3355706 : Nat := 1723090113176553018542395

theorem tailTrace_3355706 : CollatzResearch.WordTrace tailWord_3355706 prefixEnd_3355706 1723090113176553018542395 := by
  unfold tailWord_3355706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30598163195214436450593743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81595101853905163868249981 30598163195214436450593743)
  ·
    refine ⟨45897244792821654675890615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30598163195214436450593743 45897244792821654675890615)
    ·
      refine ⟨68845867189232482013835923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45897244792821654675890615 68845867189232482013835923)
      ·
        refine ⟨103268800783848723020753885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68845867189232482013835923 103268800783848723020753885)
        ·
          refine ⟨38725800293943271132782707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103268800783848723020753885 38725800293943271132782707)
          ·
            refine ⟨58088700440914906699174061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38725800293943271132782707 58088700440914906699174061)
            ·
              refine ⟨21783262665343090012190273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58088700440914906699174061 21783262665343090012190273)
              ·
                refine ⟨16337446999007317509142705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21783262665343090012190273 16337446999007317509142705)
                ·
                  refine ⟨12253085249255488131857029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16337446999007317509142705 12253085249255488131857029)
                  ·
                    refine ⟨2297453484235404024723193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12253085249255488131857029 2297453484235404024723193)
                    ·
                      refine ⟨1723090113176553018542395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297453484235404024723193 1723090113176553018542395)
                      ·
                        rfl

theorem cell23_3355706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2].length) (baseStart_3355706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355706 prefixEnd_3355706 := by exact prefixLift 3355706
  have htrace : WordTrace (prefixWord ++ tailWord_3355706) baseStart_3355706 baseEnd_3355706 := by
    simpa [prefixWord, tailWord_3355706, baseEnd_3355706] using wordTrace_append hprefix tailTrace_3355706
  have hstable : (prefixWord ++ tailWord_3355706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355706).length < 2 ^ (prefixWord ++ tailWord_3355706).sum := by decide
  have hdescent : baseEnd_3355706 < baseStart_3355706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355729 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 6]
def baseStart_3355729 : Nat := 118140960795 + 3355729 * 2 ^ 59
def prefixEnd_3355729 : Nat := 4983230072969 + 3 ^ 40 * 3355729 * 2
def baseEnd_3355729 : Nat := 191455769247956269839421

theorem tailTrace_3355729 : CollatzResearch.WordTrace tailWord_3355729 prefixEnd_3355729 191455769247956269839421 := by
  unfold tailWord_3355729
  simp only [CollatzResearch.WordTrace]
  refine ⟨122393491659774420730462241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81595661106516280486974827 122393491659774420730462241)
  ·
    refine ⟨91795118744830815547846681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122393491659774420730462241 91795118744830815547846681)
    ·
      refine ⟨68846339058623111660885011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91795118744830815547846681 68846339058623111660885011)
      ·
        refine ⟨103269508587934667491327517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68846339058623111660885011 103269508587934667491327517)
        ·
          refine ⟨38726065720475500309247819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103269508587934667491327517 38726065720475500309247819)
          ·
            refine ⟨58089098580713250463871729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38726065720475500309247819 58089098580713250463871729)
            ·
              refine ⟨43566823935534937847903797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58089098580713250463871729 43566823935534937847903797)
              ·
                refine ⟨4084389743956400423240981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43566823935534937847903797 4084389743956400423240981)
                ·
                  refine ⟨191455769247956269839421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4084389743956400423240981 191455769247956269839421)
                  ·
                    rfl

theorem cell23_3355729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_3355729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355729 prefixEnd_3355729 := by exact prefixLift 3355729
  have htrace : WordTrace (prefixWord ++ tailWord_3355729) baseStart_3355729 baseEnd_3355729 := by
    simpa [prefixWord, tailWord_3355729, baseEnd_3355729] using wordTrace_append hprefix tailTrace_3355729
  have hstable : (prefixWord ++ tailWord_3355729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355729).length < 2 ^ (prefixWord ++ tailWord_3355729).sum := by decide
  have hdescent : baseEnd_3355729 < baseStart_3355729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355746 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 8]
def baseStart_3355746 : Nat := 118140960795 + 3355746 * 2 ^ 59
def prefixEnd_3355746 : Nat := 4983230072969 + 3 ^ 40 * 3355746 * 2
def baseEnd_3355746 : Nat := 191456739155859206893579

theorem tailTrace_3355746 : CollatzResearch.WordTrace tailWord_3355746 prefixEnd_3355746 191456739155859206893579 := by
  unfold tailWord_3355746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30598527925178208158457773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81596074467141888422554061 30598527925178208158457773)
  ·
    refine ⟨11474447971941828059421665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30598527925178208158457773 11474447971941828059421665)
    ·
      refine ⟨8605835978956371044566249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11474447971941828059421665 8605835978956371044566249)
      ·
        refine ⟨6454376984217278283424687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8605835978956371044566249 6454376984217278283424687)
        ·
          refine ⟨9681565476325917425137031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6454376984217278283424687 9681565476325917425137031)
          ·
            refine ⟨14522348214488876137705547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681565476325917425137031 14522348214488876137705547)
            ·
              refine ⟨21783522321733314206558321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14522348214488876137705547 21783522321733314206558321)
              ·
                refine ⟨16337641741299985654918741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21783522321733314206558321 16337641741299985654918741)
                ·
                  refine ⟨191456739155859206893579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16337641741299985654918741 191456739155859206893579)
                  ·
                    rfl

theorem cell23_3355746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_3355746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355746 prefixEnd_3355746 := by exact prefixLift 3355746
  have htrace : WordTrace (prefixWord ++ tailWord_3355746) baseStart_3355746 baseEnd_3355746 := by
    simpa [prefixWord, tailWord_3355746, baseEnd_3355746] using wordTrace_append hprefix tailTrace_3355746
  have hstable : (prefixWord ++ tailWord_3355746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355746).length < 2 ^ (prefixWord ++ tailWord_3355746).sum := by decide
  have hdescent : baseEnd_3355746 < baseStart_3355746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355800 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3355800 : Nat := 118140960795 + 3355800 * 2 ^ 59
def prefixEnd_3355800 : Nat := 4983230072969 + 3 ^ 40 * 3355800 * 2
def baseEnd_3355800 : Nat := 1723138380358075650766963

theorem tailTrace_3355800 : CollatzResearch.WordTrace tailWord_3355800 prefixEnd_3355800 1723138380358075650766963 := by
  unfold tailWord_3355800
  simp only [CollatzResearch.WordTrace]
  refine ⟨61198040621258599928148427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81597387495011466570864569 61198040621258599928148427)
  ·
    refine ⟨91797060931887899892222641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61198040621258599928148427 91797060931887899892222641)
    ·
      refine ⟨68847795698915924919166981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91797060931887899892222641 68847795698915924919166981)
      ·
        refine ⟨12908961693546735922343809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68847795698915924919166981 12908961693546735922343809)
        ·
          refine ⟨9681721270160051941757857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12908961693546735922343809 9681721270160051941757857)
          ·
            refine ⟨7261290952620038956318393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9681721270160051941757857 7261290952620038956318393)
            ·
              refine ⟨5445968214465029217238795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7261290952620038956318393 5445968214465029217238795)
              ·
                refine ⟨8168952321697543825858193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445968214465029217238795 8168952321697543825858193)
                ·
                  refine ⟨6126714241273157869393645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8168952321697543825858193 6126714241273157869393645)
                  ·
                    refine ⟨2297517840477434201022617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6126714241273157869393645 2297517840477434201022617)
                    ·
                      refine ⟨1723138380358075650766963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297517840477434201022617 1723138380358075650766963)
                      ·
                        rfl

theorem cell23_3355800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3355800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355800 prefixEnd_3355800 := by exact prefixLift 3355800
  have htrace : WordTrace (prefixWord ++ tailWord_3355800) baseStart_3355800 baseEnd_3355800 := by
    simpa [prefixWord, tailWord_3355800, baseEnd_3355800] using wordTrace_append hprefix tailTrace_3355800
  have hstable : (prefixWord ++ tailWord_3355800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355800).length < 2 ^ (prefixWord ++ tailWord_3355800).sum := by decide
  have hdescent : baseEnd_3355800 < baseStart_3355800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355836 : List Nat := [2, 2, 2, 3, 2, 1, 3, 8]
def baseStart_3355836 : Nat := 118140960795 + 3355836 * 2 ^ 59
def prefixEnd_3355836 : Nat := 4983230072969 + 3 ^ 40 * 3355836 * 2
def baseEnd_3355836 : Nat := 63820624654134722589511

theorem tailTrace_3355836 : CollatzResearch.WordTrace tailWord_3355836 prefixEnd_3355836 63820624654134722589511 := by
  unfold tailWord_3355836
  simp only [CollatzResearch.WordTrace]
  refine ⟨61198697135193389002303681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81598262846924518669738241 61198697135193389002303681)
  ·
    refine ⟨45899022851395041751727761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61198697135193389002303681 45899022851395041751727761)
    ·
      refine ⟨34424267138546281313795821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45899022851395041751727761 34424267138546281313795821)
      ·
        refine ⟨12909100176954855492673433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34424267138546281313795821 12909100176954855492673433)
        ·
          refine ⟨9681825132716141619505075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12909100176954855492673433 9681825132716141619505075)
          ·
            refine ⟨14522737699074212429257613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9681825132716141619505075 14522737699074212429257613)
            ·
              refine ⟨5446026637152829660971605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14522737699074212429257613 5446026637152829660971605)
              ·
                refine ⟨63820624654134722589511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5446026637152829660971605 63820624654134722589511)
                ·
                  rfl

theorem cell23_3355836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 8].length) (baseStart_3355836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355836 prefixEnd_3355836 := by exact prefixLift 3355836
  have htrace : WordTrace (prefixWord ++ tailWord_3355836) baseStart_3355836 baseEnd_3355836 := by
    simpa [prefixWord, tailWord_3355836, baseEnd_3355836] using wordTrace_append hprefix tailTrace_3355836
  have hstable : (prefixWord ++ tailWord_3355836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355836).length < 2 ^ (prefixWord ++ tailWord_3355836).sum := by decide
  have hdescent : baseEnd_3355836 < baseStart_3355836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355839 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6]
def baseStart_3355839 : Nat := 118140960795 + 3355839 * 2 ^ 59
def prefixEnd_3355839 : Nat := 4983230072969 + 3 ^ 40 * 3355839 * 2
def baseEnd_3355839 : Nat := 1723158406103600998179283

theorem tailTrace_3355839 : CollatzResearch.WordTrace tailWord_3355839 prefixEnd_3355839 1723158406103600998179283 := by
  unfold tailWord_3355839
  simp only [CollatzResearch.WordTrace]
  refine ⟨122397503689375909516966571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81598335792917273011311047 122397503689375909516966571)
  ·
    refine ⟨183596255534063864275449857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122397503689375909516966571 183596255534063864275449857)
    ·
      refine ⟨137697191650547898206587393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183596255534063864275449857 137697191650547898206587393)
      ·
        refine ⟨103272893737910923654940545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137697191650547898206587393 103272893737910923654940545)
        ·
          refine ⟨77454670303433192741205409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103272893737910923654940545 77454670303433192741205409)
          ·
            refine ⟨58091002727574894555904057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77454670303433192741205409 58091002727574894555904057)
            ·
              refine ⟨43568252045681170916928043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58091002727574894555904057 43568252045681170916928043)
              ·
                refine ⟨65352378068521756375392065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43568252045681170916928043 65352378068521756375392065)
                ·
                  refine ⟨49014283551391317281544049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65352378068521756375392065 49014283551391317281544049)
                  ·
                    refine ⟨36760712663543487961158037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49014283551391317281544049 36760712663543487961158037)
                    ·
                      refine ⟨1723158406103600998179283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36760712663543487961158037 1723158406103600998179283)
                      ·
                        rfl

theorem cell23_3355839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_3355839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355839 prefixEnd_3355839 := by exact prefixLift 3355839
  have htrace : WordTrace (prefixWord ++ tailWord_3355839) baseStart_3355839 baseEnd_3355839 := by
    simpa [prefixWord, tailWord_3355839, baseEnd_3355839] using wordTrace_append hprefix tailTrace_3355839
  have hstable : (prefixWord ++ tailWord_3355839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355839).length < 2 ^ (prefixWord ++ tailWord_3355839).sum := by decide
  have hdescent : baseEnd_3355839 < baseStart_3355839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355859 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5]
def baseStart_3355859 : Nat := 118140960795 + 3355859 * 2 ^ 59
def prefixEnd_3355859 : Nat := 4983230072969 + 3 ^ 40 * 3355859 * 2
def baseEnd_3355859 : Nat := 1723168675716690919929191

theorem tailTrace_3355859 : CollatzResearch.WordTrace tailWord_3355859 prefixEnd_3355859 1723168675716690919929191 := by
  unfold tailWord_3355859
  simp only [CollatzResearch.WordTrace]
  refine ⟨122398233149303452932694631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81598822099535635288463087 122398233149303452932694631)
  ·
    refine ⟨183597349723955179399041947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122398233149303452932694631 183597349723955179399041947)
    ·
      refine ⟨275396024585932769098562921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183597349723955179399041947 275396024585932769098562921)
      ·
        refine ⟨206547018439449576823922191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275396024585932769098562921 206547018439449576823922191)
        ·
          refine ⟨309820527659174365235883287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206547018439449576823922191 309820527659174365235883287)
          ·
            refine ⟨464730791488761547853824931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309820527659174365235883287 464730791488761547853824931)
            ·
              refine ⟨697096187233142321780737397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 464730791488761547853824931 697096187233142321780737397)
              ·
                refine ⟨65352767553107092666944131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 697096187233142321780737397 65352767553107092666944131)
                ·
                  refine ⟨98029151329660639000416197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65352767553107092666944131 98029151329660639000416197)
                  ·
                    refine ⟨18380465874311369812578037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98029151329660639000416197 18380465874311369812578037)
                    ·
                      refine ⟨1723168675716690919929191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18380465874311369812578037 1723168675716690919929191)
                      ·
                        rfl

theorem cell23_3355859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 5].length) (baseStart_3355859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355859 prefixEnd_3355859 := by exact prefixLift 3355859
  have htrace : WordTrace (prefixWord ++ tailWord_3355859) baseStart_3355859 baseEnd_3355859 := by
    simpa [prefixWord, tailWord_3355859, baseEnd_3355859] using wordTrace_append hprefix tailTrace_3355859
  have hstable : (prefixWord ++ tailWord_3355859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355859).length < 2 ^ (prefixWord ++ tailWord_3355859).sum := by decide
  have hdescent : baseEnd_3355859 < baseStart_3355859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355864 : List Nat := [2, 1, 2, 2, 5, 1, 2, 3, 1, 2, 2]
def baseStart_3355864 : Nat := 118140960795 + 3355864 * 2 ^ 59
def prefixEnd_3355864 : Nat := 4983230072969 + 3 ^ 40 * 3355864 * 2
def baseEnd_3355864 : Nat := 1723171243119963400366669

theorem tailTrace_3355864 : CollatzResearch.WordTrace tailWord_3355864 prefixEnd_3355864 1723171243119963400366669 := by
  unfold tailWord_3355864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61199207757142669393313323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81598943676190225857751097 61199207757142669393313323)
  ·
    refine ⟨91798811635714004089969985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61199207757142669393313323 91798811635714004089969985)
    ·
      refine ⟨68849108726785503067477489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91798811635714004089969985 68849108726785503067477489)
      ·
        refine ⟨51636831545089127300608117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68849108726785503067477489 51636831545089127300608117)
        ·
          refine ⟨4840952957352105684432011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51636831545089127300608117 4840952957352105684432011)
          ·
            refine ⟨7261429436028158526648017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4840952957352105684432011 7261429436028158526648017)
            ·
              refine ⟨5446072077021118894986013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7261429436028158526648017 5446072077021118894986013)
              ·
                refine ⟨2042277028882919585619755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5446072077021118894986013 2042277028882919585619755)
                ·
                  refine ⟨3063415543324379378429633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042277028882919585619755 3063415543324379378429633)
                  ·
                    refine ⟨2297561657493284533822225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3063415543324379378429633 2297561657493284533822225)
                    ·
                      refine ⟨1723171243119963400366669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297561657493284533822225 1723171243119963400366669)
                      ·
                        rfl

theorem cell23_3355864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_3355864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355864 prefixEnd_3355864 := by exact prefixLift 3355864
  have htrace : WordTrace (prefixWord ++ tailWord_3355864) baseStart_3355864 baseEnd_3355864 := by
    simpa [prefixWord, tailWord_3355864, baseEnd_3355864] using wordTrace_append hprefix tailTrace_3355864
  have hstable : (prefixWord ++ tailWord_3355864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355864).length < 2 ^ (prefixWord ++ tailWord_3355864).sum := by decide
  have hdescent : baseEnd_3355864 < baseStart_3355864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355886 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3355886 : Nat := 118140960795 + 3355886 * 2 ^ 59
def prefixEnd_3355886 : Nat := 4983230072969 + 3 ^ 40 * 3355886 * 2
def baseEnd_3355886 : Nat := 1723182539694362314291567

theorem tailTrace_3355886 : CollatzResearch.WordTrace tailWord_3355886 prefixEnd_3355886 1723182539694362314291567 := by
  unfold tailWord_3355886
  simp only [CollatzResearch.WordTrace]
  refine ⟨15299902240025704567990939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81599478613470424362618341 15299902240025704567990939)
  ·
    refine ⟨22949853360038556851986409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15299902240025704567990939 22949853360038556851986409)
    ·
      refine ⟨17212390020028917638989807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22949853360038556851986409 17212390020028917638989807)
      ·
        refine ⟨25818585030043376458484711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17212390020028917638989807 25818585030043376458484711)
        ·
          refine ⟨38727877545065064687727067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25818585030043376458484711 38727877545065064687727067)
          ·
            refine ⟨58091816317597597031590601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38727877545065064687727067 58091816317597597031590601)
            ·
              refine ⟨43568862238198197773692951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58091816317597597031590601 43568862238198197773692951)
              ·
                refine ⟨65353293357297296660539427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43568862238198197773692951 65353293357297296660539427)
                ·
                  refine ⟨98029940035945944990809141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65353293357297296660539427 98029940035945944990809141)
                  ·
                    refine ⟨9190306878369932342888357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98029940035945944990809141 9190306878369932342888357)
                    ·
                      refine ⟨1723182539694362314291567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9190306878369932342888357 1723182539694362314291567)
                      ·
                        rfl

theorem cell23_3355886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3355886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355886 prefixEnd_3355886 := by exact prefixLift 3355886
  have htrace : WordTrace (prefixWord ++ tailWord_3355886) baseStart_3355886 baseEnd_3355886 := by
    simpa [prefixWord, tailWord_3355886, baseEnd_3355886] using wordTrace_append hprefix tailTrace_3355886
  have hstable : (prefixWord ++ tailWord_3355886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355886).length < 2 ^ (prefixWord ++ tailWord_3355886).sum := by decide
  have hdescent : baseEnd_3355886 < baseStart_3355886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355899 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10]
def baseStart_3355899 : Nat := 118140960795 + 3355899 * 2 ^ 59
def prefixEnd_3355899 : Nat := 4983230072969 + 3 ^ 40 * 3355899 * 2
def baseEnd_3355899 : Nat := 1723189214942870763429007

theorem tailTrace_3355899 : CollatzResearch.WordTrace tailWord_3355899 prefixEnd_3355899 1723189214942870763429007 := by
  unfold tailWord_3355899
  simp only [CollatzResearch.WordTrace]
  refine ⟨122399692069158539764150751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81599794712772359842767167 122399692069158539764150751)
  ·
    refine ⟨183599538103737809646226127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122399692069158539764150751 183599538103737809646226127)
    ·
      refine ⟨275399307155606714469339191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183599538103737809646226127 275399307155606714469339191)
      ·
        refine ⟨413098960733410071704008787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275399307155606714469339191 413098960733410071704008787)
        ·
          refine ⟨619648441100115107556013181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413098960733410071704008787 619648441100115107556013181)
          ·
            refine ⟨232368165412543165333504943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 619648441100115107556013181 232368165412543165333504943)
            ·
              refine ⟨348552248118814748000257415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232368165412543165333504943 348552248118814748000257415)
              ·
                refine ⟨522828372178222122000386123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 348552248118814748000257415 522828372178222122000386123)
                ·
                  refine ⟨784242558267333183000579185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 522828372178222122000386123 784242558267333183000579185)
                  ·
                    refine ⟨588181918700499887250434389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 784242558267333183000579185 588181918700499887250434389)
                    ·
                      refine ⟨1723189214942870763429007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 588181918700499887250434389 1723189214942870763429007)
                      ·
                        rfl

theorem cell23_3355899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 10].length) (baseStart_3355899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355899 prefixEnd_3355899 := by exact prefixLift 3355899
  have htrace : WordTrace (prefixWord ++ tailWord_3355899) baseStart_3355899 baseEnd_3355899 := by
    simpa [prefixWord, tailWord_3355899, baseEnd_3355899] using wordTrace_append hprefix tailTrace_3355899
  have hstable : (prefixWord ++ tailWord_3355899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355899).length < 2 ^ (prefixWord ++ tailWord_3355899).sum := by decide
  have hdescent : baseEnd_3355899 < baseStart_3355899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355954 : List Nat := [3, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2]
def baseStart_3355954 : Nat := 118140960795 + 3355954 * 2 ^ 59
def prefixEnd_3355954 : Nat := 4983230072969 + 3 ^ 40 * 3355954 * 2
def baseEnd_3355954 : Nat := 1723217456378868048241255

theorem tailTrace_3355954 : CollatzResearch.WordTrace tailWord_3355954 prefixEnd_3355954 1723217456378868048241255 := by
  unfold tailWord_3355954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30600424520989821039350729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81601132055972856104935277 30600424520989821039350729)
  ·
    refine ⟨22950318390742365779513047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30600424520989821039350729 22950318390742365779513047)
    ·
      refine ⟨34425477586113548669269571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22950318390742365779513047 34425477586113548669269571)
      ·
        refine ⟨51638216379170323003904357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34425477586113548669269571 51638216379170323003904357)
        ·
          refine ⟨9682165571094435563232067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51638216379170323003904357 9682165571094435563232067)
          ·
            refine ⟨14523248356641653344848101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9682165571094435563232067 14523248356641653344848101)
            ·
              refine ⟨2723109066870310002159019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14523248356641653344848101 2723109066870310002159019)
              ·
                refine ⟨4084663600305465003238529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723109066870310002159019 4084663600305465003238529)
                ·
                  refine ⟨3063497700229098752428897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4084663600305465003238529 3063497700229098752428897)
                  ·
                    refine ⟨2297623275171824064321673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3063497700229098752428897 2297623275171824064321673)
                    ·
                      refine ⟨1723217456378868048241255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297623275171824064321673 1723217456378868048241255)
                      ·
                        rfl

theorem cell23_3355954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_3355954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355954 prefixEnd_3355954 := by exact prefixLift 3355954
  have htrace : WordTrace (prefixWord ++ tailWord_3355954) baseStart_3355954 baseEnd_3355954 := by
    simpa [prefixWord, tailWord_3355954, baseEnd_3355954] using wordTrace_append hprefix tailTrace_3355954
  have hstable : (prefixWord ++ tailWord_3355954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355954).length < 2 ^ (prefixWord ++ tailWord_3355954).sum := by decide
  have hdescent : baseEnd_3355954 < baseStart_3355954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355958 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2]
def baseStart_3355958 : Nat := 118140960795 + 3355958 * 2 ^ 59
def prefixEnd_3355958 : Nat := 4983230072969 + 3 ^ 40 * 3355958 * 2
def baseEnd_3355958 : Nat := 1723219510301486032591237

theorem tailTrace_3355958 : CollatzResearch.WordTrace tailWord_3355958 prefixEnd_3355958 1723219510301486032591237 := by
  unfold tailWord_3355958
  simp only [CollatzResearch.WordTrace]
  refine ⟨7650115248496549552534283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81601229317296528560365685 7650115248496549552534283)
  ·
    refine ⟨11475172872744824328801425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7650115248496549552534283 11475172872744824328801425)
    ·
      refine ⟨8606379654558618246601069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11475172872744824328801425 8606379654558618246601069)
      ·
        refine ⟨3227392370459481842475401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8606379654558618246601069 3227392370459481842475401)
        ·
          refine ⟨2420544277844611381856551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3227392370459481842475401 2420544277844611381856551)
          ·
            refine ⟨3630816416766917072784827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420544277844611381856551 3630816416766917072784827)
            ·
              refine ⟨5446224625150375609177241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3630816416766917072784827 5446224625150375609177241)
              ·
                refine ⟨4084668468862781706882931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5446224625150375609177241 4084668468862781706882931)
                ·
                  refine ⟨6127002703294172560324397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084668468862781706882931 6127002703294172560324397)
                  ·
                    refine ⟨2297626013735314710121649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6127002703294172560324397 2297626013735314710121649)
                    ·
                      refine ⟨1723219510301486032591237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297626013735314710121649 1723219510301486032591237)
                      ·
                        rfl

theorem cell23_3355958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_3355958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355958 prefixEnd_3355958 := by exact prefixLift 3355958
  have htrace : WordTrace (prefixWord ++ tailWord_3355958) baseStart_3355958 baseEnd_3355958 := by
    simpa [prefixWord, tailWord_3355958, baseEnd_3355958] using wordTrace_append hprefix tailTrace_3355958
  have hstable : (prefixWord ++ tailWord_3355958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355958).length < 2 ^ (prefixWord ++ tailWord_3355958).sum := by decide
  have hdescent : baseEnd_3355958 < baseStart_3355958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3355993 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_3355993 : Nat := 118140960795 + 3355993 * 2 ^ 59
def prefixEnd_3355993 : Nat := 4983230072969 + 3 ^ 40 * 3355993 * 2
def baseEnd_3355993 : Nat := 1723237482124393395653575

theorem tailTrace_3355993 : CollatzResearch.WordTrace tailWord_3355993 prefixEnd_3355993 1723237482124393395653575 := by
  unfold tailWord_3355993
  simp only [CollatzResearch.WordTrace]
  refine ⟨122403120530817993818072633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81602080353878662545381755 122403120530817993818072633)
  ·
    refine ⟨91802340398113495363554475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122403120530817993818072633 91802340398113495363554475)
    ·
      refine ⟨137703510597170243045331713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91802340398113495363554475 137703510597170243045331713)
      ·
        refine ⟨103277632947877682283998785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137703510597170243045331713 103277632947877682283998785)
        ·
          refine ⟨77458224710908261712999089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103277632947877682283998785 77458224710908261712999089)
          ·
            refine ⟨58093668533181196284749317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77458224710908261712999089 58093668533181196284749317)
            ·
              refine ⟨10892562849971474303390497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58093668533181196284749317 10892562849971474303390497)
              ·
                refine ⟨8169422137478605727542873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10892562849971474303390497 8169422137478605727542873)
                ·
                  refine ⟨6127066603108954295657155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8169422137478605727542873 6127066603108954295657155)
                  ·
                    refine ⟨9190599904663431443485733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6127066603108954295657155 9190599904663431443485733)
                    ·
                      refine ⟨1723237482124393395653575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9190599904663431443485733 1723237482124393395653575)
                      ·
                        rfl

theorem cell23_3355993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_3355993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3355993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3355993 prefixEnd_3355993 := by exact prefixLift 3355993
  have htrace : WordTrace (prefixWord ++ tailWord_3355993) baseStart_3355993 baseEnd_3355993 := by
    simpa [prefixWord, tailWord_3355993, baseEnd_3355993] using wordTrace_append hprefix tailTrace_3355993
  have hstable : (prefixWord ++ tailWord_3355993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3355993).length < 2 ^ (prefixWord ++ tailWord_3355993).sum := by decide
  have hdescent : baseEnd_3355993 < baseStart_3355993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3355993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356083 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4]
def baseStart_3356083 : Nat := 118140960795 + 3356083 * 2 ^ 59
def prefixEnd_3356083 : Nat := 4983230072969 + 3 ^ 40 * 3356083 * 2
def baseEnd_3356083 : Nat := 1723283695383298043528161

theorem tailTrace_3356083 : CollatzResearch.WordTrace tailWord_3356083 prefixEnd_3356083 1723283695383298043528161 := by
  unfold tailWord_3356083
  simp only [CollatzResearch.WordTrace]
  refine ⟨122406403100491939188848903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81604268733661292792565935 122406403100491939188848903)
  ·
    refine ⟨183609604650737908783273355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122406403100491939188848903 183609604650737908783273355)
    ·
      refine ⟨275414406976106863174910033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183609604650737908783273355 275414406976106863174910033)
      ·
        refine ⟨206560805232080147381182525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275414406976106863174910033 206560805232080147381182525)
        ·
          refine ⟨77460301962030055267943447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206560805232080147381182525 77460301962030055267943447)
          ·
            refine ⟨116190452943045082901915171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77460301962030055267943447 116190452943045082901915171)
            ·
              refine ⟨174285679414567624352872757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116190452943045082901915171 174285679414567624352872757)
              ·
                refine ⟨16339282445115714783081821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174285679414567624352872757 16339282445115714783081821)
                ·
                  refine ⟨6127230916918393043655683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16339282445115714783081821 6127230916918393043655683)
                  ·
                    refine ⟨9190846375377589565483525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6127230916918393043655683 9190846375377589565483525)
                    ·
                      refine ⟨1723283695383298043528161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9190846375377589565483525 1723283695383298043528161)
                      ·
                        rfl

theorem cell23_3356083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 4].length) (baseStart_3356083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356083 prefixEnd_3356083 := by exact prefixLift 3356083
  have htrace : WordTrace (prefixWord ++ tailWord_3356083) baseStart_3356083 baseEnd_3356083 := by
    simpa [prefixWord, tailWord_3356083, baseEnd_3356083] using wordTrace_append hprefix tailTrace_3356083
  have hstable : (prefixWord ++ tailWord_3356083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356083).length < 2 ^ (prefixWord ++ tailWord_3356083).sum := by decide
  have hdescent : baseEnd_3356083 < baseStart_3356083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356093 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_3356093 : Nat := 118140960795 + 3356093 * 2 ^ 59
def prefixEnd_3356093 : Nat := 4983230072969 + 3 ^ 40 * 3356093 * 2
def baseEnd_3356093 : Nat := 574429610063281001467705

theorem tailTrace_3356093 : CollatzResearch.WordTrace tailWord_3356093 prefixEnd_3356093 574429610063281001467705 := by
  unfold tailWord_3356093
  simp only [CollatzResearch.WordTrace]
  refine ⟨122406767830455710896712933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81604511886970473931141955 122406767830455710896712933)
  ·
    refine ⟨22951268968210445793133675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122406767830455710896712933 22951268968210445793133675)
    ·
      refine ⟨34426903452315668689700513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22951268968210445793133675 34426903452315668689700513)
      ·
        refine ⟨25820177589236751517275385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34426903452315668689700513 25820177589236751517275385)
        ·
          refine ⟨19365133191927563637956539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25820177589236751517275385 19365133191927563637956539)
          ·
            refine ⟨29047699787891345456934809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19365133191927563637956539 29047699787891345456934809)
            ·
              refine ⟨21785774840918509092701107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29047699787891345456934809 21785774840918509092701107)
              ·
                refine ⟨32678662261377763639051661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21785774840918509092701107 32678662261377763639051661)
                ·
                  refine ⟨12254498348016661364644373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32678662261377763639051661 12254498348016661364644373)
                  ·
                    refine ⟨574429610063281001467705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12254498348016661364644373 574429610063281001467705)
                    ·
                      rfl

theorem cell23_3356093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_3356093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356093 prefixEnd_3356093 := by exact prefixLift 3356093
  have htrace : WordTrace (prefixWord ++ tailWord_3356093) baseStart_3356093 baseEnd_3356093 := by
    simpa [prefixWord, tailWord_3356093, baseEnd_3356093] using wordTrace_append hprefix tailTrace_3356093
  have hstable : (prefixWord ++ tailWord_3356093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356093).length < 2 ^ (prefixWord ++ tailWord_3356093).sum := by decide
  have hdescent : baseEnd_3356093 < baseStart_3356093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356098 : List Nat := [3, 5, 2, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3356098 : Nat := 118140960795 + 3356098 * 2 ^ 59
def prefixEnd_3356098 : Nat := 4983230072969 + 3 ^ 40 * 3356098 * 2
def baseEnd_3356098 : Nat := 1723291397593115484840593

theorem tailTrace_3356098 : CollatzResearch.WordTrace tailWord_3356098 prefixEnd_3356098 1723291397593115484840593 := by
  unfold tailWord_3356098
  simp only [CollatzResearch.WordTrace]
  refine ⟨30601737548859399187661237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81604633463625064500429965 30601737548859399187661237)
  ·
    refine ⟨2868912895205568673843241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30601737548859399187661237 2868912895205568673843241)
    ·
      refine ⟨2151684671404176505382431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2868912895205568673843241 2151684671404176505382431)
      ·
        refine ⟨3227527007106264758073647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151684671404176505382431 3227527007106264758073647)
        ·
          refine ⟨4841290510659397137110471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227527007106264758073647 4841290510659397137110471)
          ·
            refine ⟨7261935765989095705665707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841290510659397137110471 7261935765989095705665707)
            ·
              refine ⟨10892903648983643558498561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7261935765989095705665707 10892903648983643558498561)
              ·
                refine ⟨8169677736737732668873921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10892903648983643558498561 8169677736737732668873921)
                ·
                  refine ⟨6127258302553299501655441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8169677736737732668873921 6127258302553299501655441)
                  ·
                    refine ⟨4595443726914974626241581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6127258302553299501655441 4595443726914974626241581)
                    ·
                      refine ⟨1723291397593115484840593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4595443726914974626241581 1723291397593115484840593)
                      ·
                        rfl

theorem cell23_3356098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3356098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356098 prefixEnd_3356098 := by exact prefixLift 3356098
  have htrace : WordTrace (prefixWord ++ tailWord_3356098) baseStart_3356098 baseEnd_3356098 := by
    simpa [prefixWord, tailWord_3356098, baseEnd_3356098] using wordTrace_append hprefix tailTrace_3356098
  have hstable : (prefixWord ++ tailWord_3356098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356098).length < 2 ^ (prefixWord ++ tailWord_3356098).sum := by decide
  have hdescent : baseEnd_3356098 < baseStart_3356098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356110 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3356110 : Nat := 118140960795 + 3356110 * 2 ^ 59
def prefixEnd_3356110 : Nat := 4983230072969 + 3 ^ 40 * 3356110 * 2
def baseEnd_3356110 : Nat := 574432519786989812630179

theorem tailTrace_3356110 : CollatzResearch.WordTrace tailWord_3356110 prefixEnd_3356110 574432519786989812630179 := by
  unfold tailWord_3356110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15300923483924265350010223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81604925247596081866721189 15300923483924265350010223)
  ·
    refine ⟨22951385225886398025015335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15300923483924265350010223 22951385225886398025015335)
    ·
      refine ⟨34427077838829597037523003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22951385225886398025015335 34427077838829597037523003)
      ·
        refine ⟨51640616758244395556284505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34427077838829597037523003 51640616758244395556284505)
        ·
          refine ⟨38730462568683296667213379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51640616758244395556284505 38730462568683296667213379)
          ·
            refine ⟨58095693853024945000820069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38730462568683296667213379 58095693853024945000820069)
            ·
              refine ⟨10892942597442177187653763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58095693853024945000820069 10892942597442177187653763)
              ·
                refine ⟨16339413896163265781480645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10892942597442177187653763 16339413896163265781480645)
                ·
                  refine ⟨3063640105530612334027621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16339413896163265781480645 3063640105530612334027621)
                  ·
                    refine ⟨574432519786989812630179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063640105530612334027621 574432519786989812630179)
                    ·
                      rfl

theorem cell23_3356110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3356110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356110 prefixEnd_3356110 := by exact prefixLift 3356110
  have htrace : WordTrace (prefixWord ++ tailWord_3356110) baseStart_3356110 baseEnd_3356110 := by
    simpa [prefixWord, tailWord_3356110, baseEnd_3356110] using wordTrace_append hprefix tailTrace_3356110
  have hstable : (prefixWord ++ tailWord_3356110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356110).length < 2 ^ (prefixWord ++ tailWord_3356110).sum := by decide
  have hdescent : baseEnd_3356110 < baseStart_3356110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356211 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 1, 3, 2]
def baseStart_3356211 : Nat := 118140960795 + 3356211 * 2 ^ 59
def prefixEnd_3356211 : Nat := 4983230072969 + 3 ^ 40 * 3356211 * 2
def baseEnd_3356211 : Nat := 1723349420907073542727573

theorem tailTrace_3356211 : CollatzResearch.WordTrace tailWord_3356211 prefixEnd_3356211 1723349420907073542727573 := by
  unfold tailWord_3356211
  simp only [CollatzResearch.WordTrace]
  refine ⟨122411071644028217049508487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81607381096018811366338991 122411071644028217049508487)
  ·
    refine ⟨183616607466042325574262731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122411071644028217049508487 183616607466042325574262731)
    ·
      refine ⟨275424911199063488361394097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183616607466042325574262731 275424911199063488361394097)
      ·
        refine ⟨206568683399297616271045573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275424911199063488361394097 206568683399297616271045573)
        ·
          refine ⟨38731628137368303050821045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206568683399297616271045573 38731628137368303050821045)
          ·
            refine ⟨3631090137878278411014473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38731628137368303050821045 3631090137878278411014473)
            ·
              refine ⟨2723317603408708808260855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631090137878278411014473 2723317603408708808260855)
              ·
                refine ⟨4084976405113063212391283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723317603408708808260855 4084976405113063212391283)
                ·
                  refine ⟨6127464607669594818586925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4084976405113063212391283 6127464607669594818586925)
                  ·
                    refine ⟨2297799227876098056970097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6127464607669594818586925 2297799227876098056970097)
                    ·
                      refine ⟨1723349420907073542727573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297799227876098056970097 1723349420907073542727573)
                      ·
                        rfl

theorem cell23_3356211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 1, 3, 2].length) (baseStart_3356211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356211 prefixEnd_3356211 := by exact prefixLift 3356211
  have htrace : WordTrace (prefixWord ++ tailWord_3356211) baseStart_3356211 baseEnd_3356211 := by
    simpa [prefixWord, tailWord_3356211, baseEnd_3356211] using wordTrace_append hprefix tailTrace_3356211
  have hstable : (prefixWord ++ tailWord_3356211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356211).length < 2 ^ (prefixWord ++ tailWord_3356211).sum := by decide
  have hdescent : baseEnd_3356211 < baseStart_3356211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356240 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_3356240 : Nat := 118140960795 + 3356240 * 2 ^ 59
def prefixEnd_3356240 : Nat := 4983230072969 + 3 ^ 40 * 3356240 * 2
def baseEnd_3356240 : Nat := 1723364311846053929264939

theorem tailTrace_3356240 : CollatzResearch.WordTrace tailWord_3356240 prefixEnd_3356240 1723364311846053929264939 := by
  unfold tailWord_3356240
  simp only [CollatzResearch.WordTrace]
  refine ⟨61206064680461577501157087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81608086240615436668209449 61206064680461577501157087)
  ·
    refine ⟨91809097020692366251735631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61206064680461577501157087 91809097020692366251735631)
    ·
      refine ⟨137713645531038549377603447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91809097020692366251735631 137713645531038549377603447)
      ·
        refine ⟨206570468296557824066405171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137713645531038549377603447 206570468296557824066405171)
        ·
          refine ⟨309855702444836736099607757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206570468296557824066405171 309855702444836736099607757)
          ·
            refine ⟨116195888416813776037352909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309855702444836736099607757 116195888416813776037352909)
            ·
              refine ⟨43573458156305166014007341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116195888416813776037352909 43573458156305166014007341)
              ·
                refine ⟨16340046808614437255252753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43573458156305166014007341 16340046808614437255252753)
                ·
                  refine ⟨12255035106460827941439565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16340046808614437255252753 12255035106460827941439565)
                  ·
                    refine ⟨4595638164922810478039837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12255035106460827941439565 4595638164922810478039837)
                    ·
                      refine ⟨1723364311846053929264939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4595638164922810478039837 1723364311846053929264939)
                      ·
                        rfl

theorem cell23_3356240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_3356240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356240 prefixEnd_3356240 := by exact prefixLift 3356240
  have htrace : WordTrace (prefixWord ++ tailWord_3356240) baseStart_3356240 baseEnd_3356240 := by
    simpa [prefixWord, tailWord_3356240, baseEnd_3356240] using wordTrace_append hprefix tailTrace_3356240
  have hstable : (prefixWord ++ tailWord_3356240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356240).length < 2 ^ (prefixWord ++ tailWord_3356240).sum := by decide
  have hdescent : baseEnd_3356240 < baseStart_3356240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356241 : List Nat := [1, 2, 2, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_3356241 : Nat := 118140960795 + 3356241 * 2 ^ 59
def prefixEnd_3356241 : Nat := 4983230072969 + 3 ^ 40 * 3356241 * 2
def baseEnd_3356241 : Nat := 1723364825326708425352435

theorem tailTrace_3356241 : CollatzResearch.WordTrace tailWord_3356241 prefixEnd_3356241 1723364825326708425352435 := by
  unfold tailWord_3356241
  simp only [CollatzResearch.WordTrace]
  refine ⟨122412165833919532173100577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81608110555946354782067051 122412165833919532173100577)
  ·
    refine ⟨91809124375439649129825433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122412165833919532173100577 91809124375439649129825433)
    ·
      refine ⟨68856843281579736847369075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91809124375439649129825433 68856843281579736847369075)
      ·
        refine ⟨103285264922369605271053613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68856843281579736847369075 103285264922369605271053613)
        ·
          refine ⟨38731974345888601976645105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103285264922369605271053613 38731974345888601976645105)
          ·
            refine ⟨29048980759416451482483829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38731974345888601976645105 29048980759416451482483829)
            ·
              refine ⟨2723341946195292326482859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29048980759416451482483829 2723341946195292326482859)
              ·
                refine ⟨4085012919292938489724289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723341946195292326482859 4085012919292938489724289)
                ·
                  refine ⟨3063759689469703867293217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085012919292938489724289 3063759689469703867293217)
                  ·
                    refine ⟨2297819767102277900469913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3063759689469703867293217 2297819767102277900469913)
                    ·
                      refine ⟨1723364825326708425352435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297819767102277900469913 1723364825326708425352435)
                      ·
                        rfl

theorem cell23_3356241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_3356241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356241 prefixEnd_3356241 := by exact prefixLift 3356241
  have htrace : WordTrace (prefixWord ++ tailWord_3356241) baseStart_3356241 baseEnd_3356241 := by
    simpa [prefixWord, tailWord_3356241, baseEnd_3356241] using wordTrace_append hprefix tailTrace_3356241
  have hstable : (prefixWord ++ tailWord_3356241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356241).length < 2 ^ (prefixWord ++ tailWord_3356241).sum := by decide
  have hdescent : baseEnd_3356241 < baseStart_3356241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356260 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_3356260 : Nat := 118140960795 + 3356260 * 2 ^ 59
def prefixEnd_3356260 : Nat := 4983230072969 + 3 ^ 40 * 3356260 * 2
def baseEnd_3356260 : Nat := 574458193819714617004949

theorem tailTrace_3356260 : CollatzResearch.WordTrace tailWord_3356260 prefixEnd_3356260 574458193819714617004949 := by
  unfold tailWord_3356260
  simp only [CollatzResearch.WordTrace]
  refine ⟨61206429410425349209021117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81608572547233798945361489 61206429410425349209021117)
  ·
    refine ⟨22952411028909505953382919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61206429410425349209021117 22952411028909505953382919)
    ·
      refine ⟨34428616543364258930074379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22952411028909505953382919 34428616543364258930074379)
      ·
        refine ⟨51642924815046388395111569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34428616543364258930074379 51642924815046388395111569)
        ·
          refine ⟨38732193611284791296333677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51642924815046388395111569 38732193611284791296333677)
          ·
            refine ⟨14524572604231796736125129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38732193611284791296333677 14524572604231796736125129)
            ·
              refine ⟨10893429453173847552093847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14524572604231796736125129 10893429453173847552093847)
              ·
                refine ⟨16340144179760771328140771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10893429453173847552093847 16340144179760771328140771)
                ·
                  refine ⟨24510216269641156992211157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16340144179760771328140771 24510216269641156992211157)
                  ·
                    refine ⟨574458193819714617004949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24510216269641156992211157 574458193819714617004949)
                    ·
                      rfl

theorem cell23_3356260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_3356260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356260 prefixEnd_3356260 := by exact prefixLift 3356260
  have htrace : WordTrace (prefixWord ++ tailWord_3356260) baseStart_3356260 baseEnd_3356260 := by
    simpa [prefixWord, tailWord_3356260, baseEnd_3356260] using wordTrace_append hprefix tailTrace_3356260
  have hstable : (prefixWord ++ tailWord_3356260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356260).length < 2 ^ (prefixWord ++ tailWord_3356260).sum := by decide
  have hdescent : baseEnd_3356260 < baseStart_3356260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356264 : List Nat := [2, 1, 4, 3, 1, 1, 3, 3, 5]
def baseStart_3356264 : Nat := 118140960795 + 3356264 * 2 ^ 59
def prefixEnd_3356264 : Nat := 4983230072969 + 3 ^ 40 * 3356264 * 2
def baseEnd_3356264 : Nat := 191486292820195759484981

theorem tailTrace_3356264 : CollatzResearch.WordTrace tailWord_3356264 prefixEnd_3356264 191486292820195759484981 := by
  unfold tailWord_3356264
  simp only [CollatzResearch.WordTrace]
  refine ⟨61206502356418103550593923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81608669808557471400791897 61206502356418103550593923)
  ·
    refine ⟨91809753534627155325890885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61206502356418103550593923 91809753534627155325890885)
    ·
      refine ⟨17214328787742591623604541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91809753534627155325890885 17214328787742591623604541)
      ·
        refine ⟨6455373295403471858851703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17214328787742591623604541 6455373295403471858851703)
        ·
          refine ⟨9683059943105207788277555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455373295403471858851703 9683059943105207788277555)
          ·
            refine ⟨14524589914657811682416333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683059943105207788277555 14524589914657811682416333)
            ·
              refine ⟨5446721217996679380906125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14524589914657811682416333 5446721217996679380906125)
              ·
                refine ⟨2042520456748754767839797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5446721217996679380906125 2042520456748754767839797)
                ·
                  refine ⟨191486292820195759484981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2042520456748754767839797 191486292820195759484981)
                  ·
                    rfl

theorem cell23_3356264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 3, 5].length) (baseStart_3356264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356264 prefixEnd_3356264 := by exact prefixLift 3356264
  have htrace : WordTrace (prefixWord ++ tailWord_3356264) baseStart_3356264 baseEnd_3356264 := by
    simpa [prefixWord, tailWord_3356264, baseEnd_3356264] using wordTrace_append hprefix tailTrace_3356264
  have hstable : (prefixWord ++ tailWord_3356264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356264).length < 2 ^ (prefixWord ++ tailWord_3356264).sum := by decide
  have hdescent : baseEnd_3356264 < baseStart_3356264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356277 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_3356277 : Nat := 118140960795 + 3356277 * 2 ^ 59
def prefixEnd_3356277 : Nat := 4983230072969 + 3 ^ 40 * 3356277 * 2
def baseEnd_3356277 : Nat := 574461103543423428167423

theorem tailTrace_3356277 : CollatzResearch.WordTrace tailWord_3356277 prefixEnd_3356277 574461103543423428167423 := by
  unfold tailWord_3356277
  simp only [CollatzResearch.WordTrace]
  refine ⟨122413478861789110321411085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81608985907859406880940723 122413478861789110321411085)
  ·
    refine ⟨45905054573170916370529157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122413478861789110321411085 45905054573170916370529157)
    ·
      refine ⟨8607197732469546819474217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45905054573170916370529157 8607197732469546819474217)
      ·
        refine ⟨6455398299352160114605663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8607197732469546819474217 6455398299352160114605663)
        ·
          refine ⟨9683097449028240171908495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455398299352160114605663 9683097449028240171908495)
          ·
            refine ⟨14524646173542360257862743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9683097449028240171908495 14524646173542360257862743)
            ·
              refine ⟨21786969260313540386794115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14524646173542360257862743 21786969260313540386794115)
              ·
                refine ⟨32680453890470310580191173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21786969260313540386794115 32680453890470310580191173)
                ·
                  refine ⟨6127585104463183233785845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32680453890470310580191173 6127585104463183233785845)
                  ·
                    refine ⟨574461103543423428167423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6127585104463183233785845 574461103543423428167423)
                    ·
                      rfl

theorem cell23_3356277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_3356277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356277 prefixEnd_3356277 := by exact prefixLift 3356277
  have htrace : WordTrace (prefixWord ++ tailWord_3356277) baseStart_3356277 baseEnd_3356277 := by
    simpa [prefixWord, tailWord_3356277, baseEnd_3356277] using wordTrace_append hprefix tailTrace_3356277
  have hstable : (prefixWord ++ tailWord_3356277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356277).length < 2 ^ (prefixWord ++ tailWord_3356277).sum := by decide
  have hdescent : baseEnd_3356277 < baseStart_3356277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356297 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 2, 4, 2]
def baseStart_3356297 : Nat := 118140960795 + 3356297 * 2 ^ 59
def prefixEnd_3356297 : Nat := 4983230072969 + 3 ^ 40 * 3356297 * 2
def baseEnd_3356297 : Nat := 1723393580243360206252177

theorem tailTrace_3356297 : CollatzResearch.WordTrace tailWord_3356297 prefixEnd_3356297 1723393580243360206252177 := by
  unfold tailWord_3356297
  simp only [CollatzResearch.WordTrace]
  refine ⟨122414208321716653737139145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81609472214477769158092763 122414208321716653737139145)
  ·
    refine ⟨91810656241287490302854359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122414208321716653737139145 91810656241287490302854359)
    ·
      refine ⟨137715984361931235454281539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91810656241287490302854359 137715984361931235454281539)
      ·
        refine ⟨206573976542896853181422309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137715984361931235454281539 206573976542896853181422309)
        ·
          refine ⟨38732620601793159971516683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206573976542896853181422309 38732620601793159971516683)
          ·
            refine ⟨58098930902689739957275025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38732620601793159971516683 58098930902689739957275025)
            ·
              refine ⟨43574198177017304967956269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58098930902689739957275025 43574198177017304967956269)
              ·
                refine ⟨16340324316381489362983601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43574198177017304967956269 16340324316381489362983601)
                ·
                  refine ⟨12255243237286117022237701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16340324316381489362983601 12255243237286117022237701)
                  ·
                    refine ⟨2297858106991146941669569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12255243237286117022237701 2297858106991146941669569)
                    ·
                      refine ⟨1723393580243360206252177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297858106991146941669569 1723393580243360206252177)
                      ·
                        rfl

theorem cell23_3356297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 4, 2].length) (baseStart_3356297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356297 prefixEnd_3356297 := by exact prefixLift 3356297
  have htrace : WordTrace (prefixWord ++ tailWord_3356297) baseStart_3356297 baseEnd_3356297 := by
    simpa [prefixWord, tailWord_3356297, baseEnd_3356297] using wordTrace_append hprefix tailTrace_3356297
  have hstable : (prefixWord ++ tailWord_3356297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356297).length < 2 ^ (prefixWord ++ tailWord_3356297).sum := by decide
  have hdescent : baseEnd_3356297 < baseStart_3356297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356347 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 3]
def baseStart_3356347 : Nat := 118140960795 + 3356347 * 2 ^ 59
def prefixEnd_3356347 : Nat := 4983230072969 + 3 ^ 40 * 3356347 * 2
def baseEnd_3356347 : Nat := 1723419254276085010626947

theorem tailTrace_3356347 : CollatzResearch.WordTrace tailWord_3356347 prefixEnd_3356347 1723419254276085010626947 := by
  unfold tailWord_3356347
  simp only [CollatzResearch.WordTrace]
  refine ⟨122416031971535512276459295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81610687981023674850972863 122416031971535512276459295)
  ·
    refine ⟨183624047957303268414688943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122416031971535512276459295 183624047957303268414688943)
    ·
      refine ⟨275436071935954902622033415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183624047957303268414688943 275436071935954902622033415)
      ·
        refine ⟨413154107903932353933050123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275436071935954902622033415 413154107903932353933050123)
        ·
          refine ⟨619731161855898530899575185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413154107903932353933050123 619731161855898530899575185)
          ·
            refine ⟨464798371391923898174681389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619731161855898530899575185 464798371391923898174681389)
            ·
              refine ⟨174299389271971461815505521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464798371391923898174681389 174299389271971461815505521)
              ·
                refine ⟨130724541953978596361629141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174299389271971461815505521 130724541953978596361629141)
                ·
                  refine ⟨3063856452046373352225683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 130724541953978596361629141 3063856452046373352225683)
                  ·
                    refine ⟨4595784678069560028338525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3063856452046373352225683 4595784678069560028338525)
                    ·
                      refine ⟨1723419254276085010626947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4595784678069560028338525 1723419254276085010626947)
                      ·
                        rfl

theorem cell23_3356347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 7, 1, 3].length) (baseStart_3356347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356347 prefixEnd_3356347 := by exact prefixLift 3356347
  have htrace : WordTrace (prefixWord ++ tailWord_3356347) baseStart_3356347 baseEnd_3356347 := by
    simpa [prefixWord, tailWord_3356347, baseEnd_3356347] using wordTrace_append hprefix tailTrace_3356347
  have hstable : (prefixWord ++ tailWord_3356347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356347).length < 2 ^ (prefixWord ++ tailWord_3356347).sum := by decide
  have hdescent : baseEnd_3356347 < baseStart_3356347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356357 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_3356357 : Nat := 118140960795 + 3356357 * 2 ^ 59
def prefixEnd_3356357 : Nat := 4983230072969 + 3 ^ 40 * 3356357 * 2
def baseEnd_3356357 : Nat := 1723424389082629971501901

theorem tailTrace_3356357 : CollatzResearch.WordTrace tailWord_3356357 prefixEnd_3356357 1723424389082629971501901 := by
  unfold tailWord_3356357
  simp only [CollatzResearch.WordTrace]
  refine ⟨122416396701499283984323325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81610931134332855989548883 122416396701499283984323325)
  ·
    refine ⟨45906148763062231494121247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122416396701499283984323325 45906148763062231494121247)
    ·
      refine ⟨68859223144593347241181871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45906148763062231494121247 68859223144593347241181871)
      ·
        refine ⟨103288834716890020861772807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68859223144593347241181871 103288834716890020861772807)
        ·
          refine ⟨154933252075335031292659211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103288834716890020861772807 154933252075335031292659211)
          ·
            refine ⟨232399878113002546938988817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154933252075335031292659211 232399878113002546938988817)
            ·
              refine ⟨174299908584751910204241613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232399878113002546938988817 174299908584751910204241613)
              ·
                refine ⟨65362465719281966326590605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174299908584751910204241613 65362465719281966326590605)
                ·
                  refine ⟨24510924644730737372471477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65362465719281966326590605 24510924644730737372471477)
                  ·
                    refine ⟨2297899185443506628669201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24510924644730737372471477 2297899185443506628669201)
                    ·
                      refine ⟨1723424389082629971501901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2297899185443506628669201 1723424389082629971501901)
                      ·
                        rfl

theorem cell23_3356357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_3356357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356357 prefixEnd_3356357 := by exact prefixLift 3356357
  have htrace : WordTrace (prefixWord ++ tailWord_3356357) baseStart_3356357 baseEnd_3356357 := by
    simpa [prefixWord, tailWord_3356357, baseEnd_3356357] using wordTrace_append hprefix tailTrace_3356357
  have hstable : (prefixWord ++ tailWord_3356357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356357).length < 2 ^ (prefixWord ++ tailWord_3356357).sum := by decide
  have hdescent : baseEnd_3356357 < baseStart_3356357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356358 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3356358 : Nat := 118140960795 + 3356358 * 2 ^ 59
def prefixEnd_3356358 : Nat := 4983230072969 + 3 ^ 40 * 3356358 * 2
def baseEnd_3356358 : Nat := 574474967521094822529799

theorem tailTrace_3356358 : CollatzResearch.WordTrace tailWord_3356358 prefixEnd_3356358 574474967521094822529799 := by
  unfold tailWord_3356358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825513536702989411097179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81610955449663774103406485 3825513536702989411097179)
  ·
    refine ⟨5738270305054484116645769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3825513536702989411097179 5738270305054484116645769)
    ·
      refine ⟨4303702728790863087484327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5738270305054484116645769 4303702728790863087484327)
      ·
        refine ⟨6455554093186294631226491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303702728790863087484327 6455554093186294631226491)
        ·
          refine ⟨9683331139779441946839737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455554093186294631226491 9683331139779441946839737)
          ·
            refine ⟨7262498354834581460129803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9683331139779441946839737 7262498354834581460129803)
            ·
              refine ⟨10893747532251872190194705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7262498354834581460129803 10893747532251872190194705)
              ·
                refine ⟨8170310649188904142646029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10893747532251872190194705 8170310649188904142646029)
                ·
                  refine ⟨3063866493445839053492261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8170310649188904142646029 3063866493445839053492261)
                  ·
                    refine ⟨574474967521094822529799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3063866493445839053492261 574474967521094822529799)
                    ·
                      rfl

theorem cell23_3356358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3356358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356358 prefixEnd_3356358 := by exact prefixLift 3356358
  have htrace : WordTrace (prefixWord ++ tailWord_3356358) baseStart_3356358 baseEnd_3356358 := by
    simpa [prefixWord, tailWord_3356358, baseEnd_3356358] using wordTrace_append hprefix tailTrace_3356358
  have hstable : (prefixWord ++ tailWord_3356358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356358).length < 2 ^ (prefixWord ++ tailWord_3356358).sum := by decide
  have hdescent : baseEnd_3356358 < baseStart_3356358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356360 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_3356360 : Nat := 118140960795 + 3356360 * 2 ^ 59
def prefixEnd_3356360 : Nat := 4983230072969 + 3 ^ 40 * 3356360 * 2
def baseEnd_3356360 : Nat := 1723425929524593459764387

theorem tailTrace_3356360 : CollatzResearch.WordTrace tailWord_3356360 prefixEnd_3356360 1723425929524593459764387 := by
  unfold tailWord_3356360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61208253060244207748341267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81611004080325610331121689 61208253060244207748341267)
  ·
    refine ⟨91812379590366311622511901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61208253060244207748341267 91812379590366311622511901)
    ·
      refine ⟨34429642346387366858441963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91812379590366311622511901 34429642346387366858441963)
      ·
        refine ⟨51644463519581050287662945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34429642346387366858441963 51644463519581050287662945)
        ·
          refine ⟨38733347639685787715747209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51644463519581050287662945 38733347639685787715747209)
          ·
            refine ⟨29050010729764340786810407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38733347639685787715747209 29050010729764340786810407)
            ·
              refine ⟨43575016094646511180215611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29050010729764340786810407 43575016094646511180215611)
              ·
                refine ⟨65362524141969766770323417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43575016094646511180215611 65362524141969766770323417)
                ·
                  refine ⟨49021893106477325077742563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65362524141969766770323417 49021893106477325077742563)
                  ·
                    refine ⟨73532839659715987616613845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49021893106477325077742563 73532839659715987616613845)
                    ·
                      refine ⟨1723425929524593459764387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73532839659715987616613845 1723425929524593459764387)
                      ·
                        rfl

theorem cell23_3356360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_3356360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356360 prefixEnd_3356360 := by exact prefixLift 3356360
  have htrace : WordTrace (prefixWord ++ tailWord_3356360) baseStart_3356360 baseEnd_3356360 := by
    simpa [prefixWord, tailWord_3356360, baseEnd_3356360] using wordTrace_append hprefix tailTrace_3356360
  have hstable : (prefixWord ++ tailWord_3356360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356360).length < 2 ^ (prefixWord ++ tailWord_3356360).sum := by decide
  have hdescent : baseEnd_3356360 < baseStart_3356360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356384 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 1, 5]
def baseStart_3356384 : Nat := 118140960795 + 3356384 * 2 ^ 59
def prefixEnd_3356384 : Nat := 4983230072969 + 3 ^ 40 * 3356384 * 2
def baseEnd_3356384 : Nat := 574479417686767121954759

theorem tailTrace_3356384 : CollatzResearch.WordTrace tailWord_3356384 prefixEnd_3356384 574479417686767121954759 := by
  unfold tailWord_3356384
  simp only [CollatzResearch.WordTrace]
  refine ⟨61208690736200733797778103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81611587648267645063704137 61208690736200733797778103)
  ·
    refine ⟨91813036104301100696667155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61208690736200733797778103 91813036104301100696667155)
    ·
      refine ⟨137719554156451651045000733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91813036104301100696667155 137719554156451651045000733)
      ·
        refine ⟨51644832808669369141875275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137719554156451651045000733 51644832808669369141875275)
        ·
          refine ⟨77467249213004053712812913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51644832808669369141875275 77467249213004053712812913)
          ·
            refine ⟨58100436909753040284609685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77467249213004053712812913 58100436909753040284609685)
            ·
              refine ⟨2723457980144673763341079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58100436909753040284609685 2723457980144673763341079)
              ·
                refine ⟨4085186970217010645011619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723457980144673763341079 4085186970217010645011619)
                ·
                  refine ⟨6127780455325515967517429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085186970217010645011619 6127780455325515967517429)
                  ·
                    refine ⟨574479417686767121954759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6127780455325515967517429 574479417686767121954759)
                    ·
                      rfl

theorem cell23_3356384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_3356384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356384 prefixEnd_3356384 := by exact prefixLift 3356384
  have htrace : WordTrace (prefixWord ++ tailWord_3356384) baseStart_3356384 baseEnd_3356384 := by
    simpa [prefixWord, tailWord_3356384, baseEnd_3356384] using wordTrace_append hprefix tailTrace_3356384
  have hstable : (prefixWord ++ tailWord_3356384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356384).length < 2 ^ (prefixWord ++ tailWord_3356384).sum := by decide
  have hdescent : baseEnd_3356384 < baseStart_3356384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356407 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3]
def baseStart_3356407 : Nat := 118140960795 + 3356407 * 2 ^ 59
def prefixEnd_3356407 : Nat := 4983230072969 + 3 ^ 40 * 3356407 * 2
def baseEnd_3356407 : Nat := 1723450063115354775876671

theorem tailTrace_3356407 : CollatzResearch.WordTrace tailWord_3356407 prefixEnd_3356407 1723450063115354775876671 := by
  unfold tailWord_3356407
  simp only [CollatzResearch.WordTrace]
  refine ⟨122418220351318142523643475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81612146900878761682428983 122418220351318142523643475)
  ·
    refine ⟨183627330526977213785465213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122418220351318142523643475 183627330526977213785465213)
    ·
      refine ⟨68860248947616455169549455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183627330526977213785465213 68860248947616455169549455)
      ·
        refine ⟨103290373421424682754324183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68860248947616455169549455 103290373421424682754324183)
        ·
          refine ⟨154935560132137024131486275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103290373421424682754324183 154935560132137024131486275)
          ·
            refine ⟨232403340198205536197229413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154935560132137024131486275 232403340198205536197229413)
            ·
              refine ⟨43575626287163538036980515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232403340198205536197229413 43575626287163538036980515)
              ·
                refine ⟨65363439430745307055470773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43575626287163538036980515 65363439430745307055470773)
                ·
                  refine ⟨6127822446632372536450385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65363439430745307055470773 6127822446632372536450385)
                  ·
                    refine ⟨4595866834974279402337789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6127822446632372536450385 4595866834974279402337789)
                    ·
                      refine ⟨1723450063115354775876671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4595866834974279402337789 1723450063115354775876671)
                      ·
                        rfl

theorem cell23_3356407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 3].length) (baseStart_3356407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356407 prefixEnd_3356407 := by exact prefixLift 3356407
  have htrace : WordTrace (prefixWord ++ tailWord_3356407) baseStart_3356407 baseEnd_3356407 := by
    simpa [prefixWord, tailWord_3356407, baseEnd_3356407] using wordTrace_append hprefix tailTrace_3356407
  have hstable : (prefixWord ++ tailWord_3356407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356407).length < 2 ^ (prefixWord ++ tailWord_3356407).sum := by decide
  have hdescent : baseEnd_3356407 < baseStart_3356407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356410 : List Nat := [3, 1, 1, 1, 1, 3, 1, 12]
def baseStart_3356410 : Nat := 118140960795 + 3356410 * 2 ^ 59
def prefixEnd_3356410 : Nat := 4983230072969 + 3 ^ 40 * 3356410 * 2
def baseEnd_3356410 : Nat := 63831540872493269042191

theorem tailTrace_3356410 : CollatzResearch.WordTrace tailWord_3356410 prefixEnd_3356410 63831540872493269042191 := by
  unfold tailWord_3356410
  simp only [CollatzResearch.WordTrace]
  refine ⟨30604582442576818509000671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81612219846871516024001789 30604582442576818509000671)
  ·
    refine ⟨45906873663865227763501007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30604582442576818509000671 45906873663865227763501007)
    ·
      refine ⟨68860310495797841645251511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45906873663865227763501007 68860310495797841645251511)
      ·
        refine ⟨103290465743696762467877267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68860310495797841645251511 103290465743696762467877267)
        ·
          refine ⟨154935698615545143701815901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103290465743696762467877267 154935698615545143701815901)
          ·
            refine ⟨58100886980829428888180963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154935698615545143701815901 58100886980829428888180963)
            ·
              refine ⟨87151330471244143332271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58100886980829428888180963 87151330471244143332271445)
              ·
                refine ⟨63831540872493269042191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 87151330471244143332271445 63831540872493269042191)
                ·
                  rfl

theorem cell23_3356410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 12].length) (baseStart_3356410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356410 prefixEnd_3356410 := by exact prefixLift 3356410
  have htrace : WordTrace (prefixWord ++ tailWord_3356410) baseStart_3356410 baseEnd_3356410 := by
    simpa [prefixWord, tailWord_3356410, baseEnd_3356410] using wordTrace_append hprefix tailTrace_3356410
  have hstable : (prefixWord ++ tailWord_3356410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356410).length < 2 ^ (prefixWord ++ tailWord_3356410).sum := by decide
  have hdescent : baseEnd_3356410 < baseStart_3356410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356427 : List Nat := [1, 1, 1, 1, 5, 1, 6, 7]
def baseStart_3356427 : Nat := 118140960795 + 3356427 * 2 ^ 59
def prefixEnd_3356427 : Nat := 4983230072969 + 3 ^ 40 * 3356427 * 2
def baseEnd_3356427 : Nat := 63831864175127581393577

theorem tailTrace_3356427 : CollatzResearch.WordTrace tailWord_3356427 prefixEnd_3356427 63831864175127581393577 := by
  unfold tailWord_3356427
  simp only [CollatzResearch.WordTrace]
  refine ⟨122418949811245685939371535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81612633207497123959581023 122418949811245685939371535)
  ·
    refine ⟨183628424716868528909057303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122418949811245685939371535 183628424716868528909057303)
    ·
      refine ⟨275442637075302793363585955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183628424716868528909057303 275442637075302793363585955)
      ·
        refine ⟨413163955612954190045378933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275442637075302793363585955 413163955612954190045378933)
        ·
          refine ⟨38734120838714455316754275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 413163955612954190045378933 38734120838714455316754275)
          ·
            refine ⟨58101181258071682975131413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38734120838714455316754275 58101181258071682975131413)
            ·
              refine ⟨2723492871472110139459285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58101181258071682975131413 2723492871472110139459285)
              ·
                refine ⟨63831864175127581393577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2723492871472110139459285 63831864175127581393577)
                ·
                  rfl

theorem cell23_3356427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 7].length) (baseStart_3356427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356427 prefixEnd_3356427 := by exact prefixLift 3356427
  have htrace : WordTrace (prefixWord ++ tailWord_3356427) baseStart_3356427 baseEnd_3356427 := by
    simpa [prefixWord, tailWord_3356427, baseEnd_3356427] using wordTrace_append hprefix tailTrace_3356427
  have hstable : (prefixWord ++ tailWord_3356427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356427).length < 2 ^ (prefixWord ++ tailWord_3356427).sum := by decide
  have hdescent : baseEnd_3356427 < baseStart_3356427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356517 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 7]
def baseStart_3356517 : Nat := 118140960795 + 3356517 * 2 ^ 59
def prefixEnd_3356517 : Nat := 4983230072969 + 3 ^ 40 * 3356517 * 2
def baseEnd_3356517 : Nat := 191500727331927705055685

theorem tailTrace_3356517 : CollatzResearch.WordTrace tailWord_3356517 prefixEnd_3356517 191500727331927705055685 := by
  unfold tailWord_3356517
  simp only [CollatzResearch.WordTrace]
  refine ⟨122422232380919631310147805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81614821587279754206765203 122422232380919631310147805)
  ·
    refine ⟨45908337142844861741305427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122422232380919631310147805 45908337142844861741305427)
    ·
      refine ⟨68862505714267292611958141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45908337142844861741305427 68862505714267292611958141)
      ·
        refine ⟨25823439642850234729484303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68862505714267292611958141 25823439642850234729484303)
        ·
          refine ⟨38735159464275352094226455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25823439642850234729484303 38735159464275352094226455)
          ·
            refine ⟨58102739196413028141339683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38735159464275352094226455 58102739196413028141339683)
            ·
              refine ⟨87154108794619542212009525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58102739196413028141339683 87154108794619542212009525)
              ·
                refine ⟨8170697699495582082375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87154108794619542212009525 8170697699495582082375893)
                ·
                  refine ⟨191500727331927705055685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8170697699495582082375893 191500727331927705055685)
                  ·
                    rfl

theorem cell23_3356517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_3356517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356517 prefixEnd_3356517 := by exact prefixLift 3356517
  have htrace : WordTrace (prefixWord ++ tailWord_3356517) baseStart_3356517 baseEnd_3356517 := by
    simpa [prefixWord, tailWord_3356517, baseEnd_3356517] using wordTrace_append hprefix tailTrace_3356517
  have hstable : (prefixWord ++ tailWord_3356517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356517).length < 2 ^ (prefixWord ++ tailWord_3356517).sum := by decide
  have hdescent : baseEnd_3356517 < baseStart_3356517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356524 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 4]
def baseStart_3356524 : Nat := 118140960795 + 3356524 * 2 ^ 59
def prefixEnd_3356524 : Nat := 4983230072969 + 3 ^ 40 * 3356524 * 2
def baseEnd_3356524 : Nat := 1723510140351930818113633

theorem tailTrace_3356524 : CollatzResearch.WordTrace tailWord_3356524 prefixEnd_3356524 1723510140351930818113633 := by
  unfold tailWord_3356524
  simp only [CollatzResearch.WordTrace]
  refine ⟨61211243845947135752826313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81614991794596181003768417 61211243845947135752826313)
  ·
    refine ⟨45908432884460351814619735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61211243845947135752826313 45908432884460351814619735)
    ·
      refine ⟨68862649326690527721929603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45908432884460351814619735 68862649326690527721929603)
      ·
        refine ⟨103293973990035791582894405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68862649326690527721929603 103293973990035791582894405)
        ·
          refine ⟨19367620123131710921792701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103293973990035791582894405 19367620123131710921792701)
          ·
            refine ⟨7262857546174391595672263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19367620123131710921792701 7262857546174391595672263)
            ·
              refine ⟨10894286319261587393508395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7262857546174391595672263 10894286319261587393508395)
              ·
                refine ⟨16341429478892381090262593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10894286319261587393508395 16341429478892381090262593)
                ·
                  refine ⟨12256072109169285817696945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16341429478892381090262593 12256072109169285817696945)
                  ·
                    refine ⟨9192054081876964363272709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12256072109169285817696945 9192054081876964363272709)
                    ·
                      refine ⟨1723510140351930818113633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9192054081876964363272709 1723510140351930818113633)
                      ·
                        rfl

theorem cell23_3356524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_3356524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356524 prefixEnd_3356524 := by exact prefixLift 3356524
  have htrace : WordTrace (prefixWord ++ tailWord_3356524) baseStart_3356524 baseEnd_3356524 := by
    simpa [prefixWord, tailWord_3356524, baseEnd_3356524] using wordTrace_append hprefix tailTrace_3356524
  have hstable : (prefixWord ++ tailWord_3356524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356524).length < 2 ^ (prefixWord ++ tailWord_3356524).sum := by decide
  have hdescent : baseEnd_3356524 < baseStart_3356524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356562 : List Nat := [3, 2, 3, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_3356562 : Nat := 118140960795 + 3356562 * 2 ^ 59
def prefixEnd_3356562 : Nat := 4983230072969 + 3 ^ 40 * 3356562 * 2
def baseEnd_3356562 : Nat := 1723529652616801669438459

theorem tailTrace_3356562 : CollatzResearch.WordTrace tailWord_3356562 prefixEnd_3356562 1723529652616801669438459 := by
  unfold tailWord_3356562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30605968416439150998883985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81615915777171069330357293 30605968416439150998883985)
  ·
    refine ⟨22954476312329363249162989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30605968416439150998883985 22954476312329363249162989)
    ·
      refine ⟨8607928617123511218436121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22954476312329363249162989 8607928617123511218436121)
      ·
        refine ⟨6455946462842633413827091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8607928617123511218436121 6455946462842633413827091)
        ·
          refine ⟨9683919694263950120740637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6455946462842633413827091 9683919694263950120740637)
          ·
            refine ⟨3631469885348981295277739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9683919694263950120740637 3631469885348981295277739)
            ·
              refine ⟨5447204828023471942916609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3631469885348981295277739 5447204828023471942916609)
              ·
                refine ⟨4085403621017603957187457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447204828023471942916609 4085403621017603957187457)
                ·
                  refine ⟨3064052715763202967890593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085403621017603957187457 3064052715763202967890593)
                  ·
                    refine ⟨2298039536822402225917945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064052715763202967890593 2298039536822402225917945)
                    ·
                      refine ⟨1723529652616801669438459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298039536822402225917945 1723529652616801669438459)
                      ·
                        rfl

theorem cell23_3356562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_3356562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356562 prefixEnd_3356562 := by exact prefixLift 3356562
  have htrace : WordTrace (prefixWord ++ tailWord_3356562) baseStart_3356562 baseEnd_3356562 := by
    simpa [prefixWord, tailWord_3356562, baseEnd_3356562] using wordTrace_append hprefix tailTrace_3356562
  have hstable : (prefixWord ++ tailWord_3356562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356562).length < 2 ^ (prefixWord ++ tailWord_3356562).sum := by decide
  have hdescent : baseEnd_3356562 < baseStart_3356562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356607 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 10]
def baseStart_3356607 : Nat := 118140960795 + 3356607 * 2 ^ 59
def prefixEnd_3356607 : Nat := 4983230072969 + 3 ^ 40 * 3356607 * 2
def baseEnd_3356607 : Nat := 191505862138472665930639

theorem tailTrace_3356607 : CollatzResearch.WordTrace tailWord_3356607 prefixEnd_3356607 191505862138472665930639 := by
  unfold tailWord_3356607
  simp only [CollatzResearch.WordTrace]
  refine ⟨122425514950593576680924075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81617009967062384453949383 122425514950593576680924075)
  ·
    refine ⟨183638272425890365021386113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122425514950593576680924075 183638272425890365021386113)
    ·
      refine ⟨137728704319417773766039585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183638272425890365021386113 137728704319417773766039585)
      ·
        refine ⟨103296528239563330324529689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137728704319417773766039585 103296528239563330324529689)
        ·
          refine ⟨77472396179672497743397267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103296528239563330324529689 77472396179672497743397267)
          ·
            refine ⟨116208594269508746615095901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77472396179672497743397267 116208594269508746615095901)
            ·
              refine ⟨43578222851065779980660963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116208594269508746615095901 43578222851065779980660963)
              ·
                refine ⟨65367334276598669970991445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43578222851065779980660963 65367334276598669970991445)
                ·
                  refine ⟨191505862138472665930639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65367334276598669970991445 191505862138472665930639)
                  ·
                    rfl

theorem cell23_3356607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 10].length) (baseStart_3356607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356607 prefixEnd_3356607 := by exact prefixLift 3356607
  have htrace : WordTrace (prefixWord ++ tailWord_3356607) baseStart_3356607 baseEnd_3356607 := by
    simpa [prefixWord, tailWord_3356607, baseEnd_3356607] using wordTrace_append hprefix tailTrace_3356607
  have hstable : (prefixWord ++ tailWord_3356607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356607).length < 2 ^ (prefixWord ++ tailWord_3356607).sum := by decide
  have hdescent : baseEnd_3356607 < baseStart_3356607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356641 : List Nat := [1, 2, 3, 1, 2, 1, 6, 1, 6]
def baseStart_3356641 : Nat := 118140960795 + 3356641 * 2 ^ 59
def prefixEnd_3356641 : Nat := 4983230072969 + 3 ^ 40 * 3356641 * 2
def baseEnd_3356641 : Nat := 191507801954278540038955

theorem tailTrace_3356641 : CollatzResearch.WordTrace tailWord_3356641 prefixEnd_3356641 191507801954278540038955 := by
  unfold tailWord_3356641
  simp only [CollatzResearch.WordTrace]
  refine ⟨122426755032470400487661777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81617836688313600325107851 122426755032470400487661777)
  ·
    refine ⟨91820066274352800365746333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122426755032470400487661777 91820066274352800365746333)
    ·
      refine ⟨34432524852882300137154875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91820066274352800365746333 34432524852882300137154875)
      ·
        refine ⟨51648787279323450205732313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34432524852882300137154875 51648787279323450205732313)
        ·
          refine ⟨38736590459492587654299235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51648787279323450205732313 38736590459492587654299235)
          ·
            refine ⟨58104885689238881481448853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38736590459492587654299235 58104885689238881481448853)
            ·
              refine ⟨2723666516683072569442915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58104885689238881481448853 2723666516683072569442915)
              ·
                refine ⟨4085499775024608854164373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723666516683072569442915 4085499775024608854164373)
                ·
                  refine ⟨191507801954278540038955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4085499775024608854164373 191507801954278540038955)
                  ·
                    rfl

theorem cell23_3356641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 6, 1, 6].length) (baseStart_3356641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356641 prefixEnd_3356641 := by exact prefixLift 3356641
  have htrace : WordTrace (prefixWord ++ tailWord_3356641) baseStart_3356641 baseEnd_3356641 := by
    simpa [prefixWord, tailWord_3356641, baseEnd_3356641] using wordTrace_append hprefix tailTrace_3356641
  have hstable : (prefixWord ++ tailWord_3356641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356641).length < 2 ^ (prefixWord ++ tailWord_3356641).sum := by decide
  have hdescent : baseEnd_3356641 < baseStart_3356641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356651 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 3]
def baseStart_3356651 : Nat := 118140960795 + 3356651 * 2 ^ 59
def prefixEnd_3356651 : Nat := 4983230072969 + 3 ^ 40 * 3356651 * 2
def baseEnd_3356651 : Nat := 1723575352395051821225549

theorem tailTrace_3356651 : CollatzResearch.WordTrace tailWord_3356651 prefixEnd_3356651 1723575352395051821225549 := by
  unfold tailWord_3356651
  simp only [CollatzResearch.WordTrace]
  refine ⟨122427119762434172195525807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81618079841622781463683871 122427119762434172195525807)
  ·
    refine ⟨183640679643651258293288711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122427119762434172195525807 183640679643651258293288711)
    ·
      refine ⟨275461019465476887439933067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183640679643651258293288711 275461019465476887439933067)
      ·
        refine ⟨413191529198215331159899601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275461019465476887439933067 413191529198215331159899601)
        ·
          refine ⟨309893646898661498369924701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413191529198215331159899601 309893646898661498369924701)
          ·
            refine ⟨116210117586998061888721763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309893646898661498369924701 116210117586998061888721763)
            ·
              refine ⟨174315176380497092833082645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116210117586998061888721763 174315176380497092833082645)
              ·
                refine ⟨8171023892835801226550749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174315176380497092833082645 8171023892835801226550749)
                ·
                  refine ⟨3064133959813425459956531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8171023892835801226550749 3064133959813425459956531)
                  ·
                    refine ⟨4596200939720138189934797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3064133959813425459956531 4596200939720138189934797)
                    ·
                      refine ⟨1723575352395051821225549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4596200939720138189934797 1723575352395051821225549)
                      ·
                        rfl

theorem cell23_3356651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 3].length) (baseStart_3356651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356651 prefixEnd_3356651 := by exact prefixLift 3356651
  have htrace : WordTrace (prefixWord ++ tailWord_3356651) baseStart_3356651 baseEnd_3356651 := by
    simpa [prefixWord, tailWord_3356651, baseEnd_3356651] using wordTrace_append hprefix tailTrace_3356651
  have hstable : (prefixWord ++ tailWord_3356651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356651).length < 2 ^ (prefixWord ++ tailWord_3356651).sum := by decide
  have hdescent : baseEnd_3356651 < baseStart_3356651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356684 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_3356684 : Nat := 118140960795 + 3356684 * 2 ^ 59
def prefixEnd_3356684 : Nat := 4983230072969 + 3 ^ 40 * 3356684 * 2
def baseEnd_3356684 : Nat := 574530765752216730704299

theorem tailTrace_3356684 : CollatzResearch.WordTrace tailWord_3356684 prefixEnd_3356684 574530765752216730704299 := by
  unfold tailWord_3356684
  simp only [CollatzResearch.WordTrace]
  refine ⟨61214161685657309415738553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81618882247543079220984737 61214161685657309415738553)
  ·
    refine ⟨45910621264242982061803915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61214161685657309415738553 45910621264242982061803915)
    ·
      refine ⟨68865931896364473092705873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45910621264242982061803915 68865931896364473092705873)
      ·
        refine ⟨51649448922273354819529405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68865931896364473092705873 51649448922273354819529405)
        ·
          refine ⟨19368543345852508057323527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51649448922273354819529405 19368543345852508057323527)
          ·
            refine ⟨29052815018778762085985291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19368543345852508057323527 29052815018778762085985291)
            ·
              refine ⟨43579222528168143128977937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29052815018778762085985291 43579222528168143128977937)
              ·
                refine ⟨32684416896126107346733453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43579222528168143128977937 32684416896126107346733453)
                ·
                  refine ⟨12256656336047290255025045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32684416896126107346733453 12256656336047290255025045)
                  ·
                    refine ⟨574530765752216730704299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12256656336047290255025045 574530765752216730704299)
                    ·
                      rfl

theorem cell23_3356684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_3356684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356684 prefixEnd_3356684 := by exact prefixLift 3356684
  have htrace : WordTrace (prefixWord ++ tailWord_3356684) baseStart_3356684 baseEnd_3356684 := by
    simpa [prefixWord, tailWord_3356684, baseEnd_3356684] using wordTrace_append hprefix tailTrace_3356684
  have hstable : (prefixWord ++ tailWord_3356684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356684).length < 2 ^ (prefixWord ++ tailWord_3356684).sum := by decide
  have hdescent : baseEnd_3356684 < baseStart_3356684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356701 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_3356701 : Nat := 118140960795 + 3356701 * 2 ^ 59
def prefixEnd_3356701 : Nat := 4983230072969 + 3 ^ 40 * 3356701 * 2
def baseEnd_3356701 : Nat := 574533675475925541866773

theorem tailTrace_3356701 : CollatzResearch.WordTrace tailWord_3356701 prefixEnd_3356701 574533675475925541866773 := by
  unfold tailWord_3356701
  simp only [CollatzResearch.WordTrace]
  refine ⟨122428943412253030734845957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81619295608168687156563971 122428943412253030734845957)
  ·
    refine ⟨22955426889797443262783617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122428943412253030734845957 22955426889797443262783617)
    ·
      refine ⟨17216570167348082447087713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22955426889797443262783617 17216570167348082447087713)
      ·
        refine ⟨12912427625511061835315785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17216570167348082447087713 12912427625511061835315785)
        ·
          refine ⟨9684320719133296376486839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12912427625511061835315785 9684320719133296376486839)
          ·
            refine ⟨14526481078699944564730259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9684320719133296376486839 14526481078699944564730259)
            ·
              refine ⟨21789721618049916847095389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14526481078699944564730259 21789721618049916847095389)
              ·
                refine ⟨8171145606768718817660771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21789721618049916847095389 8171145606768718817660771)
                ·
                  refine ⟨12256718410153078226491157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8171145606768718817660771 12256718410153078226491157)
                  ·
                    refine ⟨574533675475925541866773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12256718410153078226491157 574533675475925541866773)
                    ·
                      rfl

theorem cell23_3356701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_3356701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356701 prefixEnd_3356701 := by exact prefixLift 3356701
  have htrace : WordTrace (prefixWord ++ tailWord_3356701) baseStart_3356701 baseEnd_3356701 := by
    simpa [prefixWord, tailWord_3356701, baseEnd_3356701] using wordTrace_append hprefix tailTrace_3356701
  have hstable : (prefixWord ++ tailWord_3356701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356701).length < 2 ^ (prefixWord ++ tailWord_3356701).sum := by decide
  have hdescent : baseEnd_3356701 < baseStart_3356701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356721 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3356721 : Nat := 118140960795 + 3356721 * 2 ^ 59
def prefixEnd_3356721 : Nat := 4983230072969 + 3 ^ 40 * 3356721 * 2
def baseEnd_3356721 : Nat := 1723611296040866547350227

theorem tailTrace_3356721 : CollatzResearch.WordTrace tailWord_3356721 prefixEnd_3356721 1723611296040866547350227 := by
  unfold tailWord_3356721
  simp only [CollatzResearch.WordTrace]
  refine ⟨122429672872180574150574017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81619781914787049433716011 122429672872180574150574017)
  ·
    refine ⟨91822254654135430612930513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122429672872180574150574017 91822254654135430612930513)
    ·
      refine ⟨68866690990601572959697885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91822254654135430612930513 68866690990601572959697885)
      ·
        refine ⟨25825009121475589859886707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68866690990601572959697885 25825009121475589859886707)
        ·
          refine ⟨38737513682213384789830061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25825009121475589859886707 38737513682213384789830061)
          ·
            refine ⟨14526567630830019296186273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38737513682213384789830061 14526567630830019296186273)
            ·
              refine ⟨10894925723122514472139705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14526567630830019296186273 10894925723122514472139705)
              ·
                refine ⟨8171194292341885854104779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10894925723122514472139705 8171194292341885854104779)
                ·
                  refine ⟨12256791438512828781157169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8171194292341885854104779 12256791438512828781157169)
                  ·
                    refine ⟨9192593578884621585867877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12256791438512828781157169 9192593578884621585867877)
                    ·
                      refine ⟨1723611296040866547350227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9192593578884621585867877 1723611296040866547350227)
                      ·
                        rfl

theorem cell23_3356721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3356721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356721 prefixEnd_3356721 := by exact prefixLift 3356721
  have htrace : WordTrace (prefixWord ++ tailWord_3356721) baseStart_3356721 baseEnd_3356721 := by
    simpa [prefixWord, tailWord_3356721, baseEnd_3356721] using wordTrace_append hprefix tailTrace_3356721
  have hstable : (prefixWord ++ tailWord_3356721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356721).length < 2 ^ (prefixWord ++ tailWord_3356721).sum := by decide
  have hdescent : baseEnd_3356721 < baseStart_3356721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356744 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_3356744 : Nat := 118140960795 + 3356744 * 2 ^ 59
def prefixEnd_3356744 : Nat := 4983230072969 + 3 ^ 40 * 3356744 * 2
def baseEnd_3356744 : Nat := 574541035365306652454207

theorem tailTrace_3356744 : CollatzResearch.WordTrace tailWord_3356744 prefixEnd_3356744 574541035365306652454207 := by
  unfold tailWord_3356744
  simp only [CollatzResearch.WordTrace]
  refine ⟨61215255875548624539330643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81620341167398166052440857 61215255875548624539330643)
  ·
    refine ⟨91822883813322936808995965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61215255875548624539330643 91822883813322936808995965)
    ·
      refine ⟨34433581429996101303373487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91822883813322936808995965 34433581429996101303373487)
      ·
        refine ⟨51650372144994151955060231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34433581429996101303373487 51650372144994151955060231)
        ·
          refine ⟨77475558217491227932590347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51650372144994151955060231 77475558217491227932590347)
          ·
            refine ⟨116213337326236841898885521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77475558217491227932590347 116213337326236841898885521)
            ·
              refine ⟨87160002994677631424164141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116213337326236841898885521 87160002994677631424164141)
              ·
                refine ⟨32685001123004111784061553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87160002994677631424164141 32685001123004111784061553)
                ·
                  refine ⟨24513750842253083838046165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32685001123004111784061553 24513750842253083838046165)
                  ·
                    refine ⟨574541035365306652454207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24513750842253083838046165 574541035365306652454207)
                    ·
                      rfl

theorem cell23_3356744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_3356744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356744 prefixEnd_3356744 := by exact prefixLift 3356744
  have htrace : WordTrace (prefixWord ++ tailWord_3356744) baseStart_3356744 baseEnd_3356744 := by
    simpa [prefixWord, tailWord_3356744, baseEnd_3356744] using wordTrace_append hprefix tailTrace_3356744
  have hstable : (prefixWord ++ tailWord_3356744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356744).length < 2 ^ (prefixWord ++ tailWord_3356744).sum := by decide
  have hdescent : baseEnd_3356744 < baseStart_3356744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356765 : List Nat := [1, 4, 4, 1, 1, 3, 2, 7]
def baseStart_3356765 : Nat := 118140960795 + 3356765 * 2 ^ 59
def prefixEnd_3356765 : Nat := 4983230072969 + 3 ^ 40 * 3356765 * 2
def baseEnd_3356765 : Nat := 63838292192209791674075

theorem tailTrace_3356765 : CollatzResearch.WordTrace tailWord_3356765 prefixEnd_3356765 63838292192209791674075 := by
  unfold tailWord_3356765
  simp only [CollatzResearch.WordTrace]
  refine ⟨122431277684021169665175749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81620851789347446443450499 122431277684021169665175749)
  ·
    refine ⟨22955864565753969312220453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122431277684021169665175749 22955864565753969312220453)
    ·
      refine ⟨4304224606078869246041335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22955864565753969312220453 4304224606078869246041335)
      ·
        refine ⟨6456336909118303869062003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304224606078869246041335 6456336909118303869062003)
        ·
          refine ⟨9684505363677455803593005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456336909118303869062003 9684505363677455803593005)
          ·
            refine ⟨3631689511379045926347377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9684505363677455803593005 3631689511379045926347377)
            ·
              refine ⟨2723767133534284444760533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631689511379045926347377 2723767133534284444760533)
              ·
                refine ⟨63838292192209791674075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2723767133534284444760533 63838292192209791674075)
                ·
                  rfl

theorem cell23_3356765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 7].length) (baseStart_3356765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356765 prefixEnd_3356765 := by exact prefixLift 3356765
  have htrace : WordTrace (prefixWord ++ tailWord_3356765) baseStart_3356765 baseEnd_3356765 := by
    simpa [prefixWord, tailWord_3356765, baseEnd_3356765] using wordTrace_append hprefix tailTrace_3356765
  have hstable : (prefixWord ++ tailWord_3356765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356765).length < 2 ^ (prefixWord ++ tailWord_3356765).sum := by decide
  have hdescent : baseEnd_3356765 < baseStart_3356765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356849 : List Nat := [1, 2, 2, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_3356849 : Nat := 118140960795 + 3356849 * 2 ^ 59
def prefixEnd_3356849 : Nat := 4983230072969 + 3 ^ 40 * 3356849 * 2
def baseEnd_3356849 : Nat := 1723677021564642046549639

theorem tailTrace_3356849 : CollatzResearch.WordTrace tailWord_3356849 prefixEnd_3356849 1723677021564642046549639 := by
  unfold tailWord_3356849
  simp only [CollatzResearch.WordTrace]
  refine ⟨122434341415716852011233601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81622894277144568007489067 122434341415716852011233601)
  ·
    refine ⟨91825756061787639008425201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122434341415716852011233601 91825756061787639008425201)
    ·
      refine ⟨68869317046340729256318901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91825756061787639008425201 68869317046340729256318901)
      ·
        refine ⟨6456498473094443367779897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68869317046340729256318901 6456498473094443367779897)
        ·
          refine ⟨4842373854820832525834923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6456498473094443367779897 4842373854820832525834923)
          ·
            refine ⟨7263560782231248788752385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4842373854820832525834923 7263560782231248788752385)
            ·
              refine ⟨5447670586673436591564289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7263560782231248788752385 5447670586673436591564289)
              ·
                refine ⟨4085752940005077443673217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447670586673436591564289 4085752940005077443673217)
                ·
                  refine ⟨3064314705003808082754913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085752940005077443673217 3064314705003808082754913)
                  ·
                    refine ⟨2298236028752856062066185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064314705003808082754913 2298236028752856062066185)
                    ·
                      refine ⟨1723677021564642046549639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298236028752856062066185 1723677021564642046549639)
                      ·
                        rfl

theorem cell23_3356849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_3356849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356849 prefixEnd_3356849 := by exact prefixLift 3356849
  have htrace : WordTrace (prefixWord ++ tailWord_3356849) baseStart_3356849 baseEnd_3356849 := by
    simpa [prefixWord, tailWord_3356849, baseEnd_3356849] using wordTrace_append hprefix tailTrace_3356849
  have hstable : (prefixWord ++ tailWord_3356849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356849).length < 2 ^ (prefixWord ++ tailWord_3356849).sum := by decide
  have hdescent : baseEnd_3356849 < baseStart_3356849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356855 : List Nat := [1, 1, 3, 1, 4, 2, 4, 2, 5]
def baseStart_3356855 : Nat := 118140960795 + 3356855 * 2 ^ 59
def prefixEnd_3356855 : Nat := 4983230072969 + 3 ^ 40 * 3356855 * 2
def baseEnd_3356855 : Nat := 191520011383174335897179

theorem tailTrace_3356855 : CollatzResearch.WordTrace tailWord_3356855 prefixEnd_3356855 191520011383174335897179 := by
  unfold tailWord_3356855
  simp only [CollatzResearch.WordTrace]
  refine ⟨122434560253695115035952019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81623040169130076690634679 122434560253695115035952019)
  ·
    refine ⟨183651840380542672553928029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122434560253695115035952019 183651840380542672553928029)
    ·
      refine ⟨68869440142703502207723011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183651840380542672553928029 68869440142703502207723011)
      ·
        refine ⟨103304160214055253311584517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68869440142703502207723011 103304160214055253311584517)
        ·
          refine ⟨19369530040135359995922097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103304160214055253311584517 19369530040135359995922097)
          ·
            refine ⟨14527147530101519996941573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19369530040135359995922097 14527147530101519996941573)
            ·
              refine ⟨2723840161894034999426545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14527147530101519996941573 2723840161894034999426545)
              ·
                refine ⟨2042880121420526249569909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2723840161894034999426545 2042880121420526249569909)
                ·
                  refine ⟨191520011383174335897179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2042880121420526249569909 191520011383174335897179)
                  ·
                    rfl

theorem cell23_3356855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 2, 5].length) (baseStart_3356855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356855 prefixEnd_3356855 := by exact prefixLift 3356855
  have htrace : WordTrace (prefixWord ++ tailWord_3356855) baseStart_3356855 baseEnd_3356855 := by
    simpa [prefixWord, tailWord_3356855, baseEnd_3356855] using wordTrace_append hprefix tailTrace_3356855
  have hstable : (prefixWord ++ tailWord_3356855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356855).length < 2 ^ (prefixWord ++ tailWord_3356855).sum := by decide
  have hdescent : baseEnd_3356855 < baseStart_3356855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356858 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2]
def baseStart_3356858 : Nat := 118140960795 + 3356858 * 2 ^ 59
def prefixEnd_3356858 : Nat := 4983230072969 + 3 ^ 40 * 3356858 * 2
def baseEnd_3356858 : Nat := 1723681642890532511337097

theorem tailTrace_3356858 : CollatzResearch.WordTrace tailWord_3356858 prefixEnd_3356858 1723681642890532511337097 := by
  unfold tailWord_3356858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30608667418171061637077807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81623113115122831032207485 30608667418171061637077807)
  ·
    refine ⟨45913001127256592455616711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30608667418171061637077807 45913001127256592455616711)
    ·
      refine ⟨68869501690884888683425067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45913001127256592455616711 68869501690884888683425067)
      ·
        refine ⟨103304252536327333025137601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68869501690884888683425067 103304252536327333025137601)
        ·
          refine ⟨77478189402245499768853201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103304252536327333025137601 77478189402245499768853201)
          ·
            refine ⟨58108642051684124826639901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77478189402245499768853201 58108642051684124826639901)
            ·
              refine ⟨21790740769381546809989963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58108642051684124826639901 21790740769381546809989963)
              ·
                refine ⟨32686111154072320214984945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21790740769381546809989963 32686111154072320214984945)
                ·
                  refine ⟨24514583365554240161238709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32686111154072320214984945 24514583365554240161238709)
                  ·
                    refine ⟨2298242190520710015116129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24514583365554240161238709 2298242190520710015116129)
                    ·
                      refine ⟨1723681642890532511337097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298242190520710015116129 1723681642890532511337097)
                      ·
                        rfl

theorem cell23_3356858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2].length) (baseStart_3356858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356858 prefixEnd_3356858 := by exact prefixLift 3356858
  have htrace : WordTrace (prefixWord ++ tailWord_3356858) baseStart_3356858 baseEnd_3356858 := by
    simpa [prefixWord, tailWord_3356858, baseEnd_3356858] using wordTrace_append hprefix tailTrace_3356858
  have hstable : (prefixWord ++ tailWord_3356858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356858).length < 2 ^ (prefixWord ++ tailWord_3356858).sum := by decide
  have hdescent : baseEnd_3356858 < baseStart_3356858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356866 : List Nat := [3, 5, 1, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_3356866 : Nat := 118140960795 + 3356866 * 2 ^ 59
def prefixEnd_3356866 : Nat := 4983230072969 + 3 ^ 40 * 3356866 * 2
def baseEnd_3356866 : Nat := 1723685750735768480037061

theorem tailTrace_3356866 : CollatzResearch.WordTrace tailWord_3356866 prefixEnd_3356866 1723685750735768480037061 := by
  unfold tailWord_3356866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30608740364163815978650613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81623307637770175943068301 30608740364163815978650613)
  ·
    refine ⟨2869569409140357747998495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30608740364163815978650613 2869569409140357747998495)
    ·
      refine ⟨4304354113710536621997743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2869569409140357747998495 4304354113710536621997743)
      ·
        refine ⟨6456531170565804932996615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4304354113710536621997743 6456531170565804932996615)
        ·
          refine ⟨9684796755848707399494923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6456531170565804932996615 9684796755848707399494923)
          ·
            refine ⟨14527195133773061099242385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9684796755848707399494923 14527195133773061099242385)
            ·
              refine ⟨10895396350329795824431789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14527195133773061099242385 10895396350329795824431789)
              ·
                refine ⟨4085773631373673434161921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10895396350329795824431789 4085773631373673434161921)
                ·
                  refine ⟨3064330223530255075621441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085773631373673434161921 3064330223530255075621441)
                  ·
                    refine ⟨2298247667647691306716081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064330223530255075621441 2298247667647691306716081)
                    ·
                      refine ⟨1723685750735768480037061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298247667647691306716081 1723685750735768480037061)
                      ·
                        rfl

theorem cell23_3356866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_3356866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356866 prefixEnd_3356866 := by exact prefixLift 3356866
  have htrace : WordTrace (prefixWord ++ tailWord_3356866) baseStart_3356866 baseEnd_3356866 := by
    simpa [prefixWord, tailWord_3356866, baseEnd_3356866] using wordTrace_append hprefix tailTrace_3356866
  have hstable : (prefixWord ++ tailWord_3356866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356866).length < 2 ^ (prefixWord ++ tailWord_3356866).sum := by decide
  have hdescent : baseEnd_3356866 < baseStart_3356866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356888 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_3356888 : Nat := 118140960795 + 3356888 * 2 ^ 59
def prefixEnd_3356888 : Nat := 4983230072969 + 3 ^ 40 * 3356888 * 2
def baseEnd_3356888 : Nat := 1723697047310167393961959

theorem tailTrace_3356888 : CollatzResearch.WordTrace tailWord_3356888 prefixEnd_3356888 1723697047310167393961959 := by
  unfold tailWord_3356888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61217881931287780835951659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81623842575050374447935545 61217881931287780835951659)
  ·
    refine ⟨91826822896931671253927489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61217881931287780835951659 91826822896931671253927489)
    ·
      refine ⟨68870117172698753440445617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91826822896931671253927489 68870117172698753440445617)
      ·
        refine ⟨51652587879524065080334213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68870117172698753440445617 51652587879524065080334213)
        ·
          refine ⟨9684860227410762202562665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51652587879524065080334213 9684860227410762202562665)
          ·
            refine ⟨7263645170558071651921999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9684860227410762202562665 7263645170558071651921999)
            ·
              refine ⟨10895467755837107477882999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7263645170558071651921999 10895467755837107477882999)
              ·
                refine ⟨16343201633755661216824499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10895467755837107477882999 16343201633755661216824499)
                ·
                  refine ⟨24514802450633491825236749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16343201633755661216824499 24514802450633491825236749)
                  ·
                    refine ⟨9193050918987559434463781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24514802450633491825236749 9193050918987559434463781)
                    ·
                      refine ⟨1723697047310167393961959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9193050918987559434463781 1723697047310167393961959)
                      ·
                        rfl

theorem cell23_3356888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_3356888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356888 prefixEnd_3356888 := by exact prefixLift 3356888
  have htrace : WordTrace (prefixWord ++ tailWord_3356888) baseStart_3356888 baseEnd_3356888 := by
    simpa [prefixWord, tailWord_3356888, baseEnd_3356888] using wordTrace_append hprefix tailTrace_3356888
  have hstable : (prefixWord ++ tailWord_3356888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356888).length < 2 ^ (prefixWord ++ tailWord_3356888).sum := by decide
  have hdescent : baseEnd_3356888 < baseStart_3356888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356908 : List Nat := [2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 3]
def baseStart_3356908 : Nat := 118140960795 + 3356908 * 2 ^ 59
def prefixEnd_3356908 : Nat := 4983230072969 + 3 ^ 40 * 3356908 * 2
def baseEnd_3356908 : Nat := 1723707316923257315711867

theorem tailTrace_3356908 : CollatzResearch.WordTrace tailWord_3356908 prefixEnd_3356908 1723707316923257315711867 := by
  unfold tailWord_3356908
  simp only [CollatzResearch.WordTrace]
  refine ⟨61218246661251552543815689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81624328881668736725087585 61218246661251552543815689)
  ·
    refine ⟨45913684995938664407861767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61218246661251552543815689 45913684995938664407861767)
    ·
      refine ⟨68870527493907996611792651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45913684995938664407861767 68870527493907996611792651)
      ·
        refine ⟨103305791240861994917688977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68870527493907996611792651 103305791240861994917688977)
        ·
          refine ⟨77479343430646496188266733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103305791240861994917688977 77479343430646496188266733)
          ·
            refine ⟨29054753786492436070600025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77479343430646496188266733 29054753786492436070600025)
            ·
              refine ⟨21791065339869327052950019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29054753786492436070600025 21791065339869327052950019)
              ·
                refine ⟨32686598009803990579425029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21791065339869327052950019 32686598009803990579425029)
                ·
                  refine ⟨6128737126838248233642193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32686598009803990579425029 6128737126838248233642193)
                  ·
                    refine ⟨4596552845128686175231645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6128737126838248233642193 4596552845128686175231645)
                    ·
                      refine ⟨1723707316923257315711867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4596552845128686175231645 1723707316923257315711867)
                      ·
                        rfl

theorem cell23_3356908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_3356908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356908 prefixEnd_3356908 := by exact prefixLift 3356908
  have htrace : WordTrace (prefixWord ++ tailWord_3356908) baseStart_3356908 baseEnd_3356908 := by
    simpa [prefixWord, tailWord_3356908, baseEnd_3356908] using wordTrace_append hprefix tailTrace_3356908
  have hstable : (prefixWord ++ tailWord_3356908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356908).length < 2 ^ (prefixWord ++ tailWord_3356908).sum := by decide
  have hdescent : baseEnd_3356908 < baseStart_3356908 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356915 : List Nat := [1, 1, 1, 2, 2, 4, 1, 6, 1, 4]
def baseStart_3356915 : Nat := 118140960795 + 3356915 * 2 ^ 59
def prefixEnd_3356915 : Nat := 4983230072969 + 3 ^ 40 * 3356915 * 2
def baseEnd_3356915 : Nat := 574570303762612929441445

theorem tailTrace_3356915 : CollatzResearch.WordTrace tailWord_3356915 prefixEnd_3356915 574570303762612929441445 := by
  unfold tailWord_3356915
  simp only [CollatzResearch.WordTrace]
  refine ⟨122436748633477745283136199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81624499088985163522090799 122436748633477745283136199)
  ·
    refine ⟨183655122950216617924704299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122436748633477745283136199 183655122950216617924704299)
    ·
      refine ⟨275482684425324926887056449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183655122950216617924704299 275482684425324926887056449)
      ·
        refine ⟨206612013318993695165292337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275482684425324926887056449 206612013318993695165292337)
        ·
          refine ⟨154959009989245271373969253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206612013318993695165292337 154959009989245271373969253)
          ·
            refine ⟨29054814372983488382619235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154959009989245271373969253 29054814372983488382619235)
            ·
              refine ⟨43582221559475232573928853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29054814372983488382619235 43582221559475232573928853)
              ·
                refine ⟨2042916635600401526902915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43582221559475232573928853 2042916635600401526902915)
                ·
                  refine ⟨3064374953400602290354373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042916635600401526902915 3064374953400602290354373)
                  ·
                    refine ⟨574570303762612929441445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3064374953400602290354373 574570303762612929441445)
                    ·
                      rfl

theorem cell23_3356915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 1, 4].length) (baseStart_3356915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356915 prefixEnd_3356915 := by exact prefixLift 3356915
  have htrace : WordTrace (prefixWord ++ tailWord_3356915) baseStart_3356915 baseEnd_3356915 := by
    simpa [prefixWord, tailWord_3356915, baseEnd_3356915] using wordTrace_append hprefix tailTrace_3356915
  have hstable : (prefixWord ++ tailWord_3356915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356915).length < 2 ^ (prefixWord ++ tailWord_3356915).sum := by decide
  have hdescent : baseEnd_3356915 < baseStart_3356915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356931 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6]
def baseStart_3356931 : Nat := 118140960795 + 3356931 * 2 ^ 59
def prefixEnd_3356931 : Nat := 4983230072969 + 3 ^ 40 * 3356931 * 2
def baseEnd_3356931 : Nat := 1723719126978310725724261

theorem tailTrace_3356931 : CollatzResearch.WordTrace tailWord_3356931 prefixEnd_3356931 1723719126978310725724261 := by
  unfold tailWord_3356931
  simp only [CollatzResearch.WordTrace]
  refine ⟨122437332201419780015718647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81624888134279853343812431 122437332201419780015718647)
  ·
    refine ⟨183655998302129670023577971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122437332201419780015718647 183655998302129670023577971)
    ·
      refine ⟨275483997453194505035366957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183655998302129670023577971 275483997453194505035366957)
      ·
        refine ⟨103306499044947939388262609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275483997453194505035366957 103306499044947939388262609)
        ·
          refine ⟨77479874283710954541196957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103306499044947939388262609 77479874283710954541196957)
          ·
            refine ⟨29054952856391607952948859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77479874283710954541196957 29054952856391607952948859)
            ·
              refine ⟨43582429284587411929423289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29054952856391607952948859 43582429284587411929423289)
              ·
                refine ⟨32686821963440558947067467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43582429284587411929423289 32686821963440558947067467)
                ·
                  refine ⟨49030232945160838420601201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32686821963440558947067467 49030232945160838420601201)
                  ·
                    refine ⟨36772674708870628815450901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49030232945160838420601201 36772674708870628815450901)
                    ·
                      refine ⟨1723719126978310725724261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36772674708870628815450901 1723719126978310725724261)
                      ·
                        rfl

theorem cell23_3356931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_3356931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356931 prefixEnd_3356931 := by exact prefixLift 3356931
  have htrace : WordTrace (prefixWord ++ tailWord_3356931) baseStart_3356931 baseEnd_3356931 := by
    simpa [prefixWord, tailWord_3356931, baseEnd_3356931] using wordTrace_append hprefix tailTrace_3356931
  have hstable : (prefixWord ++ tailWord_3356931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356931).length < 2 ^ (prefixWord ++ tailWord_3356931).sum := by decide
  have hdescent : baseEnd_3356931 < baseStart_3356931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356972 : List Nat := [2, 2, 1, 1, 1, 3, 2, 6, 1, 1, 3]
def baseStart_3356972 : Nat := 118140960795 + 3356972 * 2 ^ 59
def prefixEnd_3356972 : Nat := 4983230072969 + 3 ^ 40 * 3356972 * 2
def baseEnd_3356972 : Nat := 1723740179685145065311573

theorem tailTrace_3356972 : CollatzResearch.WordTrace tailWord_3356972 prefixEnd_3356972 1723740179685145065311573 := by
  unfold tailWord_3356972
  simp only [CollatzResearch.WordTrace]
  refine ⟨61219413797135622008980585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81625885062847496011974113 61219413797135622008980585)
  ·
    refine ⟨45914560347851716506735439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61219413797135622008980585 45914560347851716506735439)
    ·
      refine ⟨68871840521777574760103159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45914560347851716506735439 68871840521777574760103159)
      ·
        refine ⟨103307760782666362140154739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68871840521777574760103159 103307760782666362140154739)
        ·
          refine ⟨154961641173999543210232109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103307760782666362140154739 154961641173999543210232109)
          ·
            refine ⟨58110615440249828703837041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154961641173999543210232109 58110615440249828703837041)
            ·
              refine ⟨43582961580187371527877781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58110615440249828703837041 43582961580187371527877781)
              ·
                refine ⟨2042951324071283040369271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43582961580187371527877781 2042951324071283040369271)
                ·
                  refine ⟨3064426986106924560553907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2042951324071283040369271 3064426986106924560553907)
                  ·
                    refine ⟨4596640479160386840830861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3064426986106924560553907 4596640479160386840830861)
                    ·
                      refine ⟨1723740179685145065311573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4596640479160386840830861 1723740179685145065311573)
                      ·
                        rfl

theorem cell23_3356972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 6, 1, 1, 3].length) (baseStart_3356972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356972 prefixEnd_3356972 := by exact prefixLift 3356972
  have htrace : WordTrace (prefixWord ++ tailWord_3356972) baseStart_3356972 baseEnd_3356972 := by
    simpa [prefixWord, tailWord_3356972, baseEnd_3356972] using wordTrace_append hprefix tailTrace_3356972
  have hstable : (prefixWord ++ tailWord_3356972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356972).length < 2 ^ (prefixWord ++ tailWord_3356972).sum := by decide
  have hdescent : baseEnd_3356972 < baseStart_3356972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356988 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 1, 6]
def baseStart_3356988 : Nat := 118140960795 + 3356988 * 2 ^ 59
def prefixEnd_3356988 : Nat := 4983230072969 + 3 ^ 40 * 3356988 * 2
def baseEnd_3356988 : Nat := 574582798458539000903833

theorem tailTrace_3356988 : CollatzResearch.WordTrace tailWord_3356988 prefixEnd_3356988 574582798458539000903833 := by
  unfold tailWord_3356988
  simp only [CollatzResearch.WordTrace]
  refine ⟨61219705581106639375271809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81626274108142185833695745 61219705581106639375271809)
  ·
    refine ⟨45914779185829979531453857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61219705581106639375271809 45914779185829979531453857)
    ·
      refine ⟨34436084389372484648590393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45914779185829979531453857 34436084389372484648590393)
      ·
        refine ⟨25827063292029363486442795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34436084389372484648590393 25827063292029363486442795)
        ·
          refine ⟨38740594938044045229664193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25827063292029363486442795 38740594938044045229664193)
          ·
            refine ⟨29055446203533033922248145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38740594938044045229664193 29055446203533033922248145)
            ·
              refine ⟨21791584652649775441686109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29055446203533033922248145 21791584652649775441686109)
              ·
                refine ⟨8171844244743665790632291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21791584652649775441686109 8171844244743665790632291)
                ·
                  refine ⟨12257766367115498685948437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8171844244743665790632291 12257766367115498685948437)
                  ·
                    refine ⟨574582798458539000903833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12257766367115498685948437 574582798458539000903833)
                    ·
                      rfl

theorem cell23_3356988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_3356988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356988 prefixEnd_3356988 := by exact prefixLift 3356988
  have htrace : WordTrace (prefixWord ++ tailWord_3356988) baseStart_3356988 baseEnd_3356988 := by
    simpa [prefixWord, tailWord_3356988, baseEnd_3356988] using wordTrace_append hprefix tailTrace_3356988
  have hstable : (prefixWord ++ tailWord_3356988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356988).length < 2 ^ (prefixWord ++ tailWord_3356988).sum := by decide
  have hdescent : baseEnd_3356988 < baseStart_3356988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3356995 : List Nat := [1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 4]
def baseStart_3356995 : Nat := 118140960795 + 3356995 * 2 ^ 59
def prefixEnd_3356995 : Nat := 4983230072969 + 3 ^ 40 * 3356995 * 2
def baseEnd_3356995 : Nat := 1723751989740198475323967

theorem tailTrace_3356995 : CollatzResearch.WordTrace tailWord_3356995 prefixEnd_3356995 1723751989740198475323967 := by
  unfold tailWord_3356995
  simp only [CollatzResearch.WordTrace]
  refine ⟨122439666473187918946048439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81626444315458612630698959 122439666473187918946048439)
  ·
    refine ⟨183659499709781878419072659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122439666473187918946048439 183659499709781878419072659)
    ·
      refine ⟨275489249564672817628608989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183659499709781878419072659 275489249564672817628608989)
      ·
        refine ⟨103308468586752306610728371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275489249564672817628608989 103308468586752306610728371)
        ·
          refine ⟨154962702880128459916092557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103308468586752306610728371 154962702880128459916092557)
          ·
            refine ⟨58111013580048172468534709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154962702880128459916092557 58111013580048172468534709)
            ·
              refine ⟨5447907523129516168925129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58111013580048172468534709 5447907523129516168925129)
              ·
                refine ⟨4085930642347137126693847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5447907523129516168925129 4085930642347137126693847)
                ·
                  refine ⟨6128895963520705690040771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4085930642347137126693847 6128895963520705690040771)
                  ·
                    refine ⟨9193343945281058535061157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6128895963520705690040771 9193343945281058535061157)
                    ·
                      refine ⟨1723751989740198475323967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9193343945281058535061157 1723751989740198475323967)
                      ·
                        rfl

theorem cell23_3356995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 4].length) (baseStart_3356995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3356995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3356995 prefixEnd_3356995 := by exact prefixLift 3356995
  have htrace : WordTrace (prefixWord ++ tailWord_3356995) baseStart_3356995 baseEnd_3356995 := by
    simpa [prefixWord, tailWord_3356995, baseEnd_3356995] using wordTrace_append hprefix tailTrace_3356995
  have hstable : (prefixWord ++ tailWord_3356995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3356995).length < 2 ^ (prefixWord ++ tailWord_3356995).sum := by decide
  have hdescent : baseEnd_3356995 < baseStart_3356995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3356995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357008 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_3357008 : Nat := 118140960795 + 3357008 * 2 ^ 59
def prefixEnd_3357008 : Nat := 4983230072969 + 3 ^ 40 * 3357008 * 2
def baseEnd_3357008 : Nat := 1723758664988706924461407

theorem tailTrace_3357008 : CollatzResearch.WordTrace tailWord_3357008 prefixEnd_3357008 1723758664988706924461407 := by
  unfold tailWord_3357008
  simp only [CollatzResearch.WordTrace]
  refine ⟨61220070311070411083135839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81626760414760548110847785 61220070311070411083135839)
  ·
    refine ⟨91830105466605616624703759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61220070311070411083135839 91830105466605616624703759)
    ·
      refine ⟨137745158199908424937055639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91830105466605616624703759 137745158199908424937055639)
      ·
        refine ⟨206617737299862637405583459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137745158199908424937055639 206617737299862637405583459)
        ·
          refine ⟨309926605949793956108375189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206617737299862637405583459 309926605949793956108375189)
          ·
            refine ⟨14527809653896591692580087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309926605949793956108375189 14527809653896591692580087)
            ·
              refine ⟨21791714480844887538870131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14527809653896591692580087 21791714480844887538870131)
              ·
                refine ⟨32687571721267331308305197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21791714480844887538870131 32687571721267331308305197)
                ·
                  refine ⟨12257839395475249240614449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32687571721267331308305197 12257839395475249240614449)
                  ·
                    refine ⟨9193379546606436930460837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12257839395475249240614449 9193379546606436930460837)
                    ·
                      refine ⟨1723758664988706924461407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9193379546606436930460837 1723758664988706924461407)
                      ·
                        rfl

theorem cell23_3357008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_3357008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357008 prefixEnd_3357008 := by exact prefixLift 3357008
  have htrace : WordTrace (prefixWord ++ tailWord_3357008) baseStart_3357008 baseEnd_3357008 := by
    simpa [prefixWord, tailWord_3357008, baseEnd_3357008] using wordTrace_append hprefix tailTrace_3357008
  have hstable : (prefixWord ++ tailWord_3357008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357008).length < 2 ^ (prefixWord ++ tailWord_3357008).sum := by decide
  have hdescent : baseEnd_3357008 < baseStart_3357008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357095 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 2, 6]
def baseStart_3357095 : Nat := 118140960795 + 3357095 * 2 ^ 59
def prefixEnd_3357095 : Nat := 4983230072969 + 3 ^ 40 * 3357095 * 2
def baseEnd_3357095 : Nat := 574601112601882694691169

theorem tailTrace_3357095 : CollatzResearch.WordTrace tailWord_3357095 prefixEnd_3357095 574601112601882694691169 := by
  unfold tailWord_3357095
  simp only [CollatzResearch.WordTrace]
  refine ⟨122443313772825636024688739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81628875848550424016459159 122443313772825636024688739)
  ·
    refine ⟨183664970659238454037033109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122443313772825636024688739 183664970659238454037033109)
    ·
      refine ⟨8609295499651802532985927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183664970659238454037033109 8609295499651802532985927)
      ·
        refine ⟨12913943249477703799478891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609295499651802532985927 12913943249477703799478891)
        ·
          refine ⟨19370914874216555699218337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12913943249477703799478891 19370914874216555699218337)
          ·
            refine ⟨14528186155662416774413753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19370914874216555699218337 14528186155662416774413753)
            ·
              refine ⟨10896139616746812580810315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14528186155662416774413753 10896139616746812580810315)
              ·
                refine ⟨16344209425120218871215473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10896139616746812580810315 16344209425120218871215473)
                ·
                  refine ⟨12258157068840164153411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16344209425120218871215473 12258157068840164153411605)
                  ·
                    refine ⟨574601112601882694691169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12258157068840164153411605 574601112601882694691169)
                    ·
                      rfl

theorem cell23_3357095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_3357095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357095 prefixEnd_3357095 := by exact prefixLift 3357095
  have htrace : WordTrace (prefixWord ++ tailWord_3357095) baseStart_3357095 baseEnd_3357095 := by
    simpa [prefixWord, tailWord_3357095, baseEnd_3357095] using wordTrace_append hprefix tailTrace_3357095
  have hstable : (prefixWord ++ tailWord_3357095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357095).length < 2 ^ (prefixWord ++ tailWord_3357095).sum := by decide
  have hdescent : baseEnd_3357095 < baseStart_3357095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357192 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_3357192 : Nat := 118140960795 + 3357192 * 2 ^ 59
def prefixEnd_3357192 : Nat := 4983230072969 + 3 ^ 40 * 3357192 * 2
def baseEnd_3357192 : Nat := 1723853145429134204560561

theorem tailTrace_3357192 : CollatzResearch.WordTrace tailWord_3357192 prefixEnd_3357192 1723853145429134204560561 := by
  unfold tailWord_3357192
  simp only [CollatzResearch.WordTrace]
  refine ⟨61223425826737110795484915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81631234435649481060646553 61223425826737110795484915)
  ·
    refine ⟨91835138740105666193227373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61223425826737110795484915 91835138740105666193227373)
    ·
      refine ⟨34438177027539624822460265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91835138740105666193227373 34438177027539624822460265)
      ·
        refine ⟨25828632770654718616845199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34438177027539624822460265 25828632770654718616845199)
        ·
          refine ⟨38742949155982077925267799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25828632770654718616845199 38742949155982077925267799)
          ·
            refine ⟨58114423733973116887901699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38742949155982077925267799 58114423733973116887901699)
            ·
              refine ⟨87171635600959675331852549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58114423733973116887901699 87171635600959675331852549)
              ·
                refine ⟨16344681675179939124722353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87171635600959675331852549 16344681675179939124722353)
                ·
                  refine ⟨12258511256384954343541765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16344681675179939124722353 12258511256384954343541765)
                  ·
                    refine ⟨2298470860572178939414081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12258511256384954343541765 2298470860572178939414081)
                    ·
                      refine ⟨1723853145429134204560561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298470860572178939414081 1723853145429134204560561)
                      ·
                        rfl

theorem cell23_3357192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_3357192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357192 prefixEnd_3357192 := by exact prefixLift 3357192
  have htrace : WordTrace (prefixWord ++ tailWord_3357192) baseStart_3357192 baseEnd_3357192 := by
    simpa [prefixWord, tailWord_3357192, baseEnd_3357192] using wordTrace_append hprefix tailTrace_3357192
  have hstable : (prefixWord ++ tailWord_3357192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357192).length < 2 ^ (prefixWord ++ tailWord_3357192).sum := by decide
  have hdescent : baseEnd_3357192 < baseStart_3357192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357223 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 2, 5]
def baseStart_3357223 : Nat := 118140960795 + 3357223 * 2 ^ 59
def prefixEnd_3357223 : Nat := 4983230072969 + 3 ^ 40 * 3357223 * 2
def baseEnd_3357223 : Nat := 574623021109807861090973

theorem tailTrace_3357223 : CollatzResearch.WordTrace tailWord_3357223 prefixEnd_3357223 574623021109807861090973 := by
  unfold tailWord_3357223
  simp only [CollatzResearch.WordTrace]
  refine ⟨122447982316361913885348323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81631988210907942590232215 122447982316361913885348323)
  ·
    refine ⟨183671973474542870828022485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122447982316361913885348323 183671973474542870828022485)
    ·
      refine ⟨4304811878309598535031777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 183671973474542870828022485 4304811878309598535031777)
      ·
        refine ⟨3228608908732198901273833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4304811878309598535031777 3228608908732198901273833)
        ·
          refine ⟨2421456681549149175955375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3228608908732198901273833 2421456681549149175955375)
          ·
            refine ⟨3632185022323723763933063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421456681549149175955375 3632185022323723763933063)
            ·
              refine ⟨5448277533485585645899595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632185022323723763933063 5448277533485585645899595)
              ·
                refine ⟨8172416300228378468849393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448277533485585645899595 8172416300228378468849393)
                ·
                  refine ⟨6129312225171283851637045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8172416300228378468849393 6129312225171283851637045)
                  ·
                    refine ⟨574623021109807861090973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6129312225171283851637045 574623021109807861090973)
                    ·
                      rfl

theorem cell23_3357223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_3357223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357223 prefixEnd_3357223 := by exact prefixLift 3357223
  have htrace : WordTrace (prefixWord ++ tailWord_3357223) baseStart_3357223 baseEnd_3357223 := by
    simpa [prefixWord, tailWord_3357223, baseEnd_3357223] using wordTrace_append hprefix tailTrace_3357223
  have hstable : (prefixWord ++ tailWord_3357223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357223).length < 2 ^ (prefixWord ++ tailWord_3357223).sum := by decide
  have hdescent : baseEnd_3357223 < baseStart_3357223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357249 : List Nat := [1, 2, 5, 1, 1, 4, 1, 2, 6]
def baseStart_3357249 : Nat := 118140960795 + 3357249 * 2 ^ 59
def prefixEnd_3357249 : Nat := 4983230072969 + 3 ^ 40 * 3357249 * 2
def baseEnd_3357249 : Nat := 191542490425160053505311

theorem tailTrace_3357249 : CollatzResearch.WordTrace tailWord_3357249 prefixEnd_3357249 191542490425160053505311 := by
  unfold tailWord_3357249
  simp only [CollatzResearch.WordTrace]
  refine ⟨122448930614267720325794801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81632620409511813550529867 122448930614267720325794801)
  ·
    refine ⟨91836697960700790244346101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122448930614267720325794801 91836697960700790244346101)
    ·
      refine ⟨8609690433815699085407447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91836697960700790244346101 8609690433815699085407447)
      ·
        refine ⟨12914535650723548628111171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8609690433815699085407447 12914535650723548628111171)
        ·
          refine ⟨19371803476085322942166757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12914535650723548628111171 19371803476085322942166757)
          ·
            refine ⟨3632213151765998051656267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19371803476085322942166757 3632213151765998051656267)
            ·
              refine ⟨5448319727648997077484401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632213151765998051656267 5448319727648997077484401)
              ·
                refine ⟨4086239795736747808113301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5448319727648997077484401 4086239795736747808113301)
                ·
                  refine ⟨191542490425160053505311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4086239795736747808113301 191542490425160053505311)
                  ·
                    rfl

theorem cell23_3357249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_3357249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357249 prefixEnd_3357249 := by exact prefixLift 3357249
  have htrace : WordTrace (prefixWord ++ tailWord_3357249) baseStart_3357249 baseEnd_3357249 := by
    simpa [prefixWord, tailWord_3357249, baseEnd_3357249] using wordTrace_append hprefix tailTrace_3357249
  have hstable : (prefixWord ++ tailWord_3357249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357249).length < 2 ^ (prefixWord ++ tailWord_3357249).sum := by decide
  have hdescent : baseEnd_3357249 < baseStart_3357249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357292 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 4, 4]
def baseStart_3357292 : Nat := 118140960795 + 3357292 * 2 ^ 59
def prefixEnd_3357292 : Nat := 4983230072969 + 3 ^ 40 * 3357292 * 2
def baseEnd_3357292 : Nat := 574634831164861271103367

theorem tailTrace_3357292 : CollatzResearch.WordTrace tailWord_3357292 prefixEnd_3357292 574634831164861271103367 := by
  unfold tailWord_3357292
  simp only [CollatzResearch.WordTrace]
  refine ⟨61225249476555969334805065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81633665968741292446406753 61225249476555969334805065)
  ·
    refine ⟨45918937107416977001103799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61225249476555969334805065 45918937107416977001103799)
    ·
      refine ⟨68878405661125465501655699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45918937107416977001103799 68878405661125465501655699)
      ·
        refine ⟨103317608491688198252483549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68878405661125465501655699 103317608491688198252483549)
        ·
          refine ⟨38744103184383074344681331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103317608491688198252483549 38744103184383074344681331)
          ·
            refine ⟨58116154776574611517021997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38744103184383074344681331 58116154776574611517021997)
            ·
              refine ⟨21793558041215479318883249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58116154776574611517021997 21793558041215479318883249)
              ·
                refine ⟨16345168530911609489162437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21793558041215479318883249 16345168530911609489162437)
                ·
                  refine ⟨3064719099545926779217957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16345168530911609489162437 3064719099545926779217957)
                  ·
                    refine ⟨574634831164861271103367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3064719099545926779217957 574634831164861271103367)
                    ·
                      rfl

theorem cell23_3357292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 4].length) (baseStart_3357292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357292 prefixEnd_3357292 := by exact prefixLift 3357292
  have htrace : WordTrace (prefixWord ++ tailWord_3357292) baseStart_3357292 baseEnd_3357292 := by
    simpa [prefixWord, tailWord_3357292, baseEnd_3357292] using wordTrace_append hprefix tailTrace_3357292
  have hstable : (prefixWord ++ tailWord_3357292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357292).length < 2 ^ (prefixWord ++ tailWord_3357292).sum := by decide
  have hdescent : baseEnd_3357292 < baseStart_3357292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357293 : List Nat := [1, 5, 1, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_3357293 : Nat := 118140960795 + 3357293 * 2 ^ 59
def prefixEnd_3357293 : Nat := 4983230072969 + 3 ^ 40 * 3357293 * 2
def baseEnd_3357293 : Nat := 1723905006975238309397597

theorem tailTrace_3357293 : CollatzResearch.WordTrace tailWord_3357293 prefixEnd_3357293 1723905006975238309397597 := by
  unfold tailWord_3357293
  simp only [CollatzResearch.WordTrace]
  refine ⟨122450535426108315840396533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81633690284072210560264355 122450535426108315840396533)
  ·
    refine ⟨11479737696197654610037175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122450535426108315840396533 11479737696197654610037175)
    ·
      refine ⟨17219606544296481915055763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11479737696197654610037175 17219606544296481915055763)
      ·
        refine ⟨25829409816444722872583645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17219606544296481915055763 25829409816444722872583645)
        ·
          refine ⟨9686028681166771077218867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25829409816444722872583645 9686028681166771077218867)
          ·
            refine ⟨14529043021750156615828301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686028681166771077218867 14529043021750156615828301)
            ·
              refine ⟨5448391133156308730935613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14529043021750156615828301 5448391133156308730935613)
              ·
                refine ⟨2043146674933615774100855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5448391133156308730935613 2043146674933615774100855)
                ·
                  refine ⟨3064720012400423661151283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043146674933615774100855 3064720012400423661151283)
                  ·
                    refine ⟨4597080018600635491726925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3064720012400423661151283 4597080018600635491726925)
                    ·
                      refine ⟨1723905006975238309397597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4597080018600635491726925 1723905006975238309397597)
                      ·
                        rfl

theorem cell23_3357293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_3357293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357293 prefixEnd_3357293 := by exact prefixLift 3357293
  have htrace : WordTrace (prefixWord ++ tailWord_3357293) baseStart_3357293 baseEnd_3357293 := by
    simpa [prefixWord, tailWord_3357293, baseEnd_3357293] using wordTrace_append hprefix tailTrace_3357293
  have hstable : (prefixWord ++ tailWord_3357293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357293).length < 2 ^ (prefixWord ++ tailWord_3357293).sum := by decide
  have hdescent : baseEnd_3357293 < baseStart_3357293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357305 : List Nat := [1, 2, 1, 3, 3, 2, 11]
def baseStart_3357305 : Nat := 118140960795 + 3357305 * 2 ^ 59
def prefixEnd_3357305 : Nat := 4983230072969 + 3 ^ 40 * 3357305 * 2
def baseEnd_3357305 : Nat := 21282853935099904474661

theorem tailTrace_3357305 : CollatzResearch.WordTrace tailWord_3357305 prefixEnd_3357305 21282853935099904474661 := by
  unfold tailWord_3357305
  simp only [CollatzResearch.WordTrace]
  refine ⟨122450973102064841889833369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81633982068043227926555579 122450973102064841889833369)
  ·
    refine ⟨91838229826548631417375027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122450973102064841889833369 91838229826548631417375027)
    ·
      refine ⟨137757344739822947126062541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91838229826548631417375027 137757344739822947126062541)
      ·
        refine ⟨51659004277433605172273453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137757344739822947126062541 51659004277433605172273453)
        ·
          refine ⟨19372126604037601939602545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51659004277433605172273453 19372126604037601939602545)
          ·
            refine ⟨14529094953028201454701909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19372126604037601939602545 14529094953028201454701909)
            ·
              refine ⟨21282853935099904474661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14529094953028201454701909 21282853935099904474661)
              ·
                rfl

theorem cell23_3357305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 11].length) (baseStart_3357305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357305 prefixEnd_3357305 := by exact prefixLift 3357305
  have htrace : WordTrace (prefixWord ++ tailWord_3357305) baseStart_3357305 baseEnd_3357305 := by
    simpa [prefixWord, tailWord_3357305, baseEnd_3357305] using wordTrace_append hprefix tailTrace_3357305
  have hstable : (prefixWord ++ tailWord_3357305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357305).length < 2 ^ (prefixWord ++ tailWord_3357305).sum := by decide
  have hdescent : baseEnd_3357305 < baseStart_3357305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357367 : List Nat := [1, 1, 3, 1, 6, 2, 2, 2, 1, 2, 2]
def baseStart_3357367 : Nat := 118140960795 + 3357367 * 2 ^ 59
def prefixEnd_3357367 : Nat := 4983230072969 + 3 ^ 40 * 3357367 * 2
def baseEnd_3357367 : Nat := 1723943004543671019872257

theorem tailTrace_3357367 : CollatzResearch.WordTrace tailWord_3357367 prefixEnd_3357367 1723943004543671019872257 := by
  unfold tailWord_3357367
  simp only [CollatzResearch.WordTrace]
  refine ⟨122453234427840226478590355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81635489618560150985726903 122453234427840226478590355)
  ·
    refine ⟨183679851641760339717885533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122453234427840226478590355 183679851641760339717885533)
    ·
      refine ⟨68879944365660127394207075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183679851641760339717885533 68879944365660127394207075)
      ·
        refine ⟨103319916548490191091310613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68879944365660127394207075 103319916548490191091310613)
        ·
          refine ⟨4843121088210477707405185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103319916548490191091310613 4843121088210477707405185)
          ·
            refine ⟨3632340816157858280553889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843121088210477707405185 3632340816157858280553889)
            ·
              refine ⟨2724255612118393710415417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3632340816157858280553889 2724255612118393710415417)
              ·
                refine ⟨2043191709088795282811563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724255612118393710415417 2043191709088795282811563)
                ·
                  refine ⟨3064787563633192924217345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043191709088795282811563 3064787563633192924217345)
                  ·
                    refine ⟨2298590672724894693163009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064787563633192924217345 2298590672724894693163009)
                    ·
                      refine ⟨1723943004543671019872257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298590672724894693163009 1723943004543671019872257)
                      ·
                        rfl

theorem cell23_3357367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 1, 2, 2].length) (baseStart_3357367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357367 prefixEnd_3357367 := by exact prefixLift 3357367
  have htrace : WordTrace (prefixWord ++ tailWord_3357367) baseStart_3357367 baseEnd_3357367 := by
    simpa [prefixWord, tailWord_3357367, baseEnd_3357367] using wordTrace_append hprefix tailTrace_3357367
  have hstable : (prefixWord ++ tailWord_3357367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357367).length < 2 ^ (prefixWord ++ tailWord_3357367).sum := by decide
  have hdescent : baseEnd_3357367 < baseStart_3357367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357372 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_3357372 : Nat := 118140960795 + 3357372 * 2 ^ 59
def prefixEnd_3357372 : Nat := 4983230072969 + 3 ^ 40 * 3357372 * 2
def baseEnd_3357372 : Nat := 1723945571946943500309733

theorem tailTrace_3357372 : CollatzResearch.WordTrace tailWord_3357372 prefixEnd_3357372 1723945571946943500309733 := by
  unfold tailWord_3357372
  simp only [CollatzResearch.WordTrace]
  refine ⟨61226708396411056166261185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81635611195214741555014913 61226708396411056166261185)
  ·
    refine ⟨45920031297308292124695889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61226708396411056166261185 45920031297308292124695889)
    ·
      refine ⟨34440023472981219093521917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45920031297308292124695889 34440023472981219093521917)
      ·
        refine ⟨12915008802367957160070719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34440023472981219093521917 12915008802367957160070719)
        ·
          refine ⟨19372513203551935740106079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12915008802367957160070719 19372513203551935740106079)
          ·
            refine ⟨29058769805327903610159119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19372513203551935740106079 29058769805327903610159119)
            ·
              refine ⟨43588154707991855415238679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29058769805327903610159119 43588154707991855415238679)
              ·
                refine ⟨65382232061987783122858019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43588154707991855415238679 65382232061987783122858019)
                ·
                  refine ⟨98073348092981674684287029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65382232061987783122858019 98073348092981674684287029)
                  ·
                    refine ⟨9194376383717032001651909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98073348092981674684287029 9194376383717032001651909)
                    ·
                      refine ⟨1723945571946943500309733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9194376383717032001651909 1723945571946943500309733)
                      ·
                        rfl

theorem cell23_3357372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_3357372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357372 prefixEnd_3357372 := by exact prefixLift 3357372
  have htrace : WordTrace (prefixWord ++ tailWord_3357372) baseStart_3357372 baseEnd_3357372 := by
    simpa [prefixWord, tailWord_3357372, baseEnd_3357372] using wordTrace_append hprefix tailTrace_3357372
  have hstable : (prefixWord ++ tailWord_3357372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357372).length < 2 ^ (prefixWord ++ tailWord_3357372).sum := by decide
  have hdescent : baseEnd_3357372 < baseStart_3357372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357402 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3357402 : Nat := 118140960795 + 3357402 * 2 ^ 59
def prefixEnd_3357402 : Nat := 4983230072969 + 3 ^ 40 * 3357402 * 2
def baseEnd_3357402 : Nat := 1723960976366578382934595

theorem tailTrace_3357402 : CollatzResearch.WordTrace tailWord_3357402 prefixEnd_3357402 1723960976366578382934595 := by
  unfold tailWord_3357402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613627745678356864028615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81636340655142284970742973 30613627745678356864028615)
  ·
    refine ⟨45920441618517535296042923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30613627745678356864028615 45920441618517535296042923)
    ·
      refine ⟨68880662427776302944064385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45920441618517535296042923 68880662427776302944064385)
      ·
        refine ⟨51660496820832227208048289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68880662427776302944064385 51660496820832227208048289)
        ·
          refine ⟨38745372615624170406036217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51660496820832227208048289 38745372615624170406036217)
          ·
            refine ⟨29059029461718127804527163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38745372615624170406036217 29059029461718127804527163)
            ·
              refine ⟨43588544192577191706790745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29059029461718127804527163 43588544192577191706790745)
              ·
                refine ⟨32691408144432893780093059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43588544192577191706790745 32691408144432893780093059)
                ·
                  refine ⟨49037112216649340670139589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32691408144432893780093059 49037112216649340670139589)
                  ·
                    refine ⟨9194458540621751375651173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49037112216649340670139589 9194458540621751375651173)
                    ·
                      refine ⟨1723960976366578382934595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9194458540621751375651173 1723960976366578382934595)
                      ·
                        rfl

theorem cell23_3357402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3357402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357402 prefixEnd_3357402 := by exact prefixLift 3357402
  have htrace : WordTrace (prefixWord ++ tailWord_3357402) baseStart_3357402 baseEnd_3357402 := by
    simpa [prefixWord, tailWord_3357402, baseEnd_3357402] using wordTrace_append hprefix tailTrace_3357402
  have hstable : (prefixWord ++ tailWord_3357402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357402).length < 2 ^ (prefixWord ++ tailWord_3357402).sum := by decide
  have hdescent : baseEnd_3357402 < baseStart_3357402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357423 : List Nat := [1, 1, 2, 1, 5, 2, 3, 2, 2, 2, 2]
def baseStart_3357423 : Nat := 118140960795 + 3357423 * 2 ^ 59
def prefixEnd_3357423 : Nat := 4983230072969 + 3 ^ 40 * 3357423 * 2
def baseEnd_3357423 : Nat := 1723971759460322800771999

theorem tailTrace_3357423 : CollatzResearch.WordTrace tailWord_3357423 prefixEnd_3357423 1723971759460322800771999 := by
  unfold tailWord_3357423
  simp only [CollatzResearch.WordTrace]
  refine ⟨122455276915637348042628923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81636851277091565361752615 122455276915637348042628923)
  ·
    refine ⟨183682915373456022063943385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122455276915637348042628923 183682915373456022063943385)
    ·
      refine ⟨137762186530092016547957539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183682915373456022063943385 137762186530092016547957539)
      ·
        refine ⟨206643279795138024821936309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137762186530092016547957539 206643279795138024821936309)
        ·
          refine ⟨19372807480794189827056529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206643279795138024821936309 19372807480794189827056529)
          ·
            refine ⟨14529605610595642370292397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19372807480794189827056529 14529605610595642370292397)
            ·
              refine ⟨5448602103973365888859649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14529605610595642370292397 5448602103973365888859649)
              ·
                refine ⟨4086451577980024416644737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5448602103973365888859649 4086451577980024416644737)
                ·
                  refine ⟨3064838683485018312483553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4086451577980024416644737 3064838683485018312483553)
                  ·
                    refine ⟨2298629012613763734362665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3064838683485018312483553 2298629012613763734362665)
                    ·
                      refine ⟨1723971759460322800771999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298629012613763734362665 1723971759460322800771999)
                      ·
                        rfl

theorem cell23_3357423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 2, 2].length) (baseStart_3357423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357423 prefixEnd_3357423 := by exact prefixLift 3357423
  have htrace : WordTrace (prefixWord ++ tailWord_3357423) baseStart_3357423 baseEnd_3357423 := by
    simpa [prefixWord, tailWord_3357423, baseEnd_3357423] using wordTrace_append hprefix tailTrace_3357423
  have hstable : (prefixWord ++ tailWord_3357423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357423).length < 2 ^ (prefixWord ++ tailWord_3357423).sum := by decide
  have hdescent : baseEnd_3357423 < baseStart_3357423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357449 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 2, 5, 2]
def baseStart_3357449 : Nat := 118140960795 + 3357449 * 2 ^ 59
def prefixEnd_3357449 : Nat := 4983230072969 + 3 ^ 40 * 3357449 * 2
def baseEnd_3357449 : Nat := 1723985109957339699046879

theorem tailTrace_3357449 : CollatzResearch.WordTrace tailWord_3357449 prefixEnd_3357449 1723985109957339699046879 := by
  unfold tailWord_3357449
  simp only [CollatzResearch.WordTrace]
  refine ⟨122456225213543154483075401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81637483475695436322050267 122456225213543154483075401)
  ·
    refine ⟨91842168910157365862306551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122456225213543154483075401 91842168910157365862306551)
    ·
      refine ⟨137763253365236048793459827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91842168910157365862306551 137763253365236048793459827)
      ·
        refine ⟨206644880047854073190189741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137763253365236048793459827 206644880047854073190189741)
        ·
          refine ⟨77491830017945277446321153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206644880047854073190189741 77491830017945277446321153)
          ·
            refine ⟨58118872513458958084740865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77491830017945277446321153 58118872513458958084740865)
            ·
              refine ⟨43589154385094218563555649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58118872513458958084740865 43589154385094218563555649)
              ·
                refine ⟨32691865788820663922666737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43589154385094218563555649 32691865788820663922666737)
                ·
                  refine ⟨24518899341615497942000053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32691865788820663922666737 24518899341615497942000053)
                  ·
                    refine ⟨2298646813276452932062505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24518899341615497942000053 2298646813276452932062505)
                    ·
                      refine ⟨1723985109957339699046879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298646813276452932062505 1723985109957339699046879)
                      ·
                        rfl

theorem cell23_3357449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 5, 2].length) (baseStart_3357449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357449 prefixEnd_3357449 := by exact prefixLift 3357449
  have htrace : WordTrace (prefixWord ++ tailWord_3357449) baseStart_3357449 baseEnd_3357449 := by
    simpa [prefixWord, tailWord_3357449, baseEnd_3357449] using wordTrace_append hprefix tailTrace_3357449
  have hstable : (prefixWord ++ tailWord_3357449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357449).length < 2 ^ (prefixWord ++ tailWord_3357449).sum := by decide
  have hdescent : baseEnd_3357449 < baseStart_3357449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357452 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_3357452 : Nat := 118140960795 + 3357452 * 2 ^ 59
def prefixEnd_3357452 : Nat := 4983230072969 + 3 ^ 40 * 3357452 * 2
def baseEnd_3357452 : Nat := 1723986650399303187309365

theorem tailTrace_3357452 : CollatzResearch.WordTrace tailWord_3357452 prefixEnd_3357452 1723986650399303187309365 := by
  unfold tailWord_3357452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61228167316266142997717305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81637556421688190663623073 61228167316266142997717305)
  ·
    refine ⟨45921125487199607248287979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61228167316266142997717305 45921125487199607248287979)
    ·
      refine ⟨68881688230799410872431969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45921125487199607248287979 68881688230799410872431969)
      ·
        refine ⟨51661266173099558154323977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68881688230799410872431969 51661266173099558154323977)
        ·
          refine ⟨38745949629824668615742983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51661266173099558154323977 38745949629824668615742983)
          ·
            refine ⟨58118924444737002923614475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38745949629824668615742983 58118924444737002923614475)
            ·
              refine ⟨87178386667105504385421713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58118924444737002923614475 87178386667105504385421713)
              ·
                refine ⟨65383790000329128289066285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87178386667105504385421713 65383790000329128289066285)
                ·
                  refine ⟨24518921250123423108399857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65383790000329128289066285 24518921250123423108399857)
                  ·
                    refine ⟨18389190937592567331299893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24518921250123423108399857 18389190937592567331299893)
                    ·
                      refine ⟨1723986650399303187309365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18389190937592567331299893 1723986650399303187309365)
                      ·
                        rfl

theorem cell23_3357452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_3357452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357452 prefixEnd_3357452 := by exact prefixLift 3357452
  have htrace : WordTrace (prefixWord ++ tailWord_3357452) baseStart_3357452 baseEnd_3357452 := by
    simpa [prefixWord, tailWord_3357452, baseEnd_3357452] using wordTrace_append hprefix tailTrace_3357452
  have hstable : (prefixWord ++ tailWord_3357452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357452).length < 2 ^ (prefixWord ++ tailWord_3357452).sum := by decide
  have hdescent : baseEnd_3357452 < baseStart_3357452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357463 : List Nat := [1, 1, 3, 4, 3, 2, 1, 3, 5]
def baseStart_3357463 : Nat := 118140960795 + 3357463 * 2 ^ 59
def prefixEnd_3357463 : Nat := 4983230072969 + 3 ^ 40 * 3357463 * 2
def baseEnd_3357463 : Nat := 191554699854055849363535

theorem tailTrace_3357463 : CollatzResearch.WordTrace tailWord_3357463 prefixEnd_3357463 191554699854055849363535 := by
  unfold tailWord_3357463
  simp only [CollatzResearch.WordTrace]
  refine ⟨122456735835492434874085043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81637823890328289916056695 122456735835492434874085043)
  ·
    refine ⟨183685103753238652311127565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122456735835492434874085043 183685103753238652311127565)
    ·
      refine ⟨68881913907464494616672837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183685103753238652311127565 68881913907464494616672837)
      ·
        refine ⟨12915358857649592740626157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68881913907464494616672837 12915358857649592740626157)
        ·
          refine ⟨4843259571618597277734809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12915358857649592740626157 4843259571618597277734809)
          ·
            refine ⟨3632444678713947958301107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843259571618597277734809 3632444678713947958301107)
            ·
              refine ⟨5448667018070921937451661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632444678713947958301107 5448667018070921937451661)
              ·
                refine ⟨2043250131776595726544373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5448667018070921937451661 2043250131776595726544373)
                ·
                  refine ⟨191554699854055849363535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2043250131776595726544373 191554699854055849363535)
                  ·
                    rfl

theorem cell23_3357463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 3, 5].length) (baseStart_3357463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357463 prefixEnd_3357463 := by exact prefixLift 3357463
  have htrace : WordTrace (prefixWord ++ tailWord_3357463) baseStart_3357463 baseEnd_3357463 := by
    simpa [prefixWord, tailWord_3357463, baseEnd_3357463] using wordTrace_append hprefix tailTrace_3357463
  have hstable : (prefixWord ++ tailWord_3357463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357463).length < 2 ^ (prefixWord ++ tailWord_3357463).sum := by decide
  have hdescent : baseEnd_3357463 < baseStart_3357463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357476 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_3357476 : Nat := 118140960795 + 3357476 * 2 ^ 59
def prefixEnd_3357476 : Nat := 4983230072969 + 3 ^ 40 * 3357476 * 2
def baseEnd_3357476 : Nat := 574666324645003697803085

theorem tailTrace_3357476 : CollatzResearch.WordTrace tailWord_3357476 prefixEnd_3357476 574666324645003697803085 := by
  unfold tailWord_3357476
  simp only [CollatzResearch.WordTrace]
  refine ⟨61228604992222669047154141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81638139989630225396205521 61228604992222669047154141)
  ·
    refine ⟨22960726872083500892682803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61228604992222669047154141 22960726872083500892682803)
    ·
      refine ⟨34441090308125251339024205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22960726872083500892682803 34441090308125251339024205)
      ·
        refine ⟨12915408865546969252134077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34441090308125251339024205 12915408865546969252134077)
        ·
          refine ⟨4843278324580113469550279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12915408865546969252134077 4843278324580113469550279)
          ·
            refine ⟨7264917486870170204325419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843278324580113469550279 7264917486870170204325419)
            ·
              refine ⟨10897376230305255306488129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7264917486870170204325419 10897376230305255306488129)
              ·
                refine ⟨8173032172728941479866097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10897376230305255306488129 8173032172728941479866097)
                ·
                  refine ⟨6129774129546706109899573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173032172728941479866097 6129774129546706109899573)
                  ·
                    refine ⟨574666324645003697803085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6129774129546706109899573 574666324645003697803085)
                    ·
                      rfl

theorem cell23_3357476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_3357476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357476 prefixEnd_3357476 := by exact prefixLift 3357476
  have htrace : WordTrace (prefixWord ++ tailWord_3357476) baseStart_3357476 baseEnd_3357476 := by
    simpa [prefixWord, tailWord_3357476, baseEnd_3357476] using wordTrace_append hprefix tailTrace_3357476
  have hstable : (prefixWord ++ tailWord_3357476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357476).length < 2 ^ (prefixWord ++ tailWord_3357476).sum := by decide
  have hdescent : baseEnd_3357476 < baseStart_3357476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357486 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3357486 : Nat := 118140960795 + 3357486 * 2 ^ 59
def prefixEnd_3357486 : Nat := 4983230072969 + 3 ^ 40 * 3357486 * 2
def baseEnd_3357486 : Nat := 1724004108741556054284209

theorem tailTrace_3357486 : CollatzResearch.WordTrace tailWord_3357486 prefixEnd_3357486 1724004108741556054284209 := by
  unfold tailWord_3357486
  simp only [CollatzResearch.WordTrace]
  refine ⟨15307196839301138725271539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81638383142939406534781541 15307196839301138725271539)
  ·
    refine ⟨22960795258951708087907309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15307196839301138725271539 22960795258951708087907309)
    ·
      refine ⟨8610298222106890532965241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22960795258951708087907309 8610298222106890532965241)
      ·
        refine ⟨6457723666580167899723931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8610298222106890532965241 6457723666580167899723931)
        ·
          refine ⟨9686585499870251849585897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457723666580167899723931 9686585499870251849585897)
          ·
            refine ⟨7264939124902688887189423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9686585499870251849585897 7264939124902688887189423)
            ·
              refine ⟨10897408687354033330784135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7264939124902688887189423 10897408687354033330784135)
              ·
                refine ⟨16346113031031049996176203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10897408687354033330784135 16346113031031049996176203)
                ·
                  refine ⟨24519169546546574994264305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16346113031031049996176203 24519169546546574994264305)
                  ·
                    refine ⟨18389377159909931245698229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24519169546546574994264305 18389377159909931245698229)
                    ·
                      refine ⟨1724004108741556054284209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18389377159909931245698229 1724004108741556054284209)
                      ·
                        rfl

theorem cell23_3357486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3357486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357486 prefixEnd_3357486 := by exact prefixLift 3357486
  have htrace : WordTrace (prefixWord ++ tailWord_3357486) baseStart_3357486 baseEnd_3357486 := by
    simpa [prefixWord, tailWord_3357486, baseEnd_3357486] using wordTrace_append hprefix tailTrace_3357486
  have hstable : (prefixWord ++ tailWord_3357486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357486).length < 2 ^ (prefixWord ++ tailWord_3357486).sum := by decide
  have hdescent : baseEnd_3357486 < baseStart_3357486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357510 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_3357510 : Nat := 118140960795 + 3357510 * 2 ^ 59
def prefixEnd_3357510 : Nat := 4983230072969 + 3 ^ 40 * 3357510 * 2
def baseEnd_3357510 : Nat := 574672144092421320128033

theorem tailTrace_3357510 : CollatzResearch.WordTrace tailWord_3357510 prefixEnd_3357510 574672144092421320128033 := by
  unfold tailWord_3357510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826826564572567559407687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81638966710881441267363989 3826826564572567559407687)
  ·
    refine ⟨5740239846858851339111531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3826826564572567559407687 5740239846858851339111531)
    ·
      refine ⟨8610359770288277008667297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740239846858851339111531 8610359770288277008667297)
      ·
        refine ⟨6457769827716207756500473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8610359770288277008667297 6457769827716207756500473)
        ·
          refine ⟨4843327370787155817375355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6457769827716207756500473 4843327370787155817375355)
          ·
            refine ⟨7264991056180733726063033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843327370787155817375355 7264991056180733726063033)
            ·
              refine ⟨5448743292135550294547275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7264991056180733726063033 5448743292135550294547275)
              ·
                refine ⟨8173114938203325441820913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448743292135550294547275 8173114938203325441820913)
                ·
                  refine ⟨6129836203652494081365685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173114938203325441820913 6129836203652494081365685)
                  ·
                    refine ⟨574672144092421320128033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6129836203652494081365685 574672144092421320128033)
                    ·
                      rfl

theorem cell23_3357510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_3357510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357510 prefixEnd_3357510 := by exact prefixLift 3357510
  have htrace : WordTrace (prefixWord ++ tailWord_3357510) baseStart_3357510 baseEnd_3357510 := by
    simpa [prefixWord, tailWord_3357510, baseEnd_3357510] using wordTrace_append hprefix tailTrace_3357510
  have hstable : (prefixWord ++ tailWord_3357510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357510).length < 2 ^ (prefixWord ++ tailWord_3357510).sum := by decide
  have hdescent : baseEnd_3357510 < baseStart_3357510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357516 : List Nat := [2, 2, 1, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_3357516 : Nat := 118140960795 + 3357516 * 2 ^ 59
def prefixEnd_3357516 : Nat := 4983230072969 + 3 ^ 40 * 3357516 * 2
def baseEnd_3357516 : Nat := 1724019513161190936909071

theorem tailTrace_3357516 : CollatzResearch.WordTrace tailWord_3357516 prefixEnd_3357516 1724019513161190936909071 := by
  unfold tailWord_3357516
  simp only [CollatzResearch.WordTrace]
  refine ⟨61229334452150212462882201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81639112602866949950509601 61229334452150212462882201)
  ·
    refine ⟨45922000839112659347161651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61229334452150212462882201 45922000839112659347161651)
    ·
      refine ⟨68883001258668989020742477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45922000839112659347161651 68883001258668989020742477)
      ·
        refine ⟨25831125472000870882778429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68883001258668989020742477 25831125472000870882778429)
        ·
          refine ⟨9686672052000326581041911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25831125472000870882778429 9686672052000326581041911)
          ·
            refine ⟨14530008078000489871562867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686672052000326581041911 14530008078000489871562867)
            ·
              refine ⟨21795012117000734807344301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14530008078000489871562867 21795012117000734807344301)
              ·
                refine ⟨8173129543875275552754113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21795012117000734807344301 8173129543875275552754113)
                ·
                  refine ⟨6129847157906456664565585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173129543875275552754113 6129847157906456664565585)
                  ·
                    refine ⟨4597385368429842498424189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6129847157906456664565585 4597385368429842498424189)
                    ·
                      refine ⟨1724019513161190936909071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4597385368429842498424189 1724019513161190936909071)
                      ·
                        rfl

theorem cell23_3357516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_3357516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357516 prefixEnd_3357516 := by exact prefixLift 3357516
  have htrace : WordTrace (prefixWord ++ tailWord_3357516) baseStart_3357516 baseEnd_3357516 := by
    simpa [prefixWord, tailWord_3357516, baseEnd_3357516] using wordTrace_append hprefix tailTrace_3357516
  have hstable : (prefixWord ++ tailWord_3357516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357516).length < 2 ^ (prefixWord ++ tailWord_3357516).sum := by decide
  have hdescent : baseEnd_3357516 < baseStart_3357516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357540 : List Nat := [2, 3, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_3357540 : Nat := 118140960795 + 3357540 * 2 ^ 59
def prefixEnd_3357540 : Nat := 4983230072969 + 3 ^ 40 * 3357540 * 2
def baseEnd_3357540 : Nat := 574677278898966281002987

theorem tailTrace_3357540 : CollatzResearch.WordTrace tailWord_3357540 prefixEnd_3357540 574677278898966281002987 := by
  unfold tailWord_3357540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61229772128106738512319037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81639696170808984683092049 61229772128106738512319037)
  ·
    refine ⟨22961164548040026942119639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61229772128106738512319037 22961164548040026942119639)
    ·
      refine ⟨34441746822060040413179459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22961164548040026942119639 34441746822060040413179459)
      ·
        refine ⟨51662620233090060619769189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34441746822060040413179459 51662620233090060619769189)
        ·
          refine ⟨9686741293704386366206723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51662620233090060619769189 9686741293704386366206723)
          ·
            refine ⟨14530111940556579549310085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686741293704386366206723 14530111940556579549310085)
            ·
              refine ⟨2724395988854358665495641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14530111940556579549310085 2724395988854358665495641)
              ·
                refine ⟨2043296991640768999121731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724395988854358665495641 2043296991640768999121731)
                ·
                  refine ⟨3064945487461153498682597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043296991640768999121731 3064945487461153498682597)
                  ·
                    refine ⟨574677278898966281002987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3064945487461153498682597 574677278898966281002987)
                    ·
                      rfl

theorem cell23_3357540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_3357540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357540 prefixEnd_3357540 := by exact prefixLift 3357540
  have htrace : WordTrace (prefixWord ++ tailWord_3357540) baseStart_3357540 baseEnd_3357540 := by
    simpa [prefixWord, tailWord_3357540, baseEnd_3357540] using wordTrace_append hprefix tailTrace_3357540
  have hstable : (prefixWord ++ tailWord_3357540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357540).length < 2 ^ (prefixWord ++ tailWord_3357540).sum := by decide
  have hdescent : baseEnd_3357540 < baseStart_3357540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357573 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_3357573 : Nat := 118140960795 + 3357573 * 2 ^ 59
def prefixEnd_3357573 : Nat := 4983230072969 + 3 ^ 40 * 3357573 * 2
def baseEnd_3357573 : Nat := 1724048781558497213896309

theorem tailTrace_3357573 : CollatzResearch.WordTrace tailWord_3357573 prefixEnd_3357573 1724048781558497213896309 := by
  unfold tailWord_3357573
  simp only [CollatzResearch.WordTrace]
  refine ⟨122460747865093923660589373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81640498576729282440392915 122460747865093923660589373)
  ·
    refine ⟨45922780449410221372721015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122460747865093923660589373 45922780449410221372721015)
    ·
      refine ⟨68884170674115332059081523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45922780449410221372721015 68884170674115332059081523)
      ·
        refine ⟨103326256011172998088622285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68884170674115332059081523 103326256011172998088622285)
        ·
          refine ⟨38747346004189874283233357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103326256011172998088622285 38747346004189874283233357)
          ·
            refine ⟨14530254751571202856212509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38747346004189874283233357 14530254751571202856212509)
            ·
              refine ⟨5448845531839201071079691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14530254751571202856212509 5448845531839201071079691)
              ·
                refine ⟨8173268297758801606619537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448845531839201071079691 8173268297758801606619537)
                ·
                  refine ⟨6129951223319101204964653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8173268297758801606619537 6129951223319101204964653)
                  ·
                    refine ⟨2298731708744662951861745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6129951223319101204964653 2298731708744662951861745)
                    ·
                      refine ⟨1724048781558497213896309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298731708744662951861745 1724048781558497213896309)
                      ·
                        rfl

theorem cell23_3357573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_3357573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357573 prefixEnd_3357573 := by exact prefixLift 3357573
  have htrace : WordTrace (prefixWord ++ tailWord_3357573) baseStart_3357573 baseEnd_3357573 := by
    simpa [prefixWord, tailWord_3357573, baseEnd_3357573] using wordTrace_append hprefix tailTrace_3357573
  have hstable : (prefixWord ++ tailWord_3357573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357573).length < 2 ^ (prefixWord ++ tailWord_3357573).sum := by decide
  have hdescent : baseEnd_3357573 < baseStart_3357573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357579 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 1, 6]
def baseStart_3357579 : Nat := 118140960795 + 3357579 * 2 ^ 59
def prefixEnd_3357579 : Nat := 4983230072969 + 3 ^ 40 * 3357579 * 2
def baseEnd_3357579 : Nat := 574683954147474730140427

theorem tailTrace_3357579 : CollatzResearch.WordTrace tailWord_3357579 prefixEnd_3357579 574683954147474730140427 := by
  unfold tailWord_3357579
  simp only [CollatzResearch.WordTrace]
  refine ⟨122460966703072186685307791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81640644468714791123538527 122460966703072186685307791)
  ·
    refine ⟨183691450054608280027961687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122460966703072186685307791 183691450054608280027961687)
    ·
      refine ⟨275537175081912420041942531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183691450054608280027961687 275537175081912420041942531)
      ·
        refine ⟨413305762622868630062913797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275537175081912420041942531 413305762622868630062913797)
        ·
          refine ⟨77494830491787868136796337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413305762622868630062913797 77494830491787868136796337)
          ·
            refine ⟨58121122868840901102597253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77494830491787868136796337 58121122868840901102597253)
            ·
              refine ⟨10897710537907668956736985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58121122868840901102597253 10897710537907668956736985)
              ·
                refine ⟨8173282903430751717552739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10897710537907668956736985 8173282903430751717552739)
                ·
                  refine ⟨12259924355146127576329109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173282903430751717552739 12259924355146127576329109)
                  ·
                    refine ⟨574683954147474730140427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12259924355146127576329109 574683954147474730140427)
                    ·
                      rfl

theorem cell23_3357579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 1, 6].length) (baseStart_3357579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357579 prefixEnd_3357579 := by exact prefixLift 3357579
  have htrace : WordTrace (prefixWord ++ tailWord_3357579) baseStart_3357579 baseEnd_3357579 := by
    simpa [prefixWord, tailWord_3357579, baseEnd_3357579] using wordTrace_append hprefix tailTrace_3357579
  have hstable : (prefixWord ++ tailWord_3357579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357579).length < 2 ^ (prefixWord ++ tailWord_3357579).sum := by decide
  have hdescent : baseEnd_3357579 < baseStart_3357579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357603 : List Nat := [1, 1, 1, 4, 1, 2, 3, 3, 3, 2, 2]
def baseStart_3357603 : Nat := 118140960795 + 3357603 * 2 ^ 59
def prefixEnd_3357603 : Nat := 4983230072969 + 3 ^ 40 * 3357603 * 2
def baseEnd_3357603 : Nat := 1724064185978132096521171

theorem tailTrace_3357603 : CollatzResearch.WordTrace tailWord_3357603 prefixEnd_3357603 1724064185978132096521171 := by
  unfold tailWord_3357603
  simp only [CollatzResearch.WordTrace]
  refine ⟨122461842054985238784181463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81641228036656825856120975 122461842054985238784181463)
  ·
    refine ⟨183692763082477858176272195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122461842054985238784181463 183692763082477858176272195)
    ·
      refine ⟨275539144623716787264408293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183692763082477858176272195 275539144623716787264408293)
      ·
        refine ⟨51663589616946897612076555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275539144623716787264408293 51663589616946897612076555)
        ·
          refine ⟨77495384425420346418114833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51663589616946897612076555 77495384425420346418114833)
          ·
            refine ⟨58121538319065259813586125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77495384425420346418114833 58121538319065259813586125)
            ·
              refine ⟨21795576869649472430094797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58121538319065259813586125 21795576869649472430094797)
              ·
                refine ⟨8173341326118552161285549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21795576869649472430094797 8173341326118552161285549)
                ·
                  refine ⟨3065002997294457060482081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8173341326118552161285549 3065002997294457060482081)
                  ·
                    refine ⟨2298752247970842795361561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065002997294457060482081 2298752247970842795361561)
                    ·
                      refine ⟨1724064185978132096521171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298752247970842795361561 1724064185978132096521171)
                      ·
                        rfl

theorem cell23_3357603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_3357603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357603 prefixEnd_3357603 := by exact prefixLift 3357603
  have htrace : WordTrace (prefixWord ++ tailWord_3357603) baseStart_3357603 baseEnd_3357603 := by
    simpa [prefixWord, tailWord_3357603, baseEnd_3357603] using wordTrace_append hprefix tailTrace_3357603
  have hstable : (prefixWord ++ tailWord_3357603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357603).length < 2 ^ (prefixWord ++ tailWord_3357603).sum := by decide
  have hdescent : baseEnd_3357603 < baseStart_3357603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357620 : List Nat := [2, 5, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_3357620 : Nat := 118140960795 + 3357620 * 2 ^ 59
def prefixEnd_3357620 : Nat := 4983230072969 + 3 ^ 40 * 3357620 * 2
def baseEnd_3357620 : Nat := 1724072915149258530008593

theorem tailTrace_3357620 : CollatzResearch.WordTrace tailWord_3357620 prefixEnd_3357620 1724072915149258530008593 := by
  unfold tailWord_3357620
  simp only [CollatzResearch.WordTrace]
  refine ⟨61231231047961825343775157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81641641397282433791700209 61231231047961825343775157)
  ·
    refine ⟨5740427910746421125978921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61231231047961825343775157 5740427910746421125978921)
    ·
      refine ⟨4305320933059815844484191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5740427910746421125978921 4305320933059815844484191)
      ·
        refine ⟨6457981399589723766726287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305320933059815844484191 6457981399589723766726287)
        ·
          refine ⟨9686972099384585650089431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457981399589723766726287 9686972099384585650089431)
          ·
            refine ⟨14530458149076878475134147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9686972099384585650089431 14530458149076878475134147)
            ·
              refine ⟨21795687223615317712701221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14530458149076878475134147 21795687223615317712701221)
              ·
                refine ⟨4086691354427872071131479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21795687223615317712701221 4086691354427872071131479)
                ·
                  refine ⟨6130037031641808106697219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086691354427872071131479 6130037031641808106697219)
                  ·
                    refine ⟨9195055547462712160045829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6130037031641808106697219 9195055547462712160045829)
                    ·
                      refine ⟨1724072915149258530008593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9195055547462712160045829 1724072915149258530008593)
                      ·
                        rfl

theorem cell23_3357620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_3357620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357620 prefixEnd_3357620 := by exact prefixLift 3357620
  have htrace : WordTrace (prefixWord ++ tailWord_3357620) baseStart_3357620 baseEnd_3357620 := by
    simpa [prefixWord, tailWord_3357620, baseEnd_3357620] using wordTrace_append hprefix tailTrace_3357620
  have hstable : (prefixWord ++ tailWord_3357620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357620).length < 2 ^ (prefixWord ++ tailWord_3357620).sum := by decide
  have hdescent : baseEnd_3357620 < baseStart_3357620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357649 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3357649 : Nat := 118140960795 + 3357649 * 2 ^ 59
def prefixEnd_3357649 : Nat := 4983230072969 + 3 ^ 40 * 3357649 * 2
def baseEnd_3357649 : Nat := 1724087806088238916545959

theorem tailTrace_3357649 : CollatzResearch.WordTrace tailWord_3357649 prefixEnd_3357649 1724087806088238916545959 := by
  unfold tailWord_3357649
  simp only [CollatzResearch.WordTrace]
  refine ⟨122463519812818588640356001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81642346541879059093570667 122463519812818588640356001)
  ·
    refine ⟨91847639859613941480267001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122463519812818588640356001 91847639859613941480267001)
    ·
      refine ⟨68885729894710456110200251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91847639859613941480267001 68885729894710456110200251)
      ·
        refine ⟨103328594842065684165300377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68885729894710456110200251 103328594842065684165300377)
        ·
          refine ⟨77496446131549263123975283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103328594842065684165300377 77496446131549263123975283)
          ·
            refine ⟨116244669197323894685962925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77496446131549263123975283 116244669197323894685962925)
            ·
              refine ⟨43591750948996460507236097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116244669197323894685962925 43591750948996460507236097)
              ·
                refine ⟨32693813211747345380427073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43591750948996460507236097 32693813211747345380427073)
                ·
                  refine ⟨24520359908810509035320305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32693813211747345380427073 24520359908810509035320305)
                  ·
                    refine ⟨18390269931607881776490229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24520359908810509035320305 18390269931607881776490229)
                    ·
                      refine ⟨1724087806088238916545959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18390269931607881776490229 1724087806088238916545959)
                      ·
                        rfl

theorem cell23_3357649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3357649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357649 prefixEnd_3357649 := by exact prefixLift 3357649
  have htrace : WordTrace (prefixWord ++ tailWord_3357649) baseStart_3357649 baseEnd_3357649 := by
    simpa [prefixWord, tailWord_3357649, baseEnd_3357649] using wordTrace_append hprefix tailTrace_3357649
  have hstable : (prefixWord ++ tailWord_3357649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357649).length < 2 ^ (prefixWord ++ tailWord_3357649).sum := by decide
  have hdescent : baseEnd_3357649 < baseStart_3357649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357654 : List Nat := [5, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3357654 : Nat := 118140960795 + 3357654 * 2 ^ 59
def prefixEnd_3357654 : Nat := 4983230072969 + 3 ^ 40 * 3357654 * 2
def baseEnd_3357654 : Nat := 1724090373491511396983437

theorem tailTrace_3357654 : CollatzResearch.WordTrace tailWord_3357654 prefixEnd_3357654 1724090373491511396983437 := by
  unfold tailWord_3357654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653981386112529655893001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81642468118533649662858677 7653981386112529655893001)
  ·
    refine ⟨5740486039584397241919751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7653981386112529655893001 5740486039584397241919751)
    ·
      refine ⟨8610729059376595862879627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740486039584397241919751 8610729059376595862879627)
      ·
        refine ⟨12916093589064893794319441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610729059376595862879627 12916093589064893794319441)
        ·
          refine ⟨9687070191798670345739581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12916093589064893794319441 9687070191798670345739581)
          ·
            refine ⟨3632651321924501379652343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9687070191798670345739581 3632651321924501379652343)
            ·
              refine ⟨5448976982886752069478515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632651321924501379652343 5448976982886752069478515)
              ·
                refine ⟨8173465474330128104217773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5448976982886752069478515 8173465474330128104217773)
                ·
                  refine ⟨3065049552873798039081665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8173465474330128104217773 3065049552873798039081665)
                  ·
                    refine ⟨2298787164655348529311249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065049552873798039081665 2298787164655348529311249)
                    ·
                      refine ⟨1724090373491511396983437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298787164655348529311249 1724090373491511396983437)
                      ·
                        rfl

theorem cell23_3357654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3357654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357654 prefixEnd_3357654 := by exact prefixLift 3357654
  have htrace : WordTrace (prefixWord ++ tailWord_3357654) baseStart_3357654 baseEnd_3357654 := by
    simpa [prefixWord, tailWord_3357654, baseEnd_3357654] using wordTrace_append hprefix tailTrace_3357654
  have hstable : (prefixWord ++ tailWord_3357654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357654).length < 2 ^ (prefixWord ++ tailWord_3357654).sum := by decide
  have hdescent : baseEnd_3357654 < baseStart_3357654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357684 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3357684 : Nat := 118140960795 + 3357684 * 2 ^ 59
def prefixEnd_3357684 : Nat := 4983230072969 + 3 ^ 40 * 3357684 * 2
def baseEnd_3357684 : Nat := 1724105777911146279608299

theorem tailTrace_3357684 : CollatzResearch.WordTrace tailWord_3357684 prefixEnd_3357684 1724105777911146279608299 := by
  unfold tailWord_3357684
  simp only [CollatzResearch.WordTrace]
  refine ⟨61232398183845894808940053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81643197578461193078586737 61232398183845894808940053)
  ·
    refine ⟨2870268664867776319169065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61232398183845894808940053 2870268664867776319169065)
    ·
      refine ⟨2152701498650832239376799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2870268664867776319169065 2152701498650832239376799)
      ·
        refine ⟨3229052247976248359065199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152701498650832239376799 3229052247976248359065199)
        ·
          refine ⟨4843578371964372538597799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229052247976248359065199 4843578371964372538597799)
          ·
            refine ⟨7265367557946558807896699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843578371964372538597799 7265367557946558807896699)
            ·
              refine ⟨10898051336919838211845049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265367557946558807896699 10898051336919838211845049)
              ·
                refine ⟨8173538502689878658883787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898051336919838211845049 8173538502689878658883787)
                ·
                  refine ⟨12260307754034817988325681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8173538502689878658883787 12260307754034817988325681)
                  ·
                    refine ⟨9195230815526113491244261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12260307754034817988325681 9195230815526113491244261)
                    ·
                      refine ⟨1724105777911146279608299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9195230815526113491244261 1724105777911146279608299)
                      ·
                        rfl

theorem cell23_3357684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3357684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357684 prefixEnd_3357684 := by exact prefixLift 3357684
  have htrace : WordTrace (prefixWord ++ tailWord_3357684) baseStart_3357684 baseEnd_3357684 := by
    simpa [prefixWord, tailWord_3357684, baseEnd_3357684] using wordTrace_append hprefix tailTrace_3357684
  have hstable : (prefixWord ++ tailWord_3357684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357684).length < 2 ^ (prefixWord ++ tailWord_3357684).sum := by decide
  have hdescent : baseEnd_3357684 < baseStart_3357684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357697 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_3357697 : Nat := 118140960795 + 3357697 * 2 ^ 59
def prefixEnd_3357697 : Nat := 4983230072969 + 3 ^ 40 * 3357697 * 2
def baseEnd_3357697 : Nat := 1724112453159654728745739

theorem tailTrace_3357697 : CollatzResearch.WordTrace tailWord_3357697 prefixEnd_3357697 1724112453159654728745739 := by
  unfold tailWord_3357697
  simp only [CollatzResearch.WordTrace]
  refine ⟨122465270516644692838103345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81643513677763128558735563 122465270516644692838103345)
  ·
    refine ⟨91848952887483519628577509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122465270516644692838103345 91848952887483519628577509)
    ·
      refine ⟨17221678666403159930358283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91848952887483519628577509 17221678666403159930358283)
      ·
        refine ⟨25832517999604739895537425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17221678666403159930358283 25832517999604739895537425)
        ·
          refine ⟨19374388499703554921653069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25832517999604739895537425 19374388499703554921653069)
          ·
            refine ⟨7265395687388833095619901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19374388499703554921653069 7265395687388833095619901)
            ·
              refine ⟨2724523382770812410857463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7265395687388833095619901 2724523382770812410857463)
              ·
                refine ⟨4086785074156218616286195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724523382770812410857463 4086785074156218616286195)
                ·
                  refine ⟨6130177611234327924429293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4086785074156218616286195 6130177611234327924429293)
                  ·
                    refine ⟨2298816604212872971660985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6130177611234327924429293 2298816604212872971660985)
                    ·
                      refine ⟨1724112453159654728745739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298816604212872971660985 1724112453159654728745739)
                      ·
                        rfl

theorem cell23_3357697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_3357697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357697 prefixEnd_3357697 := by exact prefixLift 3357697
  have htrace : WordTrace (prefixWord ++ tailWord_3357697) baseStart_3357697 baseEnd_3357697 := by
    simpa [prefixWord, tailWord_3357697, baseEnd_3357697] using wordTrace_append hprefix tailTrace_3357697
  have hstable : (prefixWord ++ tailWord_3357697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357697).length < 2 ^ (prefixWord ++ tailWord_3357697).sum := by decide
  have hdescent : baseEnd_3357697 < baseStart_3357697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357746 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_3357746 : Nat := 118140960795 + 3357746 * 2 ^ 59
def prefixEnd_3357746 : Nat := 4983230072969 + 3 ^ 40 * 3357746 * 2
def baseEnd_3357746 : Nat := 574712537903908345677671

theorem tailTrace_3357746 : CollatzResearch.WordTrace tailWord_3357746 prefixEnd_3357746 574712537903908345677671 := by
  unfold tailWord_3357746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30616764423366793551659273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81644705128978116137758061 30616764423366793551659273)
  ·
    refine ⟨22962573317525095163744455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30616764423366793551659273 22962573317525095163744455)
    ·
      refine ⟨34443859976287642745616683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22962573317525095163744455 34443859976287642745616683)
      ·
        refine ⟨51665789964431464118425025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34443859976287642745616683 51665789964431464118425025)
        ·
          refine ⟨38749342473323598088818769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51665789964431464118425025 38749342473323598088818769)
          ·
            refine ⟨29062006854992698566614077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38749342473323598088818769 29062006854992698566614077)
            ·
              refine ⟨10898252570622261962480279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29062006854992698566614077 10898252570622261962480279)
              ·
                refine ⟨16347378855933392943720419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10898252570622261962480279 16347378855933392943720419)
                ·
                  refine ⟨24521068283900089415580629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16347378855933392943720419 24521068283900089415580629)
                  ·
                    refine ⟨574712537903908345677671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24521068283900089415580629 574712537903908345677671)
                    ·
                      rfl

theorem cell23_3357746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_3357746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357746 prefixEnd_3357746 := by exact prefixLift 3357746
  have htrace : WordTrace (prefixWord ++ tailWord_3357746) baseStart_3357746 baseEnd_3357746 := by
    simpa [prefixWord, tailWord_3357746, baseEnd_3357746] using wordTrace_append hprefix tailTrace_3357746
  have hstable : (prefixWord ++ tailWord_3357746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357746).length < 2 ^ (prefixWord ++ tailWord_3357746).sum := by decide
  have hdescent : baseEnd_3357746 < baseStart_3357746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357750 : List Nat := [5, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_3357750 : Nat := 118140960795 + 3357750 * 2 ^ 59
def prefixEnd_3357750 : Nat := 4983230072969 + 3 ^ 40 * 3357750 * 2
def baseEnd_3357750 : Nat := 191571074181593669042555

theorem tailTrace_3357750 : CollatzResearch.WordTrace tailWord_3357750 prefixEnd_3357750 191571074181593669042555 := by
  unfold tailWord_3357750
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654200224090792680611419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81644802390301788593188469 7654200224090792680611419)
  ·
    refine ⟨11481300336136189020917129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7654200224090792680611419 11481300336136189020917129)
    ·
      refine ⟨8610975252102141765687847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11481300336136189020917129 8610975252102141765687847)
      ·
        refine ⟨12916462878153212648531771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610975252102141765687847 12916462878153212648531771)
        ·
          refine ⟨19374694317229818972797657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12916462878153212648531771 19374694317229818972797657)
          ·
            refine ⟨14531020737922364229598243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19374694317229818972797657 14531020737922364229598243)
            ·
              refine ⟨21796531106883546344397365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14531020737922364229598243 21796531106883546344397365)
              ·
                refine ⟨2043424791270332469787253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21796531106883546344397365 2043424791270332469787253)
                ·
                  refine ⟨191571074181593669042555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2043424791270332469787253 191571074181593669042555)
                  ·
                    rfl

theorem cell23_3357750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_3357750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357750 prefixEnd_3357750 := by exact prefixLift 3357750
  have htrace : WordTrace (prefixWord ++ tailWord_3357750) baseStart_3357750 baseEnd_3357750 := by
    simpa [prefixWord, tailWord_3357750, baseEnd_3357750] using wordTrace_append hprefix tailTrace_3357750
  have hstable : (prefixWord ++ tailWord_3357750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357750).length < 2 ^ (prefixWord ++ tailWord_3357750).sum := by decide
  have hdescent : baseEnd_3357750 < baseStart_3357750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357761 : List Nat := [1, 2, 5, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_3357761 : Nat := 118140960795 + 3357761 * 2 ^ 59
def prefixEnd_3357761 : Nat := 4983230072969 + 3 ^ 40 * 3357761 * 2
def baseEnd_3357761 : Nat := 1724145315921542478345445

theorem tailTrace_3357761 : CollatzResearch.WordTrace tailWord_3357761 prefixEnd_3357761 1724145315921542478345445 := by
  unfold tailWord_3357761
  simp only [CollatzResearch.WordTrace]
  refine ⟨122467604788412831768433137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81645069858941887845622091 122467604788412831768433137)
  ·
    refine ⟨91850703591309623826324853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122467604788412831768433137 91850703591309623826324853)
    ·
      refine ⟨8611003461685277233717955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91850703591309623826324853 8611003461685277233717955)
      ·
        refine ⟨12916505192527915850576933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611003461685277233717955 12916505192527915850576933)
        ·
          refine ⟨2421844723598984221983175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12916505192527915850576933 2421844723598984221983175)
          ·
            refine ⟨3632767085398476332974763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2421844723598984221983175 3632767085398476332974763)
            ·
              refine ⟨5449150628097714499462145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632767085398476332974763 5449150628097714499462145)
              ·
                refine ⟨4086862971073285874596609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5449150628097714499462145 4086862971073285874596609)
                ·
                  refine ⟨3065147228304964405947457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4086862971073285874596609 3065147228304964405947457)
                  ·
                    refine ⟨2298860421228723304460593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065147228304964405947457 2298860421228723304460593)
                    ·
                      refine ⟨1724145315921542478345445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298860421228723304460593 1724145315921542478345445)
                      ·
                        rfl

theorem cell23_3357761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_3357761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357761 prefixEnd_3357761 := by exact prefixLift 3357761
  have htrace : WordTrace (prefixWord ++ tailWord_3357761) baseStart_3357761 baseEnd_3357761 := by
    simpa [prefixWord, tailWord_3357761, baseEnd_3357761] using wordTrace_append hprefix tailTrace_3357761
  have hstable : (prefixWord ++ tailWord_3357761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357761).length < 2 ^ (prefixWord ++ tailWord_3357761).sum := by decide
  have hdescent : baseEnd_3357761 < baseStart_3357761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357793 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_3357793 : Nat := 118140960795 + 3357793 * 2 ^ 59
def prefixEnd_3357793 : Nat := 4983230072969 + 3 ^ 40 * 3357793 * 2
def baseEnd_3357793 : Nat := 574720582434162117715099

theorem tailTrace_3357793 : CollatzResearch.WordTrace tailWord_3357793 prefixEnd_3357793 574720582434162117715099 := by
  unfold tailWord_3357793
  simp only [CollatzResearch.WordTrace]
  refine ⟨122468771924296901233598033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81645847949531267489065355 122468771924296901233598033)
  ·
    refine ⟨91851578943222675925198525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122468771924296901233598033 91851578943222675925198525)
    ·
      refine ⟨34444342103708503471949447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91851578943222675925198525 34444342103708503471949447)
      ·
        refine ⟨51666513155562755207924171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34444342103708503471949447 51666513155562755207924171)
        ·
          refine ⟨77499769733344132811886257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51666513155562755207924171 77499769733344132811886257)
          ·
            refine ⟨58124827300008099608914693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77499769733344132811886257 58124827300008099608914693)
            ·
              refine ⟨10898405118751518676671505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58124827300008099608914693 10898405118751518676671505)
              ·
                refine ⟨8173803839063639007503629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898405118751518676671505 8173803839063639007503629)
                ·
                  refine ⟨3065176439648864627813861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8173803839063639007503629 3065176439648864627813861)
                  ·
                    refine ⟨574720582434162117715099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065176439648864627813861 574720582434162117715099)
                    ·
                      rfl

theorem cell23_3357793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_3357793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357793 prefixEnd_3357793 := by exact prefixLift 3357793
  have htrace : WordTrace (prefixWord ++ tailWord_3357793) baseStart_3357793 baseEnd_3357793 := by
    simpa [prefixWord, tailWord_3357793, baseEnd_3357793] using wordTrace_append hprefix tailTrace_3357793
  have hstable : (prefixWord ++ tailWord_3357793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357793).length < 2 ^ (prefixWord ++ tailWord_3357793).sum := by decide
  have hdescent : baseEnd_3357793 < baseStart_3357793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357796 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_3357796 : Nat := 118140960795 + 3357796 * 2 ^ 59
def prefixEnd_3357796 : Nat := 4983230072969 + 3 ^ 40 * 3357796 * 2
def baseEnd_3357796 : Nat := 1724163287744449841407783

theorem tailTrace_3357796 : CollatzResearch.WordTrace tailWord_3357796 prefixEnd_3357796 1724163287744449841407783 := by
  unfold tailWord_3357796
  simp only [CollatzResearch.WordTrace]
  refine ⟨61234440671643016372978621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81645920895524021830638161 61234440671643016372978621)
  ·
    refine ⟨22962915251866131139866983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61234440671643016372978621 22962915251866131139866983)
    ·
      refine ⟨34444372877799196709800475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22962915251866131139866983 34444372877799196709800475)
      ·
        refine ⟨51666559316698795064700713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34444372877799196709800475 51666559316698795064700713)
        ·
          refine ⟨38749919487524096298525535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51666559316698795064700713 38749919487524096298525535)
          ·
            refine ⟨58124879231286144447788303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38749919487524096298525535 58124879231286144447788303)
            ·
              refine ⟨87187318846929216671682455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58124879231286144447788303 87187318846929216671682455)
              ·
                refine ⟨130780978270393825007523683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87187318846929216671682455 130780978270393825007523683)
                ·
                  refine ⟨196171467405590737511285525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130780978270393825007523683 196171467405590737511285525)
                  ·
                    refine ⟨9195537534637065820841509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 196171467405590737511285525 9195537534637065820841509)
                    ·
                      refine ⟨1724163287744449841407783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9195537534637065820841509 1724163287744449841407783)
                      ·
                        rfl

theorem cell23_3357796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_3357796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357796 prefixEnd_3357796 := by exact prefixLift 3357796
  have htrace : WordTrace (prefixWord ++ tailWord_3357796) baseStart_3357796 baseEnd_3357796 := by
    simpa [prefixWord, tailWord_3357796, baseEnd_3357796] using wordTrace_append hprefix tailTrace_3357796
  have hstable : (prefixWord ++ tailWord_3357796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357796).length < 2 ^ (prefixWord ++ tailWord_3357796).sum := by decide
  have hdescent : baseEnd_3357796 < baseStart_3357796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357827 : List Nat := [1, 1, 1, 3, 3, 2, 5, 2, 1, 4]
def baseStart_3357827 : Nat := 118140960795 + 3357827 * 2 ^ 59
def prefixEnd_3357827 : Nat := 4983230072969 + 3 ^ 40 * 3357827 * 2
def baseEnd_3357827 : Nat := 574726401881579740040047

theorem tailTrace_3357827 : CollatzResearch.WordTrace tailWord_3357827 prefixEnd_3357827 574726401881579740040047 := by
  unfold tailWord_3357827
  simp only [CollatzResearch.WordTrace]
  refine ⟨122470012006173725040335735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81646674670782483360223823 122470012006173725040335735)
  ·
    refine ⟨183705018009260587560503603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122470012006173725040335735 183705018009260587560503603)
    ·
      refine ⟨275557527013890881340755405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183705018009260587560503603 275557527013890881340755405)
      ·
        refine ⟨103334072630209080502783277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275557527013890881340755405 103334072630209080502783277)
        ·
          refine ⟨38750277236328405188543729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103334072630209080502783277 38750277236328405188543729)
          ·
            refine ⟨29062707927246303891407797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38750277236328405188543729 29062707927246303891407797)
            ·
              refine ⟨2724628868179340989819481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29062707927246303891407797 2724628868179340989819481)
              ·
                refine ⟨2043471651134505742364611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724628868179340989819481 2043471651134505742364611)
                ·
                  refine ⟨3065207476701758613546917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043471651134505742364611 3065207476701758613546917)
                  ·
                    refine ⟨574726401881579740040047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065207476701758613546917 574726401881579740040047)
                    ·
                      rfl

theorem cell23_3357827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 1, 4].length) (baseStart_3357827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357827 prefixEnd_3357827 := by exact prefixLift 3357827
  have htrace : WordTrace (prefixWord ++ tailWord_3357827) baseStart_3357827 baseEnd_3357827 := by
    simpa [prefixWord, tailWord_3357827, baseEnd_3357827] using wordTrace_append hprefix tailTrace_3357827
  have hstable : (prefixWord ++ tailWord_3357827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357827).length < 2 ^ (prefixWord ++ tailWord_3357827).sum := by decide
  have hdescent : baseEnd_3357827 < baseStart_3357827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357843 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 3, 5, 2]
def baseStart_3357843 : Nat := 118140960795 + 3357843 * 2 ^ 59
def prefixEnd_3357843 : Nat := 4983230072969 + 3 ^ 40 * 3357843 * 2
def baseEnd_3357843 : Nat := 1724187421335211157520067

theorem tailTrace_3357843 : CollatzResearch.WordTrace tailWord_3357843 prefixEnd_3357843 1724187421335211157520067 := by
  unfold tailWord_3357843
  simp only [CollatzResearch.WordTrace]
  refine ⟨122470595574115759772918183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81647063716077173181945455 122470595574115759772918183)
  ·
    refine ⟨183705893361173639659377275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122470595574115759772918183 183705893361173639659377275)
    ·
      refine ⟨275558840041760459489065913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183705893361173639659377275 275558840041760459489065913)
      ·
        refine ⟨206669130031320344616799435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275558840041760459489065913 206669130031320344616799435)
        ·
          refine ⟨310003695046980516925199153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206669130031320344616799435 310003695046980516925199153)
          ·
            refine ⟨232502771285235387693899365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310003695046980516925199153 232502771285235387693899365)
            ·
              refine ⟨43594269615981635192606131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232502771285235387693899365 43594269615981635192606131)
              ·
                refine ⟨65391404423972452788909197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43594269615981635192606131 65391404423972452788909197)
                ·
                  refine ⟨24521776658989669795840949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65391404423972452788909197 24521776658989669795840949)
                  ·
                    refine ⟨2298916561780281543360089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24521776658989669795840949 2298916561780281543360089)
                    ·
                      refine ⟨1724187421335211157520067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298916561780281543360089 1724187421335211157520067)
                      ·
                        rfl

theorem cell23_3357843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 5, 2].length) (baseStart_3357843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357843 prefixEnd_3357843 := by exact prefixLift 3357843
  have htrace : WordTrace (prefixWord ++ tailWord_3357843) baseStart_3357843 baseEnd_3357843 := by
    simpa [prefixWord, tailWord_3357843, baseEnd_3357843] using wordTrace_append hprefix tailTrace_3357843
  have hstable : (prefixWord ++ tailWord_3357843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357843).length < 2 ^ (prefixWord ++ tailWord_3357843).sum := by decide
  have hdescent : baseEnd_3357843 < baseStart_3357843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357853 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_3357853 : Nat := 118140960795 + 3357853 * 2 ^ 59
def prefixEnd_3357853 : Nat := 4983230072969 + 3 ^ 40 * 3357853 * 2
def baseEnd_3357853 : Nat := 574730852047252039465007

theorem tailTrace_3357853 : CollatzResearch.WordTrace tailWord_3357853 prefixEnd_3357853 574730852047252039465007 := by
  unfold tailWord_3357853
  simp only [CollatzResearch.WordTrace]
  refine ⟨122470960304079531480782213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81647306869386354320521475 122470960304079531480782213)
  ·
    refine ⟨22963305057014912152646665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122470960304079531480782213 22963305057014912152646665)
    ·
      refine ⟨17222478792761184114484999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22963305057014912152646665 17222478792761184114484999)
      ·
        refine ⟨25833718189141776171727499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17222478792761184114484999 25833718189141776171727499)
        ·
          refine ⟨38750577283712664257591249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25833718189141776171727499 38750577283712664257591249)
          ·
            refine ⟨29062932962784498193193437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38750577283712664257591249 29062932962784498193193437)
            ·
              refine ⟨10898599861044186822447539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29062932962784498193193437 10898599861044186822447539)
              ·
                refine ⟨16347899791566280233671309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10898599861044186822447539 16347899791566280233671309)
                ·
                  refine ⟨6130462421837355087626741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16347899791566280233671309 6130462421837355087626741)
                  ·
                    refine ⟨574730852047252039465007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6130462421837355087626741 574730852047252039465007)
                    ·
                      rfl

theorem cell23_3357853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_3357853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357853 prefixEnd_3357853 := by exact prefixLift 3357853
  have htrace : WordTrace (prefixWord ++ tailWord_3357853) baseStart_3357853 baseEnd_3357853 := by
    simpa [prefixWord, tailWord_3357853, baseEnd_3357853] using wordTrace_append hprefix tailTrace_3357853
  have hstable : (prefixWord ++ tailWord_3357853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357853).length < 2 ^ (prefixWord ++ tailWord_3357853).sum := by decide
  have hdescent : baseEnd_3357853 < baseStart_3357853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357884 : List Nat := [2, 2, 2, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_3357884 : Nat := 118140960795 + 3357884 * 2 ^ 59
def prefixEnd_3357884 : Nat := 4983230072969 + 3 ^ 40 * 3357884 * 2
def baseEnd_3357884 : Nat := 1724208474042045497107379

theorem tailTrace_3357884 : CollatzResearch.WordTrace tailWord_3357884 prefixEnd_3357884 1724208474042045497107379 := by
  unfold tailWord_3357884
  simp only [CollatzResearch.WordTrace]
  refine ⟨61236045483483611887580353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81648060644644815850107137 61236045483483611887580353)
  ·
    refine ⟨45927034112612708915685265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61236045483483611887580353 45927034112612708915685265)
    ·
      refine ⟨34445275584459531686763949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45927034112612708915685265 34445275584459531686763949)
      ·
        refine ⟨12916978344172324382536481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34445275584459531686763949 12916978344172324382536481)
        ·
          refine ⟨9687733758129243286902361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12916978344172324382536481 9687733758129243286902361)
          ·
            refine ⟨7265800318596932465176771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9687733758129243286902361 7265800318596932465176771)
            ·
              refine ⟨10898700477895398697765157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265800318596932465176771 10898700477895398697765157)
              ·
                refine ⟨2043506339605387255830967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10898700477895398697765157 2043506339605387255830967)
                ·
                  refine ⟨3065259509408080883746451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043506339605387255830967 3065259509408080883746451)
                  ·
                    refine ⟨4597889264112121325619677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3065259509408080883746451 4597889264112121325619677)
                    ·
                      refine ⟨1724208474042045497107379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4597889264112121325619677 1724208474042045497107379)
                      ·
                        rfl

theorem cell23_3357884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_3357884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357884 prefixEnd_3357884 := by exact prefixLift 3357884
  have htrace : WordTrace (prefixWord ++ tailWord_3357884) baseStart_3357884 baseEnd_3357884 := by
    simpa [prefixWord, tailWord_3357884, baseEnd_3357884] using wordTrace_append hprefix tailTrace_3357884
  have hstable : (prefixWord ++ tailWord_3357884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357884).length < 2 ^ (prefixWord ++ tailWord_3357884).sum := by decide
  have hdescent : baseEnd_3357884 < baseStart_3357884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357901 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_3357901 : Nat := 118140960795 + 3357901 * 2 ^ 59
def prefixEnd_3357901 : Nat := 4983230072969 + 3 ^ 40 * 3357901 * 2
def baseEnd_3357901 : Nat := 1724217203213171930594801

theorem tailTrace_3357901 : CollatzResearch.WordTrace tailWord_3357901 prefixEnd_3357901 1724217203213171930594801 := by
  unfold tailWord_3357901
  simp only [CollatzResearch.WordTrace]
  refine ⟨122472711007905635678529557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81648474005270423785686371 122472711007905635678529557)
  ·
    refine ⟨5740908328495576672431073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122472711007905635678529557 5740908328495576672431073)
    ·
      refine ⟨4305681246371682504323305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5740908328495576672431073 4305681246371682504323305)
      ·
        refine ⟨3229260934778761878242479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4305681246371682504323305 3229260934778761878242479)
        ·
          refine ⟨4843891402168142817363719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229260934778761878242479 4843891402168142817363719)
          ·
            refine ⟨7265837103252214226045579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843891402168142817363719 7265837103252214226045579)
            ·
              refine ⟨10898755654878321339068369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265837103252214226045579 10898755654878321339068369)
              ·
                refine ⟨8174066741158741004301277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898755654878321339068369 8174066741158741004301277)
                ·
                  refine ⟨3065275027934527876612979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8174066741158741004301277 3065275027934527876612979)
                  ·
                    refine ⟨4597912541901791814919469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3065275027934527876612979 4597912541901791814919469)
                    ·
                      refine ⟨1724217203213171930594801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4597912541901791814919469 1724217203213171930594801)
                      ·
                        rfl

theorem cell23_3357901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_3357901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357901 prefixEnd_3357901 := by exact prefixLift 3357901
  have htrace : WordTrace (prefixWord ++ tailWord_3357901) baseStart_3357901 baseEnd_3357901 := by
    simpa [prefixWord, tailWord_3357901, baseEnd_3357901] using wordTrace_append hprefix tailTrace_3357901
  have hstable : (prefixWord ++ tailWord_3357901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357901).length < 2 ^ (prefixWord ++ tailWord_3357901).sum := by decide
  have hdescent : baseEnd_3357901 < baseStart_3357901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357924 : List Nat := [2, 3, 1, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_3357924 : Nat := 118140960795 + 3357924 * 2 ^ 59
def prefixEnd_3357924 : Nat := 4983230072969 + 3 ^ 40 * 3357924 * 2
def baseEnd_3357924 : Nat := 1724229013268225340607195

theorem tailTrace_3357924 : CollatzResearch.WordTrace tailWord_3357924 prefixEnd_3357924 1724229013268225340607195 := by
  unfold tailWord_3357924
  simp only [CollatzResearch.WordTrace]
  refine ⟨61236774943411155303308413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81649033257881540404411217 61236774943411155303308413)
  ·
    refine ⟨22963790603779183238740655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61236774943411155303308413 22963790603779183238740655)
    ·
      refine ⟨34445685905668774858110983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22963790603779183238740655 34445685905668774858110983)
      ·
        refine ⟨51668528858503162287166475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34445685905668774858110983 51668528858503162287166475)
        ·
          refine ⟨77502793287754743430749713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51668528858503162287166475 77502793287754743430749713)
          ·
            refine ⟨58127094965816057573062285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77502793287754743430749713 58127094965816057573062285)
            ·
              refine ⟨21797660612181021589898357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58127094965816057573062285 21797660612181021589898357)
              ·
                refine ⟨2043530682391970774052971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21797660612181021589898357 2043530682391970774052971)
                ·
                  refine ⟨3065296023587956161079457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043530682391970774052971 3065296023587956161079457)
                  ·
                    refine ⟨2298972017690967120809593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065296023587956161079457 2298972017690967120809593)
                    ·
                      refine ⟨1724229013268225340607195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2298972017690967120809593 1724229013268225340607195)
                      ·
                        rfl

theorem cell23_3357924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_3357924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357924 prefixEnd_3357924 := by exact prefixLift 3357924
  have htrace : WordTrace (prefixWord ++ tailWord_3357924) baseStart_3357924 baseEnd_3357924 := by
    simpa [prefixWord, tailWord_3357924, baseEnd_3357924] using wordTrace_append hprefix tailTrace_3357924
  have hstable : (prefixWord ++ tailWord_3357924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357924).length < 2 ^ (prefixWord ++ tailWord_3357924).sum := by decide
  have hdescent : baseEnd_3357924 < baseStart_3357924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3357954 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3357954 : Nat := 118140960795 + 3357954 * 2 ^ 59
def prefixEnd_3357954 : Nat := 4983230072969 + 3 ^ 40 * 3357954 * 2
def baseEnd_3357954 : Nat := 1724244417687860223232057

theorem tailTrace_3357954 : CollatzResearch.WordTrace tailWord_3357954 prefixEnd_3357954 1724244417687860223232057 := by
  unfold tailWord_3357954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30618661019178406432552229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81649762717809083820139277 30618661019178406432552229)
  ·
    refine ⟨5740998941095951206103543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30618661019178406432552229 5740998941095951206103543)
    ·
      refine ⟨8611498411643926809155315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740998941095951206103543 8611498411643926809155315)
      ·
        refine ⟨12917247617465890213732973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8611498411643926809155315 12917247617465890213732973)
        ·
          refine ⟨4843967856549708830149865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12917247617465890213732973 4843967856549708830149865)
          ·
            refine ⟨3632975892412281622612399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843967856549708830149865 3632975892412281622612399)
            ·
              refine ⟨5449463838618422433918599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632975892412281622612399 5449463838618422433918599)
              ·
                refine ⟨8174195757927633650877899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449463838618422433918599 8174195757927633650877899)
                ·
                  refine ⟨12261293636891450476316849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8174195757927633650877899 12261293636891450476316849)
                  ·
                    refine ⟨9195970227668587857237637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12261293636891450476316849 9195970227668587857237637)
                    ·
                      refine ⟨1724244417687860223232057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9195970227668587857237637 1724244417687860223232057)
                      ·
                        rfl

theorem cell23_3357954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3357954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3357954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3357954 prefixEnd_3357954 := by exact prefixLift 3357954
  have htrace : WordTrace (prefixWord ++ tailWord_3357954) baseStart_3357954 baseEnd_3357954 := by
    simpa [prefixWord, tailWord_3357954, baseEnd_3357954] using wordTrace_append hprefix tailTrace_3357954
  have hstable : (prefixWord ++ tailWord_3357954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3357954).length < 2 ^ (prefixWord ++ tailWord_3357954).sum := by decide
  have hdescent : baseEnd_3357954 < baseStart_3357954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3357954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358060 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_3358060 : Nat := 118140960795 + 3358060 * 2 ^ 59
def prefixEnd_3358060 : Nat := 4983230072969 + 3 ^ 40 * 3358060 * 2
def baseEnd_3358060 : Nat := 1724298846637236808506569

theorem tailTrace_3358060 : CollatzResearch.WordTrace tailWord_3358060 prefixEnd_3358060 1724298846637236808506569 := by
  unfold tailWord_3358060
  simp only [CollatzResearch.WordTrace]
  refine ⟨61239255107164802916783817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81652340142886403889045089 61239255107164802916783817)
  ·
    refine ⟨45929441330373602187587863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61239255107164802916783817 45929441330373602187587863)
    ·
      refine ⟨68894161995560403281381795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45929441330373602187587863 68894161995560403281381795)
      ·
        refine ⟨103341242993340604922072693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68894161995560403281381795 103341242993340604922072693)
        ·
          refine ⟨9688241530625681711444315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103341242993340604922072693 9688241530625681711444315)
          ·
            refine ⟨14532362295938522567166473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9688241530625681711444315 14532362295938522567166473)
            ·
              refine ⟨10899271721953891925374855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14532362295938522567166473 10899271721953891925374855)
              ·
                refine ⟨16348907582930837888062283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10899271721953891925374855 16348907582930837888062283)
                ·
                  refine ⟨24523361374396256832093425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16348907582930837888062283 24523361374396256832093425)
                  ·
                    refine ⟨18392521030797192624070069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24523361374396256832093425 18392521030797192624070069)
                    ·
                      refine ⟨1724298846637236808506569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18392521030797192624070069 1724298846637236808506569)
                      ·
                        rfl

theorem cell23_3358060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_3358060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358060 prefixEnd_3358060 := by exact prefixLift 3358060
  have htrace : WordTrace (prefixWord ++ tailWord_3358060) baseStart_3358060 baseEnd_3358060 := by
    simpa [prefixWord, tailWord_3358060, baseEnd_3358060] using wordTrace_append hprefix tailTrace_3358060
  have hstable : (prefixWord ++ tailWord_3358060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358060).length < 2 ^ (prefixWord ++ tailWord_3358060).sum := by decide
  have hdescent : baseEnd_3358060 < baseStart_3358060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358087 : List Nat := [1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4]
def baseStart_3358087 : Nat := 118140960795 + 3358087 * 2 ^ 59
def prefixEnd_3358087 : Nat := 4983230072969 + 3 ^ 40 * 3358087 * 2
def baseEnd_3358087 : Nat := 1724312710614908202868945

theorem tailTrace_3358087 : CollatzResearch.WordTrace tailWord_3358087 prefixEnd_3358087 1724312710614908202868945 := by
  unfold tailWord_3358087
  simp only [CollatzResearch.WordTrace]
  refine ⟨122479494985231789444800515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81652996656821192963200343 122479494985231789444800515)
  ·
    refine ⟨183719242477847684167200773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122479494985231789444800515 183719242477847684167200773)
    ·
      refine ⟨34447357964596440781350145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183719242477847684167200773 34447357964596440781350145)
      ·
        refine ⟨25835518473447330586012609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34447357964596440781350145 25835518473447330586012609)
        ·
          refine ⟨19376638855085497939509457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25835518473447330586012609 19376638855085497939509457)
          ·
            refine ⟨14532479141314123454632093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19376638855085497939509457 14532479141314123454632093)
            ·
              refine ⟨5449679677992796295487035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14532479141314123454632093 5449679677992796295487035)
              ·
                refine ⟨8174519516989194443230553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449679677992796295487035 8174519516989194443230553)
                ·
                  refine ⟨6130889637741895832422915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8174519516989194443230553 6130889637741895832422915)
                  ·
                    refine ⟨9196334456612843748634373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6130889637741895832422915 9196334456612843748634373)
                    ·
                      refine ⟨1724312710614908202868945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9196334456612843748634373 1724312710614908202868945)
                      ·
                        rfl

theorem cell23_3358087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_3358087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358087 prefixEnd_3358087 := by exact prefixLift 3358087
  have htrace : WordTrace (prefixWord ++ tailWord_3358087) baseStart_3358087 baseEnd_3358087 := by
    simpa [prefixWord, tailWord_3358087, baseEnd_3358087] using wordTrace_append hprefix tailTrace_3358087
  have hstable : (prefixWord ++ tailWord_3358087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358087).length < 2 ^ (prefixWord ++ tailWord_3358087).sum := by decide
  have hdescent : baseEnd_3358087 < baseStart_3358087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358114 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_3358114 : Nat := 118140960795 + 3358114 * 2 ^ 59
def prefixEnd_3358114 : Nat := 4983230072969 + 3 ^ 40 * 3358114 * 2
def baseEnd_3358114 : Nat := 574775524864193199077107

theorem tailTrace_3358114 : CollatzResearch.WordTrace tailWord_3358114 prefixEnd_3358114 574775524864193199077107 := by
  unfold tailWord_3358114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30620119939033493264008349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81653653170755982037355597 30620119939033493264008349)
  ·
    refine ⟨11482544977137559974003131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30620119939033493264008349 11482544977137559974003131)
    ·
      refine ⟨17223817465706339961004697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11482544977137559974003131 17223817465706339961004697)
      ·
        refine ⟨12917863099279754970753523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17223817465706339961004697 12917863099279754970753523)
        ·
          refine ⟨19376794648919632456130285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12917863099279754970753523 19376794648919632456130285)
          ·
            refine ⟨7266297993344862171048857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19376794648919632456130285 7266297993344862171048857)
            ·
              refine ⟨5449723495008646628286643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266297993344862171048857 5449723495008646628286643)
              ·
                refine ⟨8174585242512969942429965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5449723495008646628286643 8174585242512969942429965)
                ·
                  refine ⟨3065469465942363728411237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8174585242512969942429965 3065469465942363728411237)
                  ·
                    refine ⟨574775524864193199077107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065469465942363728411237 574775524864193199077107)
                    ·
                      rfl

theorem cell23_3358114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_3358114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358114 prefixEnd_3358114 := by exact prefixLift 3358114
  have htrace : WordTrace (prefixWord ++ tailWord_3358114) baseStart_3358114 baseEnd_3358114 := by
    simpa [prefixWord, tailWord_3358114, baseEnd_3358114] using wordTrace_append hprefix tailTrace_3358114
  have hstable : (prefixWord ++ tailWord_3358114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358114).length < 2 ^ (prefixWord ++ tailWord_3358114).sum := by decide
  have hdescent : baseEnd_3358114 < baseStart_3358114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358147 : List Nat := [1, 1, 1, 3, 1, 1, 6, 1, 1, 5, 2]
def baseStart_3358147 : Nat := 118140960795 + 3358147 * 2 ^ 59
def prefixEnd_3358147 : Nat := 4983230072969 + 3 ^ 40 * 3358147 * 2
def baseEnd_3358147 : Nat := 1724343519454177968118669

theorem tailTrace_3358147 : CollatzResearch.WordTrace tailWord_3358147 prefixEnd_3358147 1724343519454177968118669 := by
  unfold tailWord_3358147
  simp only [CollatzResearch.WordTrace]
  refine ⟨122481683365014419691984695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81654455576676279794656463 122481683365014419691984695)
  ·
    refine ⟨183722525047521629537977043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122481683365014419691984695 183722525047521629537977043)
    ·
      refine ⟨275583787571282444306965565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183722525047521629537977043 275583787571282444306965565)
      ·
        refine ⟨103343920339230916615112087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275583787571282444306965565 103343920339230916615112087)
        ·
          refine ⟨155015880508846374922668131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103343920339230916615112087 155015880508846374922668131)
          ·
            refine ⟨232523820763269562384002197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155015880508846374922668131 232523820763269562384002197)
            ·
              refine ⟨10899554098278260736750103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232523820763269562384002197 10899554098278260736750103)
              ·
                refine ⟨16349331147417391105125155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10899554098278260736750103 16349331147417391105125155)
                ·
                  refine ⟨24523996721126086657687733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16349331147417391105125155 24523996721126086657687733)
                  ·
                    refine ⟨2299124692605570624158225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24523996721126086657687733 2299124692605570624158225)
                    ·
                      refine ⟨1724343519454177968118669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299124692605570624158225 1724343519454177968118669)
                      ·
                        rfl

theorem cell23_3358147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 5, 2].length) (baseStart_3358147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358147 prefixEnd_3358147 := by exact prefixLift 3358147
  have htrace : WordTrace (prefixWord ++ tailWord_3358147) baseStart_3358147 baseEnd_3358147 := by
    simpa [prefixWord, tailWord_3358147, baseEnd_3358147] using wordTrace_append hprefix tailTrace_3358147
  have hstable : (prefixWord ++ tailWord_3358147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358147).length < 2 ^ (prefixWord ++ tailWord_3358147).sum := by decide
  have hdescent : baseEnd_3358147 < baseStart_3358147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358148 : List Nat := [2, 3, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_3358148 : Nat := 118140960795 + 3358148 * 2 ^ 59
def prefixEnd_3358148 : Nat := 4983230072969 + 3 ^ 40 * 3358148 * 2
def baseEnd_3358148 : Nat := 574781344311610821402055

theorem tailTrace_3358148 : CollatzResearch.WordTrace tailWord_3358148 prefixEnd_3358148 574781344311610821402055 := by
  unfold tailWord_3358148
  simp only [CollatzResearch.WordTrace]
  refine ⟨61240859919005398431385549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81654479892007197908514065 61240859919005398431385549)
  ·
    refine ⟨22965322469627024411769581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61240859919005398431385549 22965322469627024411769581)
    ·
      refine ⟨8611995926110134154413593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22965322469627024411769581 8611995926110134154413593)
      ·
        refine ⟨6458996944582600615810195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8611995926110134154413593 6458996944582600615810195)
        ·
          refine ⟨9688495416873900923715293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458996944582600615810195 9688495416873900923715293)
          ·
            refine ⟨3633185781327712846393235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9688495416873900923715293 3633185781327712846393235)
            ·
              refine ⟨5449778671991569269589853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633185781327712846393235 5449778671991569269589853)
              ·
                refine ⟨2043667001996838476096195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5449778671991569269589853 2043667001996838476096195)
                ·
                  refine ⟨3065500502995257714144293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043667001996838476096195 3065500502995257714144293)
                  ·
                    refine ⟨574781344311610821402055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065500502995257714144293 574781344311610821402055)
                    ·
                      rfl

theorem cell23_3358148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_3358148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358148 prefixEnd_3358148 := by exact prefixLift 3358148
  have htrace : WordTrace (prefixWord ++ tailWord_3358148) baseStart_3358148 baseEnd_3358148 := by
    simpa [prefixWord, tailWord_3358148, baseEnd_3358148] using wordTrace_append hprefix tailTrace_3358148
  have hstable : (prefixWord ++ tailWord_3358148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358148).length < 2 ^ (prefixWord ++ tailWord_3358148).sum := by decide
  have hdescent : baseEnd_3358148 < baseStart_3358148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358194 : List Nat := [3, 2, 1, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_3358194 : Nat := 118140960795 + 3358194 * 2 ^ 59
def prefixEnd_3358194 : Nat := 4983230072969 + 3 ^ 40 * 3358194 * 2
def baseEnd_3358194 : Nat := 1724367653044939284230953

theorem tailTrace_3358194 : CollatzResearch.WordTrace tailWord_3358194 prefixEnd_3358194 1724367653044939284230953 := by
  unfold tailWord_3358194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30620849398961036679736409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81655598397229431145963757 30620849398961036679736409)
  ·
    refine ⟨22965637049220777509802307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30620849398961036679736409 22965637049220777509802307)
    ·
      refine ⟨34448455573831166264703461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965637049220777509802307 34448455573831166264703461)
      ·
        refine ⟨6459085420093343674631899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34448455573831166264703461 6459085420093343674631899)
        ·
          refine ⟨9688628130140015511947849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459085420093343674631899 9688628130140015511947849)
          ·
            refine ⟨7266471097605011633960887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9688628130140015511947849 7266471097605011633960887)
            ·
              refine ⟨10899706646407517450941331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7266471097605011633960887 10899706646407517450941331)
              ·
                refine ⟨16349559969611276176411997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10899706646407517450941331 16349559969611276176411997)
                ·
                  refine ⟨6131084988604228566154499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16349559969611276176411997 6131084988604228566154499)
                  ·
                    refine ⟨9196627482906342849231749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6131084988604228566154499 9196627482906342849231749)
                    ·
                      refine ⟨1724367653044939284230953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9196627482906342849231749 1724367653044939284230953)
                      ·
                        rfl

theorem cell23_3358194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_3358194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358194 prefixEnd_3358194 := by exact prefixLift 3358194
  have htrace : WordTrace (prefixWord ++ tailWord_3358194) baseStart_3358194 baseEnd_3358194 := by
    simpa [prefixWord, tailWord_3358194, baseEnd_3358194] using wordTrace_append hprefix tailTrace_3358194
  have hstable : (prefixWord ++ tailWord_3358194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358194).length < 2 ^ (prefixWord ++ tailWord_3358194).sum := by decide
  have hdescent : baseEnd_3358194 < baseStart_3358194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358200 : List Nat := [2, 1, 2, 1, 1, 5, 2, 9]
def baseStart_3358200 : Nat := 118140960795 + 3358200 * 2 ^ 59
def prefixEnd_3358200 : Nat := 4983230072969 + 3 ^ 40 * 3358200 * 2
def baseEnd_3358200 : Nat := 63865582738106157805775

theorem tailTrace_3358200 : CollatzResearch.WordTrace tailWord_3358200 prefixEnd_3358200 63865582738106157805775 := by
  unfold tailWord_3358200
  simp only [CollatzResearch.WordTrace]
  refine ⟨61241808216911204871832027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81655744289214939829109369 61241808216911204871832027)
  ·
    refine ⟨91862712325366807307748041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61241808216911204871832027 91862712325366807307748041)
    ·
      refine ⟨68897034244025105480811031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91862712325366807307748041 68897034244025105480811031)
      ·
        refine ⟨103345551366037658221216547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68897034244025105480811031 103345551366037658221216547)
        ·
          refine ⟨155018327049056487331824821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103345551366037658221216547 155018327049056487331824821)
          ·
            refine ⟨14532968160849045687358577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155018327049056487331824821 14532968160849045687358577)
            ·
              refine ⟨10899726120636784265518933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14532968160849045687358577 10899726120636784265518933)
              ·
                refine ⟨63865582738106157805775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10899726120636784265518933 63865582738106157805775)
                ·
                  rfl

theorem cell23_3358200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 9].length) (baseStart_3358200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358200 prefixEnd_3358200 := by exact prefixLift 3358200
  have htrace : WordTrace (prefixWord ++ tailWord_3358200) baseStart_3358200 baseEnd_3358200 := by
    simpa [prefixWord, tailWord_3358200, baseEnd_3358200] using wordTrace_append hprefix tailTrace_3358200
  have hstable : (prefixWord ++ tailWord_3358200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358200).length < 2 ^ (prefixWord ++ tailWord_3358200).sum := by decide
  have hdescent : baseEnd_3358200 < baseStart_3358200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358222 : List Nat := [4, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_3358222 : Nat := 118140960795 + 3358222 * 2 ^ 59
def prefixEnd_3358222 : Nat := 4983230072969 + 3 ^ 40 * 3358222 * 2
def baseEnd_3358222 : Nat := 1724382030503265174680825

theorem tailTrace_3358222 : CollatzResearch.WordTrace tailWord_3358222 prefixEnd_3358222 1724382030503265174680825 := by
  unfold tailWord_3358222
  simp only [CollatzResearch.WordTrace]
  refine ⟨15310552354967838437620615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81656279226495138333976613 15310552354967838437620615)
  ·
    refine ⟨22965828532451757656430923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15310552354967838437620615 22965828532451757656430923)
    ·
      refine ⟨34448742798677636484646385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22965828532451757656430923 34448742798677636484646385)
      ·
        refine ⟨25836557099008227363484789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34448742798677636484646385 25836557099008227363484789)
        ·
          refine ⟨2422177228032021315326699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25836557099008227363484789 2422177228032021315326699)
          ·
            refine ⟨3633265842048031972990049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422177228032021315326699 3633265842048031972990049)
            ·
              refine ⟨2724949381536023979742537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633265842048031972990049 2724949381536023979742537)
              ·
                refine ⟨2043712036152017984806903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2724949381536023979742537 2043712036152017984806903)
                ·
                  refine ⟨3065568054228026977210355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043712036152017984806903 3065568054228026977210355)
                  ·
                    refine ⟨4598352081342040465815533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3065568054228026977210355 4598352081342040465815533)
                    ·
                      refine ⟨1724382030503265174680825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4598352081342040465815533 1724382030503265174680825)
                      ·
                        rfl

theorem cell23_3358222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_3358222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358222 prefixEnd_3358222 := by exact prefixLift 3358222
  have htrace : WordTrace (prefixWord ++ tailWord_3358222) baseStart_3358222 baseEnd_3358222 := by
    simpa [prefixWord, tailWord_3358222, baseEnd_3358222] using wordTrace_append hprefix tailTrace_3358222
  have hstable : (prefixWord ++ tailWord_3358222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358222).length < 2 ^ (prefixWord ++ tailWord_3358222).sum := by decide
  have hdescent : baseEnd_3358222 < baseStart_3358222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358262 : List Nat := [5, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2]
def baseStart_3358262 : Nat := 118140960795 + 3358262 * 2 ^ 59
def prefixEnd_3358262 : Nat := 4983230072969 + 3 ^ 40 * 3358262 * 2
def baseEnd_3358262 : Nat := 1724402569729445018180641

theorem tailTrace_3358262 : CollatzResearch.WordTrace tailWord_3358262 prefixEnd_3358262 1724402569729445018180641 := by
  unfold tailWord_3358262
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655367359974862145776315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81657251839731862888280693 7655367359974862145776315)
  ·
    refine ⟨11483051039962293218664473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7655367359974862145776315 11483051039962293218664473)
    ·
      refine ⟨8612288279971719913998355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11483051039962293218664473 8612288279971719913998355)
      ·
        refine ⟨12918432419957579870997533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8612288279971719913998355 12918432419957579870997533)
        ·
          refine ⟨4844412157484092451624075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12918432419957579870997533 4844412157484092451624075)
          ·
            refine ⟨7266618236226138677436113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844412157484092451624075 7266618236226138677436113)
            ·
              refine ⟨5449963677169604008077085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266618236226138677436113 5449963677169604008077085)
              ·
                refine ⟨2043736378938601503028907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5449963677169604008077085 2043736378938601503028907)
                ·
                  refine ⟨3065604568407902254543361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043736378938601503028907 3065604568407902254543361)
                  ·
                    refine ⟨2299203426305926690907521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065604568407902254543361 2299203426305926690907521)
                    ·
                      refine ⟨1724402569729445018180641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299203426305926690907521 1724402569729445018180641)
                      ·
                        rfl

theorem cell23_3358262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_3358262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358262 prefixEnd_3358262 := by exact prefixLift 3358262
  have htrace : WordTrace (prefixWord ++ tailWord_3358262) baseStart_3358262 baseEnd_3358262 := by
    simpa [prefixWord, tailWord_3358262, baseEnd_3358262] using wordTrace_append hprefix tailTrace_3358262
  have hstable : (prefixWord ++ tailWord_3358262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358262).length < 2 ^ (prefixWord ++ tailWord_3358262).sum := by decide
  have hdescent : baseEnd_3358262 < baseStart_3358262 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358271 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 1, 3, 2]
def baseStart_3358271 : Nat := 118140960795 + 3358271 * 2 ^ 59
def prefixEnd_3358271 : Nat := 4983230072969 + 3 ^ 40 * 3358271 * 2
def baseEnd_3358271 : Nat := 1724407191055335482968099

theorem tailTrace_3358271 : CollatzResearch.WordTrace tailWord_3358271 prefixEnd_3358271 1724407191055335482968099 := by
  unfold tailWord_3358271
  simp only [CollatzResearch.WordTrace]
  refine ⟨122486206016565188869498667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81657470677710125912999111 122486206016565188869498667)
  ·
    refine ⟨183729309024847783304248001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122486206016565188869498667 183729309024847783304248001)
    ·
      refine ⟨137796981768635837478186001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183729309024847783304248001 137796981768635837478186001)
      ·
        refine ⟨103347736326476878108639501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137796981768635837478186001 103347736326476878108639501)
        ·
          refine ⟨38755401122428829290739813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103347736326476878108639501 38755401122428829290739813)
          ·
            refine ⟨7266637710455405492013715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38755401122428829290739813 7266637710455405492013715)
            ·
              refine ⟨10899956565683108238020573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7266637710455405492013715 10899956565683108238020573)
              ·
                refine ⟨4087483712131165589257715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10899956565683108238020573 4087483712131165589257715)
                ·
                  refine ⟨6131225568196748383886573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4087483712131165589257715 6131225568196748383886573)
                  ·
                    refine ⟨2299209588073780643957465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6131225568196748383886573 2299209588073780643957465)
                    ·
                      refine ⟨1724407191055335482968099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299209588073780643957465 1724407191055335482968099)
                      ·
                        rfl

theorem cell23_3358271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 3, 2].length) (baseStart_3358271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358271 prefixEnd_3358271 := by exact prefixLift 3358271
  have htrace : WordTrace (prefixWord ++ tailWord_3358271) baseStart_3358271 baseEnd_3358271 := by
    simpa [prefixWord, tailWord_3358271, baseEnd_3358271] using wordTrace_append hprefix tailTrace_3358271
  have hstable : (prefixWord ++ tailWord_3358271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358271).length < 2 ^ (prefixWord ++ tailWord_3358271).sum := by decide
  have hdescent : baseEnd_3358271 < baseStart_3358271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358307 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 7]
def baseStart_3358307 : Nat := 118140960795 + 3358307 * 2 ^ 59
def prefixEnd_3358307 : Nat := 4983230072969 + 3 ^ 40 * 3358307 * 2
def baseEnd_3358307 : Nat := 191602852928766371346437

theorem tailTrace_3358307 : CollatzResearch.WordTrace tailWord_3358307 prefixEnd_3358307 191602852928766371346437 := by
  unfold tailWord_3358307
  simp only [CollatzResearch.WordTrace]
  refine ⟨122487519044434767017809175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81658346029623178011872783 122487519044434767017809175)
  ·
    refine ⟨183731278566652150526713763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122487519044434767017809175 183731278566652150526713763)
    ·
      refine ⟨275596917849978225790070645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183731278566652150526713763 275596917849978225790070645)
      ·
        refine ⟨25837211048435458667819123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275596917849978225790070645 25837211048435458667819123)
        ·
          refine ⟨38755816572653188001728685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25837211048435458667819123 38755816572653188001728685)
          ·
            refine ⟨14533431214744945500648257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38755816572653188001728685 14533431214744945500648257)
            ·
              refine ⟨10900073411058709125486193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14533431214744945500648257 10900073411058709125486193)
              ·
                refine ⟨8175055058294031844114645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10900073411058709125486193 8175055058294031844114645)
                ·
                  refine ⟨191602852928766371346437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8175055058294031844114645 191602852928766371346437)
                  ·
                    rfl

theorem cell23_3358307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 7].length) (baseStart_3358307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358307 prefixEnd_3358307 := by exact prefixLift 3358307
  have htrace : WordTrace (prefixWord ++ tailWord_3358307) baseStart_3358307 baseEnd_3358307 := by
    simpa [prefixWord, tailWord_3358307, baseEnd_3358307] using wordTrace_append hprefix tailTrace_3358307
  have hstable : (prefixWord ++ tailWord_3358307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358307).length < 2 ^ (prefixWord ++ tailWord_3358307).sum := by decide
  have hdescent : baseEnd_3358307 < baseStart_3358307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358341 : List Nat := [1, 3, 1, 1, 4, 1, 5, 2, 5]
def baseStart_3358341 : Nat := 118140960795 + 3358341 * 2 ^ 59
def prefixEnd_3358341 : Nat := 4983230072969 + 3 ^ 40 * 3358341 * 2
def baseEnd_3358341 : Nat := 191604792744572245454753

theorem tailTrace_3358341 : CollatzResearch.WordTrace tailWord_3358341 prefixEnd_3358341 191604792744572245454753 := by
  unfold tailWord_3358341
  simp only [CollatzResearch.WordTrace]
  refine ⟨122488759126311590824546877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81659172750874393883031251 122488759126311590824546877)
  ·
    refine ⟨45933284672366846559205079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122488759126311590824546877 45933284672366846559205079)
    ·
      refine ⟨68899927008550269838807619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45933284672366846559205079 68899927008550269838807619)
      ·
        refine ⟨103349890512825404758211429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68899927008550269838807619 103349890512825404758211429)
        ·
          refine ⟨19378104471154763392164643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103349890512825404758211429 19378104471154763392164643)
          ·
            refine ⟨29067156706732145088246965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378104471154763392164643 29067156706732145088246965)
            ·
              refine ⟨2725045941256138602023153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29067156706732145088246965 2725045941256138602023153)
              ·
                refine ⟨2043784455942103951517365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725045941256138602023153 2043784455942103951517365)
                ·
                  refine ⟨191604792744572245454753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2043784455942103951517365 191604792744572245454753)
                  ·
                    rfl

theorem cell23_3358341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 5].length) (baseStart_3358341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358341 prefixEnd_3358341 := by exact prefixLift 3358341
  have htrace : WordTrace (prefixWord ++ tailWord_3358341) baseStart_3358341 baseEnd_3358341 := by
    simpa [prefixWord, tailWord_3358341, baseEnd_3358341] using wordTrace_append hprefix tailTrace_3358341
  have hstable : (prefixWord ++ tailWord_3358341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358341).length < 2 ^ (prefixWord ++ tailWord_3358341).sum := by decide
  have hdescent : baseEnd_3358341 < baseStart_3358341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358347 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5]
def baseStart_3358347 : Nat := 118140960795 + 3358347 * 2 ^ 59
def prefixEnd_3358347 : Nat := 4983230072969 + 3 ^ 40 * 3358347 * 2
def baseEnd_3358347 : Nat := 1724446215585077185617749

theorem tailTrace_3358347 : CollatzResearch.WordTrace tailWord_3358347 prefixEnd_3358347 1724446215585077185617749 := by
  unfold tailWord_3358347
  simp only [CollatzResearch.WordTrace]
  refine ⟨122488977964289853849265295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81659318642859902566176863 122488977964289853849265295)
  ·
    refine ⟨183733466946434780773897943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122488977964289853849265295 183733466946434780773897943)
    ·
      refine ⟨275600200419652171160846915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183733466946434780773897943 275600200419652171160846915)
      ·
        refine ⟨413400300629478256741270373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275600200419652171160846915 413400300629478256741270373)
        ·
          refine ⟨77512556368027173138988195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 413400300629478256741270373 77512556368027173138988195)
          ·
            refine ⟨116268834552040759708482293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77512556368027173138988195 116268834552040759708482293)
            ·
              refine ⟨10900203239253821222670215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116268834552040759708482293 10900203239253821222670215)
              ·
                refine ⟨16350304858880731834005323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900203239253821222670215 16350304858880731834005323)
                ·
                  refine ⟨24525457288321097751007985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16350304858880731834005323 24525457288321097751007985)
                  ·
                    refine ⟨18394092966240823313255989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24525457288321097751007985 18394092966240823313255989)
                    ·
                      refine ⟨1724446215585077185617749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18394092966240823313255989 1724446215585077185617749)
                      ·
                        rfl

theorem cell23_3358347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 5].length) (baseStart_3358347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358347 prefixEnd_3358347 := by exact prefixLift 3358347
  have htrace : WordTrace (prefixWord ++ tailWord_3358347) baseStart_3358347 baseEnd_3358347 := by
    simpa [prefixWord, tailWord_3358347, baseEnd_3358347] using wordTrace_append hprefix tailTrace_3358347
  have hstable : (prefixWord ++ tailWord_3358347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358347).length < 2 ^ (prefixWord ++ tailWord_3358347).sum := by decide
  have hdescent : baseEnd_3358347 < baseStart_3358347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358357 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 4]
def baseStart_3358357 : Nat := 118140960795 + 3358357 * 2 ^ 59
def prefixEnd_3358357 : Nat := 4983230072969 + 3 ^ 40 * 3358357 * 2
def baseEnd_3358357 : Nat := 1724451350391622146492703

theorem tailTrace_3358357 : CollatzResearch.WordTrace tailWord_3358357 prefixEnd_3358357 1724451350391622146492703 := by
  unfold tailWord_3358357
  simp only [CollatzResearch.WordTrace]
  refine ⟨122489342694253625557129325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81659561796169083704752883 122489342694253625557129325)
  ·
    refine ⟨45933503510345109583923497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122489342694253625557129325 45933503510345109583923497)
    ·
      refine ⟨34450127632758832187942623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45933503510345109583923497 34450127632758832187942623)
      ·
        refine ⟨51675191449138248281913935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34450127632758832187942623 51675191449138248281913935)
        ·
          refine ⟨77512787173707372422870903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51675191449138248281913935 77512787173707372422870903)
          ·
            refine ⟨116269180760561058634306355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77512787173707372422870903 116269180760561058634306355)
            ·
              refine ⟨174403771140841587951459533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116269180760561058634306355 174403771140841587951459533)
              ·
                refine ⟨65401414177815595481797325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174403771140841587951459533 65401414177815595481797325)
                ·
                  refine ⟨24525530316680848305673997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65401414177815595481797325 24525530316680848305673997)
                  ·
                    refine ⟨9197073868755318114627749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24525530316680848305673997 9197073868755318114627749)
                    ·
                      refine ⟨1724451350391622146492703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9197073868755318114627749 1724451350391622146492703)
                      ·
                        rfl

theorem cell23_3358357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_3358357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358357 prefixEnd_3358357 := by exact prefixLift 3358357
  have htrace : WordTrace (prefixWord ++ tailWord_3358357) baseStart_3358357 baseEnd_3358357 := by
    simpa [prefixWord, tailWord_3358357, baseEnd_3358357] using wordTrace_append hprefix tailTrace_3358357
  have hstable : (prefixWord ++ tailWord_3358357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358357).length < 2 ^ (prefixWord ++ tailWord_3358357).sum := by decide
  have hdescent : baseEnd_3358357 < baseStart_3358357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358387 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6]
def baseStart_3358387 : Nat := 118140960795 + 3358387 * 2 ^ 59
def prefixEnd_3358387 : Nat := 4983230072969 + 3 ^ 40 * 3358387 * 2
def baseEnd_3358387 : Nat := 1724466754811257029117565

theorem tailTrace_3358387 : CollatzResearch.WordTrace tailWord_3358387 prefixEnd_3358387 1724466754811257029117565 := by
  unfold tailWord_3358387
  simp only [CollatzResearch.WordTrace]
  refine ⟨122490436884144940680721415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81660291256096627120480943 122490436884144940680721415)
  ·
    refine ⟨183735655326217411021082123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122490436884144940680721415 183735655326217411021082123)
    ·
      refine ⟨275603482989326116531623185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183735655326217411021082123 275603482989326116531623185)
      ·
        refine ⟨206702612241994587398717389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275603482989326116531623185 206702612241994587398717389)
        ·
          refine ⟨77513479590747970274519021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206702612241994587398717389 77513479590747970274519021)
          ·
            refine ⟨29067554846530488852944633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77513479590747970274519021 29067554846530488852944633)
            ·
              refine ⟨21800666134897866639708475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29067554846530488852944633 21800666134897866639708475)
              ·
                refine ⟨32700999202346799959562713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21800666134897866639708475 32700999202346799959562713)
                ·
                  refine ⟨24525749401760099969672035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32700999202346799959562713 24525749401760099969672035)
                  ·
                    refine ⟨36788624102640149954508053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24525749401760099969672035 36788624102640149954508053)
                    ·
                      refine ⟨1724466754811257029117565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36788624102640149954508053 1724466754811257029117565)
                      ·
                        rfl

theorem cell23_3358387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 6].length) (baseStart_3358387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358387 prefixEnd_3358387 := by exact prefixLift 3358387
  have htrace : WordTrace (prefixWord ++ tailWord_3358387) baseStart_3358387 baseEnd_3358387 := by
    simpa [prefixWord, tailWord_3358387, baseEnd_3358387] using wordTrace_append hprefix tailTrace_3358387
  have hstable : (prefixWord ++ tailWord_3358387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358387).length < 2 ^ (prefixWord ++ tailWord_3358387).sum := by decide
  have hdescent : baseEnd_3358387 < baseStart_3358387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358414 : List Nat := [4, 1, 1, 1, 3, 1, 1, 5, 6]
def baseStart_3358414 : Nat := 118140960795 + 3358414 * 2 ^ 59
def prefixEnd_3358414 : Nat := 4983230072969 + 3 ^ 40 * 3358414 * 2
def baseEnd_3358414 : Nat := 191608957643214269275549

theorem tailTrace_3358414 : CollatzResearch.WordTrace tailWord_3358414 prefixEnd_3358414 191608957643214269275549 := by
  unfold tailWord_3358414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15311427706880890536494287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81660947770031416194636197 15311427706880890536494287)
  ·
    refine ⟨22967141560321335804741431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15311427706880890536494287 22967141560321335804741431)
    ·
      refine ⟨34450712340482003707112147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22967141560321335804741431 34450712340482003707112147)
      ·
        refine ⟨51676068510723005560668221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34450712340482003707112147 51676068510723005560668221)
        ·
          refine ⟨19378525691521127085250583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51676068510723005560668221 19378525691521127085250583)
          ·
            refine ⟨29067788537281690627875875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19378525691521127085250583 29067788537281690627875875)
            ·
              refine ⟨43601682805922535941813813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29067788537281690627875875 43601682805922535941813813)
              ·
                refine ⟨4087657763055237744545045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43601682805922535941813813 4087657763055237744545045)
                ·
                  refine ⟨191608957643214269275549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4087657763055237744545045 191608957643214269275549)
                  ·
                    rfl

theorem cell23_3358414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_3358414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358414 prefixEnd_3358414 := by exact prefixLift 3358414
  have htrace : WordTrace (prefixWord ++ tailWord_3358414) baseStart_3358414 baseEnd_3358414 := by
    simpa [prefixWord, tailWord_3358414, baseEnd_3358414] using wordTrace_append hprefix tailTrace_3358414
  have hstable : (prefixWord ++ tailWord_3358414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358414).length < 2 ^ (prefixWord ++ tailWord_3358414).sum := by decide
  have hdescent : baseEnd_3358414 < baseStart_3358414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358422 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 2, 5]
def baseStart_3358422 : Nat := 118140960795 + 3358422 * 2 ^ 59
def prefixEnd_3358422 : Nat := 4983230072969 + 3 ^ 40 * 3358422 * 2
def baseEnd_3358422 : Nat := 574828242211388130726635

theorem tailTrace_3358422 : CollatzResearch.WordTrace tailWord_3358422 prefixEnd_3358422 574828242211388130726635 := by
  unfold tailWord_3358422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655732089938633853640345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81661142292678761105497013 7655732089938633853640345)
  ·
    refine ⟨5741799067453975390230259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7655732089938633853640345 5741799067453975390230259)
    ·
      refine ⟨8612698601180963085345389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5741799067453975390230259 8612698601180963085345389)
      ·
        refine ⟨3229761975442861157004521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8612698601180963085345389 3229761975442861157004521)
        ·
          refine ⟨2422321481582145867753391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3229761975442861157004521 2422321481582145867753391)
          ·
            refine ⟨3633482222373218801630087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422321481582145867753391 3633482222373218801630087)
            ·
              refine ⟨5450223333559828202445131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633482222373218801630087 5450223333559828202445131)
              ·
                refine ⟨8175335000339742303667697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450223333559828202445131 8175335000339742303667697)
                ·
                  refine ⟨6131501250254806727750773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8175335000339742303667697 6131501250254806727750773)
                  ·
                    refine ⟨574828242211388130726635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6131501250254806727750773 574828242211388130726635)
                    ·
                      rfl

theorem cell23_3358422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_3358422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358422 prefixEnd_3358422 := by exact prefixLift 3358422
  have htrace : WordTrace (prefixWord ++ tailWord_3358422) baseStart_3358422 baseEnd_3358422 := by
    simpa [prefixWord, tailWord_3358422, baseEnd_3358422] using wordTrace_append hprefix tailTrace_3358422
  have hstable : (prefixWord ++ tailWord_3358422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358422).length < 2 ^ (prefixWord ++ tailWord_3358422).sum := by decide
  have hdescent : baseEnd_3358422 < baseStart_3358422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358428 : List Nat := [2, 2, 5, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_3358428 : Nat := 118140960795 + 3358428 * 2 ^ 59
def prefixEnd_3358428 : Nat := 4983230072969 + 3 ^ 40 * 3358428 * 2
def baseEnd_3358428 : Nat := 1724487807518091368704877

theorem tailTrace_3358428 : CollatzResearch.WordTrace tailWord_3358428 prefixEnd_3358428 1724487807518091368704877 := by
  unfold tailWord_3358428
  simp only [CollatzResearch.WordTrace]
  refine ⟨61245966138498202341481969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81661288184664269788642625 61245966138498202341481969)
  ·
    refine ⟨45934474603873651756111477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61245966138498202341481969 45934474603873651756111477)
    ·
      refine ⟨4306356994113154852135451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45934474603873651756111477 4306356994113154852135451)
      ·
        refine ⟨6459535491169732278203177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306356994113154852135451 6459535491169732278203177)
        ·
          refine ⟨4844651618377299208652383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6459535491169732278203177 4844651618377299208652383)
          ·
            refine ⟨7266977427565948812978575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844651618377299208652383 7266977427565948812978575)
            ·
              refine ⟨10900466141348923219467863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7266977427565948812978575 10900466141348923219467863)
              ·
                refine ⟨16350699212023384829201795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900466141348923219467863 16350699212023384829201795)
                ·
                  refine ⟨24526048818035077243802693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16350699212023384829201795 24526048818035077243802693)
                  ·
                    refine ⟨4598634153381576983213005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24526048818035077243802693 4598634153381576983213005)
                    ·
                      refine ⟨1724487807518091368704877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4598634153381576983213005 1724487807518091368704877)
                      ·
                        rfl

theorem cell23_3358428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_3358428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358428 prefixEnd_3358428 := by exact prefixLift 3358428
  have htrace : WordTrace (prefixWord ++ tailWord_3358428) baseStart_3358428 baseEnd_3358428 := by
    simpa [prefixWord, tailWord_3358428, baseEnd_3358428] using wordTrace_append hprefix tailTrace_3358428
  have hstable : (prefixWord ++ tailWord_3358428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358428).length < 2 ^ (prefixWord ++ tailWord_3358428).sum := by decide
  have hdescent : baseEnd_3358428 < baseStart_3358428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
