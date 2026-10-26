import V185TrunkScan23Chunk1224

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7258676 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_7258676 : Nat := 118140960795 + 7258676 * 2 ^ 59
def prefixEnd_7258676 : Nat := 4983230072969 + 3 ^ 40 * 7258676 * 2
def baseEnd_7258676 : Nat := 3727189703255147630467963

theorem tailTrace_7258676 : CollatzResearch.WordTrace tailWord_7258676 prefixEnd_7258676 3727189703255147630467963 := by
  unfold tailWord_7258676
  simp only [CollatzResearch.WordTrace]
  refine ⟨132372831725532005004845941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176497108967376006673127921 132372831725532005004845941)
  ·
    refine ⟨12409952974268625469204307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 132372831725532005004845941 12409952974268625469204307)
    ·
      refine ⟨18614929461402938203806461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12409952974268625469204307 18614929461402938203806461)
      ·
        refine ⟨6980598548026101826427423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18614929461402938203806461 6980598548026101826427423)
        ·
          refine ⟨10470897822039152739641135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6980598548026101826427423 10470897822039152739641135)
          ·
            refine ⟨15706346733058729109461703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10470897822039152739641135 15706346733058729109461703)
            ·
              refine ⟨23559520099588093664192555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15706346733058729109461703 23559520099588093664192555)
              ·
                refine ⟨35339280149382140496288833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23559520099588093664192555 35339280149382140496288833)
                ·
                  refine ⟨26504460112036605372216625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35339280149382140496288833 26504460112036605372216625)
                  ·
                    refine ⟨19878345084027454029162469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26504460112036605372216625 19878345084027454029162469)
                    ·
                      refine ⟨3727189703255147630467963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19878345084027454029162469 3727189703255147630467963)
                      ·
                        rfl

theorem cell23_7258676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_7258676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258676 prefixEnd_7258676 := by exact prefixLift 7258676
  have htrace : WordTrace (prefixWord ++ tailWord_7258676) baseStart_7258676 baseEnd_7258676 := by
    simpa [prefixWord, tailWord_7258676, baseEnd_7258676] using wordTrace_append hprefix tailTrace_7258676
  have hstable : (prefixWord ++ tailWord_7258676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258676).length < 2 ^ (prefixWord ++ tailWord_7258676).sum := by decide
  have hdescent : baseEnd_7258676 < baseStart_7258676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258802 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 1, 6]
def baseStart_7258802 : Nat := 118140960795 + 7258802 * 2 ^ 59
def prefixEnd_7258802 : Nat := 4983230072969 + 3 ^ 40 * 7258802 * 2
def baseEnd_7258802 : Nat := 1242418133939204712497461

theorem tailTrace_7258802 : CollatzResearch.WordTrace tailWord_7258802 prefixEnd_7258802 1242418133939204712497461 := by
  unfold tailWord_7258802
  simp only [CollatzResearch.WordTrace]
  refine ⟨66187564762151883382194665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176500172699071689019185773 66187564762151883382194665)
  ·
    refine ⟨49640673571613912536645999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66187564762151883382194665 49640673571613912536645999)
    ·
      refine ⟨74461010357420868804968999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49640673571613912536645999 74461010357420868804968999)
      ·
        refine ⟨111691515536131303207453499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74461010357420868804968999 111691515536131303207453499)
        ·
          refine ⟨167537273304196954811180249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111691515536131303207453499 167537273304196954811180249)
          ·
            refine ⟨125652954978147716108385187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167537273304196954811180249 125652954978147716108385187)
            ·
              refine ⟨188479432467221574162577781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125652954978147716108385187 188479432467221574162577781)
              ·
                refine ⟨17669946793802022577741667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188479432467221574162577781 17669946793802022577741667)
                ·
                  refine ⟨26504920190703033866612501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17669946793802022577741667 26504920190703033866612501)
                  ·
                    refine ⟨1242418133939204712497461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26504920190703033866612501 1242418133939204712497461)
                    ·
                      rfl

theorem cell23_7258802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_7258802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258802 prefixEnd_7258802 := by exact prefixLift 7258802
  have htrace : WordTrace (prefixWord ++ tailWord_7258802) baseStart_7258802 baseEnd_7258802 := by
    simpa [prefixWord, tailWord_7258802, baseEnd_7258802] using wordTrace_append hprefix tailTrace_7258802
  have hstable : (prefixWord ++ tailWord_7258802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258802).length < 2 ^ (prefixWord ++ tailWord_7258802).sum := by decide
  have hdescent : baseEnd_7258802 < baseStart_7258802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258849 : List Nat := [1, 2, 3, 1, 4, 3, 1, 8]
def baseStart_7258849 : Nat := 118140960795 + 7258849 * 2 ^ 59
def prefixEnd_7258849 : Nat := 4983230072969 + 3 ^ 40 * 7258849 * 2
def baseEnd_7258849 : Nat := 138047353163273164948321

theorem tailTrace_7258849 : CollatzResearch.WordTrace tailWord_7258849 prefixEnd_7258849 138047353163273164948321 := by
  unfold tailWord_7258849
  simp only [CollatzResearch.WordTrace]
  refine ⟨264751973279437260555739601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176501315519624840370493067 264751973279437260555739601)
  ·
    refine ⟨198563979959577945416804701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264751973279437260555739601 198563979959577945416804701)
    ·
      refine ⟨74461492484841729531301763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198563979959577945416804701 74461492484841729531301763)
      ·
        refine ⟨111692238727262594296952645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74461492484841729531301763 111692238727262594296952645)
        ·
          refine ⟨20942294761361736430678621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111692238727262594296952645 20942294761361736430678621)
          ·
            refine ⟨7853360535510651161504483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20942294761361736430678621 7853360535510651161504483)
            ·
              refine ⟨11780040803265976742256725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853360535510651161504483 11780040803265976742256725)
              ·
                refine ⟨138047353163273164948321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11780040803265976742256725 138047353163273164948321)
                ·
                  rfl

theorem cell23_7258849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 8].length) (baseStart_7258849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258849 prefixEnd_7258849 := by exact prefixLift 7258849
  have htrace : WordTrace (prefixWord ++ tailWord_7258849) baseStart_7258849 baseEnd_7258849 := by
    simpa [prefixWord, tailWord_7258849, baseEnd_7258849] using wordTrace_append hprefix tailTrace_7258849
  have hstable : (prefixWord ++ tailWord_7258849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258849).length < 2 ^ (prefixWord ++ tailWord_7258849).sum := by decide
  have hdescent : baseEnd_7258849 < baseStart_7258849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258856 : List Nat := [2, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4]
def baseStart_7258856 : Nat := 118140960795 + 7258856 * 2 ^ 59
def prefixEnd_7258856 : Nat := 4983230072969 + 3 ^ 40 * 7258856 * 2
def baseEnd_7258856 : Nat := 3727282129772956926217135

theorem tailTrace_7258856 : CollatzResearch.WordTrace tailWord_7258856 prefixEnd_7258856 3727282129772956926217135 := by
  unfold tailWord_7258856
  simp only [CollatzResearch.WordTrace]
  refine ⟨132376114295205950375622211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176501485726941267167496281 132376114295205950375622211)
  ·
    refine ⟨198564171442808925563433317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132376114295205950375622211 198564171442808925563433317)
    ·
      refine ⟨37230782145526673543143747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198564171442808925563433317 37230782145526673543143747)
      ·
        refine ⟨55846173218290010314715621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37230782145526673543143747 55846173218290010314715621)
        ·
          refine ⟨10471157478429376934009179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55846173218290010314715621 10471157478429376934009179)
          ·
            refine ⟨15706736217644065401013769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10471157478429376934009179 15706736217644065401013769)
            ·
              refine ⟨11780052163233049050760327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15706736217644065401013769 11780052163233049050760327)
              ·
                refine ⟨17670078244849573576140491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11780052163233049050760327 17670078244849573576140491)
                ·
                  refine ⟨26505117367274360364210737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17670078244849573576140491 26505117367274360364210737)
                  ·
                    refine ⟨19878838025455770273158053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26505117367274360364210737 19878838025455770273158053)
                    ·
                      refine ⟨3727282129772956926217135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19878838025455770273158053 3727282129772956926217135)
                      ·
                        rfl

theorem cell23_7258856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_7258856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258856 prefixEnd_7258856 := by exact prefixLift 7258856
  have htrace : WordTrace (prefixWord ++ tailWord_7258856) baseStart_7258856 baseEnd_7258856 := by
    simpa [prefixWord, tailWord_7258856, baseEnd_7258856] using wordTrace_append hprefix tailTrace_7258856
  have hstable : (prefixWord ++ tailWord_7258856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258856).length < 2 ^ (prefixWord ++ tailWord_7258856).sum := by decide
  have hdescent : baseEnd_7258856 < baseStart_7258856 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258859 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 3]
def baseStart_7258859 : Nat := 118140960795 + 7258859 * 2 ^ 59
def prefixEnd_7258859 : Nat := 4983230072969 + 3 ^ 40 * 7258859 * 2
def baseEnd_7258859 : Nat := 3727283670214920414479621

theorem tailTrace_7258859 : CollatzResearch.WordTrace tailWord_7258859 prefixEnd_7258859 3727283670214920414479621 := by
  unfold tailWord_7258859
  simp only [CollatzResearch.WordTrace]
  refine ⟨264752338009401032263603631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176501558672934021509069087 264752338009401032263603631)
  ·
    refine ⟨397128507014101548395405447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264752338009401032263603631 397128507014101548395405447)
    ·
      refine ⟨595692760521152322593108171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397128507014101548395405447 595692760521152322593108171)
      ·
        refine ⟨893539140781728483889662257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595692760521152322593108171 893539140781728483889662257)
        ·
          refine ⟨670154355586296362917246693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893539140781728483889662257 670154355586296362917246693)
          ·
            refine ⟨125653941672430568046983755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670154355586296362917246693 125653941672430568046983755)
            ·
              refine ⟨188480912508645852070475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125653941672430568046983755 188480912508645852070475633)
              ·
                refine ⟨141360684381484389052856725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188480912508645852070475633 141360684381484389052856725)
                ·
                  refine ⟨6626282080382080736852659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141360684381484389052856725 6626282080382080736852659)
                  ·
                    refine ⟨9939423120573121105278989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626282080382080736852659 9939423120573121105278989)
                    ·
                      refine ⟨3727283670214920414479621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9939423120573121105278989 3727283670214920414479621)
                      ·
                        rfl

theorem cell23_7258859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 1, 3].length) (baseStart_7258859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258859 prefixEnd_7258859 := by exact prefixLift 7258859
  have htrace : WordTrace (prefixWord ++ tailWord_7258859) baseStart_7258859 baseEnd_7258859 := by
    simpa [prefixWord, tailWord_7258859, baseEnd_7258859] using wordTrace_append hprefix tailTrace_7258859
  have hstable : (prefixWord ++ tailWord_7258859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258859).length < 2 ^ (prefixWord ++ tailWord_7258859).sum := by decide
  have hdescent : baseEnd_7258859 < baseStart_7258859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258872 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5]
def baseStart_7258872 : Nat := 118140960795 + 7258872 * 2 ^ 59
def prefixEnd_7258872 : Nat := 4983230072969 + 3 ^ 40 * 7258872 * 2
def baseEnd_7258872 : Nat := 3727290345463428863617061

theorem tailTrace_7258872 : CollatzResearch.WordTrace tailWord_7258872 prefixEnd_7258872 3727290345463428863617061 := by
  unfold tailWord_7258872
  simp only [CollatzResearch.WordTrace]
  refine ⟨132376406079176967741913435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176501874772235956989217913 132376406079176967741913435)
  ·
    refine ⟨198564609118765451612870153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132376406079176967741913435 198564609118765451612870153)
    ·
      refine ⟨148923456839074088709652615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198564609118765451612870153 148923456839074088709652615)
      ·
        refine ⟨223385185258611133064478923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148923456839074088709652615 223385185258611133064478923)
        ·
          refine ⟨335077777887916699596718385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223385185258611133064478923 335077777887916699596718385)
          ·
            refine ⟨251308333415937524697538789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335077777887916699596718385 251308333415937524697538789)
            ·
              refine ⟨47120312515488285880788523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251308333415937524697538789 47120312515488285880788523)
              ·
                refine ⟨70680468773232428821182785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47120312515488285880788523 70680468773232428821182785)
                ·
                  refine ⟨53010351579924321615887089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70680468773232428821182785 53010351579924321615887089)
                  ·
                    refine ⟨39757763684943241211915317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53010351579924321615887089 39757763684943241211915317)
                    ·
                      refine ⟨3727290345463428863617061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39757763684943241211915317 3727290345463428863617061)
                      ·
                        rfl

theorem cell23_7258872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_7258872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258872 prefixEnd_7258872 := by exact prefixLift 7258872
  have htrace : WordTrace (prefixWord ++ tailWord_7258872) baseStart_7258872 baseEnd_7258872 := by
    simpa [prefixWord, tailWord_7258872, baseEnd_7258872] using wordTrace_append hprefix tailTrace_7258872
  have hstable : (prefixWord ++ tailWord_7258872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258872).length < 2 ^ (prefixWord ++ tailWord_7258872).sum := by decide
  have hdescent : baseEnd_7258872 < baseStart_7258872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258933 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_7258933 : Nat := 118140960795 + 7258933 * 2 ^ 59
def prefixEnd_7258933 : Nat := 4983230072969 + 3 ^ 40 * 7258933 * 2
def baseEnd_7258933 : Nat := 3727321667783353124954281

theorem tailTrace_7258933 : CollatzResearch.WordTrace tailWord_7258933 prefixEnd_7258933 3727321667783353124954281 := by
  unfold tailWord_7258933
  simp only [CollatzResearch.WordTrace]
  refine ⟨264755037011132942901797453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176503358007421961934531635 264755037011132942901797453)
  ·
    refine ⟨99283138879174853588174045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264755037011132942901797453 99283138879174853588174045)
    ·
      refine ⟨37231177079690570095565267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99283138879174853588174045 37231177079690570095565267)
      ·
        refine ⟨55846765619535855143347901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37231177079690570095565267 55846765619535855143347901)
        ·
          refine ⟨20942537107325945678755463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55846765619535855143347901 20942537107325945678755463)
          ·
            refine ⟨31413805660988918518133195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20942537107325945678755463 31413805660988918518133195)
            ·
              refine ⟨47120708491483377777199793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31413805660988918518133195 47120708491483377777199793)
              ·
                refine ⟨35340531368612533332899845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47120708491483377777199793 35340531368612533332899845)
                ·
                  refine ⟨6626349631614849999918721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35340531368612533332899845 6626349631614849999918721)
                  ·
                    refine ⟨4969762223711137499939041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6626349631614849999918721 4969762223711137499939041)
                    ·
                      refine ⟨3727321667783353124954281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969762223711137499939041 3727321667783353124954281)
                      ·
                        rfl

theorem cell23_7258933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_7258933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258933 prefixEnd_7258933 := by exact prefixLift 7258933
  have htrace : WordTrace (prefixWord ++ tailWord_7258933) baseStart_7258933 baseEnd_7258933 := by
    simpa [prefixWord, tailWord_7258933, baseEnd_7258933] using wordTrace_append hprefix tailTrace_7258933
  have hstable : (prefixWord ++ tailWord_7258933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258933).length < 2 ^ (prefixWord ++ tailWord_7258933).sum := by decide
  have hdescent : baseEnd_7258933 < baseStart_7258933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258949 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 3]
def baseStart_7258949 : Nat := 118140960795 + 7258949 * 2 ^ 59
def prefixEnd_7258949 : Nat := 4983230072969 + 3 ^ 40 * 7258949 * 2
def baseEnd_7258949 : Nat := 3727329883473825062354207

theorem tailTrace_7258949 : CollatzResearch.WordTrace tailWord_7258949 prefixEnd_7258949 3727329883473825062354207 := by
  unfold tailWord_7258949
  simp only [CollatzResearch.WordTrace]
  refine ⟨264755620579074977634379901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176503747052716651756253267 264755620579074977634379901)
  ·
    refine ⟨99283357717153116612892463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264755620579074977634379901 99283357717153116612892463)
    ·
      refine ⟨148925036575729674919338695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99283357717153116612892463 148925036575729674919338695)
      ·
        refine ⟨223387554863594512379008043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148925036575729674919338695 223387554863594512379008043)
        ·
          refine ⟨335081332295391768568512065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223387554863594512379008043 335081332295391768568512065)
          ·
            refine ⟨251310999221543826426384049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335081332295391768568512065 251310999221543826426384049)
            ·
              refine ⟨188483249416157869819788037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251310999221543826426384049 188483249416157869819788037)
              ·
                refine ⟨35340609265529600591210257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188483249416157869819788037 35340609265529600591210257)
                ·
                  refine ⟨26505456949147200443407693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35340609265529600591210257 26505456949147200443407693)
                  ·
                    refine ⟨9939546355930200166277885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26505456949147200443407693 9939546355930200166277885)
                    ·
                      refine ⟨3727329883473825062354207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9939546355930200166277885 3727329883473825062354207)
                      ·
                        rfl

theorem cell23_7258949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 3, 3].length) (baseStart_7258949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258949 prefixEnd_7258949 := by exact prefixLift 7258949
  have htrace : WordTrace (prefixWord ++ tailWord_7258949) baseStart_7258949 baseEnd_7258949 := by
    simpa [prefixWord, tailWord_7258949, baseEnd_7258949] using wordTrace_append hprefix tailTrace_7258949
  have hstable : (prefixWord ++ tailWord_7258949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258949).length < 2 ^ (prefixWord ++ tailWord_7258949).sum := by decide
  have hdescent : baseEnd_7258949 < baseStart_7258949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258956 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 7]
def baseStart_7258956 : Nat := 118140960795 + 7258956 * 2 ^ 59
def prefixEnd_7258956 : Nat := 4983230072969 + 3 ^ 40 * 7258956 * 2
def baseEnd_7258956 : Nat := 414148164204267392774075

theorem tailTrace_7258956 : CollatzResearch.WordTrace tailWord_7258956 prefixEnd_7258956 414148164204267392774075 := by
  unfold tailWord_7258956
  simp only [CollatzResearch.WordTrace]
  refine ⟨132377937945024808914942361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176503917260033078553256481 132377937945024808914942361)
  ·
    refine ⟨99283453458768606686206771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132377937945024808914942361 99283453458768606686206771)
    ·
      refine ⟨148925180188152910029310157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99283453458768606686206771 148925180188152910029310157)
      ·
        refine ⟨55846942570557341260991309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148925180188152910029310157 55846942570557341260991309)
        ·
          refine ⟨20942603463959002972871741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55846942570557341260991309 20942603463959002972871741)
          ·
            refine ⟨7853476298984626114826903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20942603463959002972871741 7853476298984626114826903)
            ·
              refine ⟨11780214448476939172240355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853476298984626114826903 11780214448476939172240355)
              ·
                refine ⟨17670321672715408758360533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11780214448476939172240355 17670321672715408758360533)
                ·
                  refine ⟨414148164204267392774075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17670321672715408758360533 414148164204267392774075)
                  ·
                    rfl

theorem cell23_7258956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 7].length) (baseStart_7258956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258956 prefixEnd_7258956 := by exact prefixLift 7258956
  have htrace : WordTrace (prefixWord ++ tailWord_7258956) baseStart_7258956 baseEnd_7258956 := by
    simpa [prefixWord, tailWord_7258956, baseEnd_7258956] using wordTrace_append hprefix tailTrace_7258956
  have hstable : (prefixWord ++ tailWord_7258956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258956).length < 2 ^ (prefixWord ++ tailWord_7258956).sum := by decide
  have hdescent : baseEnd_7258956 < baseStart_7258956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7258967 : List Nat := [1, 1, 3, 2, 4, 3, 2, 1, 2, 2, 2]
def baseStart_7258967 : Nat := 118140960795 + 7258967 * 2 ^ 59
def prefixEnd_7258967 : Nat := 4983230072969 + 3 ^ 40 * 7258967 * 2
def baseEnd_7258967 : Nat := 3727339126125605991929125

theorem tailTrace_7258967 : CollatzResearch.WordTrace tailWord_7258967 prefixEnd_7258967 3727339126125605991929125 := by
  unfold tailWord_7258967
  simp only [CollatzResearch.WordTrace]
  refine ⟨264756277093009766708535155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176504184728673177805690103 264756277093009766708535155)
  ·
    refine ⟨397134415639514650062802733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264756277093009766708535155 397134415639514650062802733)
    ·
      refine ⟨148925405864817993773551025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397134415639514650062802733 148925405864817993773551025)
      ·
        refine ⟨111694054398613495330163269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148925405864817993773551025 111694054398613495330163269)
        ·
          refine ⟨20942635199740030374405613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111694054398613495330163269 20942635199740030374405613)
          ·
            refine ⟨7853488199902511390402105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20942635199740030374405613 7853488199902511390402105)
            ·
              refine ⟨5890116149926883542801579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7853488199902511390402105 5890116149926883542801579)
              ·
                refine ⟨8835174224890325314202369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890116149926883542801579 8835174224890325314202369)
                ·
                  refine ⟨6626380668667743985651777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8835174224890325314202369 6626380668667743985651777)
                  ·
                    refine ⟨4969785501500807989238833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6626380668667743985651777 4969785501500807989238833)
                    ·
                      refine ⟨3727339126125605991929125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969785501500807989238833 3727339126125605991929125)
                      ·
                        rfl

theorem cell23_7258967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_7258967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7258967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7258967 prefixEnd_7258967 := by exact prefixLift 7258967
  have htrace : WordTrace (prefixWord ++ tailWord_7258967) baseStart_7258967 baseEnd_7258967 := by
    simpa [prefixWord, tailWord_7258967, baseEnd_7258967] using wordTrace_append hprefix tailTrace_7258967
  have hstable : (prefixWord ++ tailWord_7258967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7258967).length < 2 ^ (prefixWord ++ tailWord_7258967).sum := by decide
  have hdescent : baseEnd_7258967 < baseStart_7258967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7258967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259059 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 5, 5]
def baseStart_7259059 : Nat := 118140960795 + 7259059 * 2 ^ 59
def prefixEnd_7259059 : Nat := 4983230072969 + 3 ^ 40 * 7259059 * 2
def baseEnd_7259059 : Nat := 1242462122115273210659567

theorem tailTrace_7259059 : CollatzResearch.WordTrace tailWord_7259059 prefixEnd_7259059 1242462122115273210659567 := by
  unfold tailWord_7259059
  simp only [CollatzResearch.WordTrace]
  refine ⟨264759632608676466420884231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176506421739117644280589487 264759632608676466420884231)
  ·
    refine ⟨397139448913014699631326347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264759632608676466420884231 397139448913014699631326347)
    ·
      refine ⟨595709173369522049446989521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397139448913014699631326347 595709173369522049446989521)
      ·
        refine ⟨446781880027141537085242141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595709173369522049446989521 446781880027141537085242141)
        ·
          refine ⟨167543205010178076406965803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446781880027141537085242141 167543205010178076406965803)
          ·
            refine ⟨251314807515267114610448705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167543205010178076406965803 251314807515267114610448705)
            ·
              refine ⟨188486105636450335957836529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251314807515267114610448705 188486105636450335957836529)
              ·
                refine ⟨141364579227337751968377397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188486105636450335957836529 141364579227337751968377397)
                ·
                  refine ⟨13252929302562914247035381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141364579227337751968377397 13252929302562914247035381)
                  ·
                    refine ⟨1242462122115273210659567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13252929302562914247035381 1242462122115273210659567)
                    ·
                      rfl

theorem cell23_7259059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 5].length) (baseStart_7259059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259059 prefixEnd_7259059 := by exact prefixLift 7259059
  have htrace : WordTrace (prefixWord ++ tailWord_7259059) baseStart_7259059 baseEnd_7259059 := by
    simpa [prefixWord, tailWord_7259059, baseEnd_7259059] using wordTrace_append hprefix tailTrace_7259059
  have hstable : (prefixWord ++ tailWord_7259059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259059).length < 2 ^ (prefixWord ++ tailWord_7259059).sum := by decide
  have hdescent : baseEnd_7259059 < baseStart_7259059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259090 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_7259090 : Nat := 118140960795 + 7259090 * 2 ^ 59
def prefixEnd_7259090 : Nat := 4983230072969 + 3 ^ 40 * 7259090 * 2
def baseEnd_7259090 : Nat := 3727402284246109010691059

theorem tailTrace_7259090 : CollatzResearch.WordTrace tailWord_7259090 prefixEnd_7259090 3727402284246109010691059 := by
  unfold tailWord_7259090
  simp only [CollatzResearch.WordTrace]
  refine ⟨66190190817891039678815681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176507175514376105810175149 66190190817891039678815681)
  ·
    refine ⟨49642643113418279759111761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66190190817891039678815681 49642643113418279759111761)
    ·
      refine ⟨37231982335063709819333821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49642643113418279759111761 37231982335063709819333821)
      ·
        refine ⟨13961993375648891182250183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37231982335063709819333821 13961993375648891182250183)
        ·
          refine ⟨20942990063473336773375275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13961993375648891182250183 20942990063473336773375275)
          ·
            refine ⟨31414485095210005160062913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20942990063473336773375275 31414485095210005160062913)
            ·
              refine ⟨23560863821407503870047185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31414485095210005160062913 23560863821407503870047185)
              ·
                refine ⟨17670647866055627902535389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23560863821407503870047185 17670647866055627902535389)
                ·
                  refine ⟨6626492949770860463450771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17670647866055627902535389 6626492949770860463450771)
                  ·
                    refine ⟨9939739424656290695176157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626492949770860463450771 9939739424656290695176157)
                    ·
                      refine ⟨3727402284246109010691059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9939739424656290695176157 3727402284246109010691059)
                      ·
                        rfl

theorem cell23_7259090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_7259090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259090 prefixEnd_7259090 := by exact prefixLift 7259090
  have htrace : WordTrace (prefixWord ++ tailWord_7259090) baseStart_7259090 baseEnd_7259090 := by
    simpa [prefixWord, tailWord_7259090, baseEnd_7259090] using wordTrace_append hprefix tailTrace_7259090
  have hstable : (prefixWord ++ tailWord_7259090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259090).length < 2 ^ (prefixWord ++ tailWord_7259090).sum := by decide
  have hdescent : baseEnd_7259090 < baseStart_7259090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259116 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 3]
def baseStart_7259116 : Nat := 118140960795 + 7259116 * 2 ^ 59
def prefixEnd_7259116 : Nat := 4983230072969 + 3 ^ 40 * 7259116 * 2
def baseEnd_7259116 : Nat := 3727415634743125908965939

theorem tailTrace_7259116 : CollatzResearch.WordTrace tailWord_7259116 prefixEnd_7259116 3727415634743125908965939 := by
  unfold tailWord_7259116
  simp only [CollatzResearch.WordTrace]
  refine ⟨132380855784734982577854601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176507807712979976770472801 132380855784734982577854601)
  ·
    refine ⟨99285641838551236933390951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132380855784734982577854601 99285641838551236933390951)
    ·
      refine ⟨148928462757826855400086427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99285641838551236933390951 148928462757826855400086427)
      ·
        refine ⟨223392694136740283100129641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148928462757826855400086427 223392694136740283100129641)
        ·
          refine ⟨167544520602555212325097231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223392694136740283100129641 167544520602555212325097231)
          ·
            refine ⟨251316780903832818487645847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167544520602555212325097231 251316780903832818487645847)
            ·
              refine ⟨376975171355749227731468771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251316780903832818487645847 376975171355749227731468771)
              ·
                refine ⟨565462757033623841597203157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 376975171355749227731468771 565462757033623841597203157)
                ·
                  refine ⟨13253033367975558787434449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 565462757033623841597203157 13253033367975558787434449)
                  ·
                    refine ⟨9939775025981669090575837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13253033367975558787434449 9939775025981669090575837)
                    ·
                      refine ⟨3727415634743125908965939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9939775025981669090575837 3727415634743125908965939)
                      ·
                        rfl

theorem cell23_7259116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 3].length) (baseStart_7259116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259116 prefixEnd_7259116 := by exact prefixLift 7259116
  have htrace : WordTrace (prefixWord ++ tailWord_7259116) baseStart_7259116 baseEnd_7259116 := by
    simpa [prefixWord, tailWord_7259116, baseEnd_7259116] using wordTrace_append hprefix tailTrace_7259116
  have hstable : (prefixWord ++ tailWord_7259116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259116).length < 2 ^ (prefixWord ++ tailWord_7259116).sum := by decide
  have hdescent : baseEnd_7259116 < baseStart_7259116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259119 : List Nat := [1, 1, 2, 1, 4, 3, 11]
def baseStart_7259119 : Nat := 118140960795 + 7259119 * 2 ^ 59
def prefixEnd_7259119 : Nat := 4983230072969 + 3 ^ 40 * 7259119 * 2
def baseEnd_7259119 : Nat := 46017495989939375274425

theorem tailTrace_7259119 : CollatzResearch.WordTrace tailWord_7259119 prefixEnd_7259119 46017495989939375274425 := by
  unfold tailWord_7259119
  simp only [CollatzResearch.WordTrace]
  refine ⟨264761820988459096668068411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176507880658972731112045607 264761820988459096668068411)
  ·
    refine ⟨397142731482688645002102617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264761820988459096668068411 397142731482688645002102617)
    ·
      refine ⟨297857048612016483751576963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397142731482688645002102617 297857048612016483751576963)
      ·
        refine ⟨446785572918024725627365445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297857048612016483751576963 446785572918024725627365445)
        ·
          refine ⟨83772294922129636055131021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446785572918024725627365445 83772294922129636055131021)
          ·
            refine ⟨31414610595798613520674133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83772294922129636055131021 31414610595798613520674133)
            ·
              refine ⟨46017495989939375274425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31414610595798613520674133 46017495989939375274425)
              ·
                rfl

theorem cell23_7259119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 11].length) (baseStart_7259119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259119 prefixEnd_7259119 := by exact prefixLift 7259119
  have htrace : WordTrace (prefixWord ++ tailWord_7259119) baseStart_7259119 baseEnd_7259119 := by
    simpa [prefixWord, tailWord_7259119, baseEnd_7259119] using wordTrace_append hprefix tailTrace_7259119
  have hstable : (prefixWord ++ tailWord_7259119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259119).length < 2 ^ (prefixWord ++ tailWord_7259119).sum := by decide
  have hdescent : baseEnd_7259119 < baseStart_7259119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259150 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_7259150 : Nat := 118140960795 + 7259150 * 2 ^ 59
def prefixEnd_7259150 : Nat := 4983230072969 + 3 ^ 40 * 7259150 * 2
def baseEnd_7259150 : Nat := 3727433093085378775940783

theorem tailTrace_7259150 : CollatzResearch.WordTrace tailWord_7259150 prefixEnd_7259150 3727433093085378775940783 := by
  unfold tailWord_7259150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33095368956418348620305863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176508634434231192641631269 33095368956418348620305863)
  ·
    refine ⟨49643053434627522930458795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33095368956418348620305863 49643053434627522930458795)
    ·
      refine ⟨74464580151941284395688193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49643053434627522930458795 74464580151941284395688193)
      ·
        refine ⟨55848435113955963296766145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74464580151941284395688193 55848435113955963296766145)
        ·
          refine ⟨41886326335466972472574609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55848435113955963296766145 41886326335466972472574609)
          ·
            refine ⟨31414744751600229354430957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41886326335466972472574609 31414744751600229354430957)
            ·
              refine ⟨11780529281850086007911609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31414744751600229354430957 11780529281850086007911609)
              ·
                refine ⟨8835396961387564505933707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780529281850086007911609 8835396961387564505933707)
                ·
                  refine ⟨13253095442081346758900561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835396961387564505933707 13253095442081346758900561)
                  ·
                    refine ⟨9939821581561010069175421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13253095442081346758900561 9939821581561010069175421)
                    ·
                      refine ⟨3727433093085378775940783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9939821581561010069175421 3727433093085378775940783)
                      ·
                        rfl

theorem cell23_7259150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_7259150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259150 prefixEnd_7259150 := by exact prefixLift 7259150
  have htrace : WordTrace (prefixWord ++ tailWord_7259150) baseStart_7259150 baseEnd_7259150 := by
    simpa [prefixWord, tailWord_7259150, baseEnd_7259150] using wordTrace_append hprefix tailTrace_7259150
  have hstable : (prefixWord ++ tailWord_7259150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259150).length < 2 ^ (prefixWord ++ tailWord_7259150).sum := by decide
  have hdescent : baseEnd_7259150 < baseStart_7259150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259180 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 3]
def baseStart_7259180 : Nat := 118140960795 + 7259180 * 2 ^ 59
def prefixEnd_7259180 : Nat := 4983230072969 + 3 ^ 40 * 7259180 * 2
def baseEnd_7259180 : Nat := 3727448497505013658565645

theorem tailTrace_7259180 : CollatzResearch.WordTrace tailWord_7259180 prefixEnd_7259180 3727448497505013658565645 := by
  unfold tailWord_7259180
  simp only [CollatzResearch.WordTrace]
  refine ⟨132382022920619052043019497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176509363894158736057359329 132382022920619052043019497)
  ·
    refine ⟨99286517190464289032264623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132382022920619052043019497 99286517190464289032264623)
    ·
      refine ⟨148929775785696433548396935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99286517190464289032264623 148929775785696433548396935)
      ·
        refine ⟨223394663678544650322595403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148929775785696433548396935 223394663678544650322595403)
        ·
          refine ⟨335091995517816975483893105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223394663678544650322595403 335091995517816975483893105)
          ·
            refine ⟨251318996638362731612919829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335091995517816975483893105 251318996638362731612919829)
            ·
              refine ⟨11780577967423253044355617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251318996638362731612919829 11780577967423253044355617)
              ·
                refine ⟨8835433475567439783266713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780577967423253044355617 8835433475567439783266713)
                ·
                  refine ⟨6626575106675579837450035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8835433475567439783266713 6626575106675579837450035)
                  ·
                    refine ⟨9939862660013369756175053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626575106675579837450035 9939862660013369756175053)
                    ·
                      refine ⟨3727448497505013658565645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9939862660013369756175053 3727448497505013658565645)
                      ·
                        rfl

theorem cell23_7259180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 3].length) (baseStart_7259180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259180 prefixEnd_7259180 := by exact prefixLift 7259180
  have htrace : WordTrace (prefixWord ++ tailWord_7259180) baseStart_7259180 baseEnd_7259180 := by
    simpa [prefixWord, tailWord_7259180, baseEnd_7259180] using wordTrace_append hprefix tailTrace_7259180
  have hstable : (prefixWord ++ tailWord_7259180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259180).length < 2 ^ (prefixWord ++ tailWord_7259180).sum := by decide
  have hdescent : baseEnd_7259180 < baseStart_7259180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259186 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_7259186 : Nat := 118140960795 + 7259186 * 2 ^ 59
def prefixEnd_7259186 : Nat := 4983230072969 + 3 ^ 40 * 7259186 * 2
def baseEnd_7259186 : Nat := 3727451578388940635090617

theorem tailTrace_7259186 : CollatzResearch.WordTrace tailWord_7259186 prefixEnd_7259186 3727451578388940635090617 := by
  unfold tailWord_7259186
  simp only [CollatzResearch.WordTrace]
  refine ⟨66191066169804091777689353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176509509786144244740504941 66191066169804091777689353)
  ·
    refine ⟨49643299627353068833267015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66191066169804091777689353 49643299627353068833267015)
    ·
      refine ⟨74464949441029603249900523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49643299627353068833267015 74464949441029603249900523)
      ·
        refine ⟨111697424161544404874850785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74464949441029603249900523 111697424161544404874850785)
        ·
          refine ⟨83773068121158303656138089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111697424161544404874850785 83773068121158303656138089)
          ·
            refine ⟨62829801090868727742103567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83773068121158303656138089 62829801090868727742103567)
            ·
              refine ⟨94244701636303091613155351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62829801090868727742103567 94244701636303091613155351)
              ·
                refine ⟨141367052454454637419733027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94244701636303091613155351 141367052454454637419733027)
                ·
                  refine ⟨212050578681681956129599541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141367052454454637419733027 212050578681681956129599541)
                  ·
                    refine ⟨19879741751407683387149957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 212050578681681956129599541 19879741751407683387149957)
                    ·
                      refine ⟨3727451578388940635090617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19879741751407683387149957 3727451578388940635090617)
                      ·
                        rfl

theorem cell23_7259186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_7259186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259186 prefixEnd_7259186 := by exact prefixLift 7259186
  have htrace : WordTrace (prefixWord ++ tailWord_7259186) baseStart_7259186 baseEnd_7259186 := by
    simpa [prefixWord, tailWord_7259186, baseEnd_7259186] using wordTrace_append hprefix tailTrace_7259186
  have hstable : (prefixWord ++ tailWord_7259186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259186).length < 2 ^ (prefixWord ++ tailWord_7259186).sum := by decide
  have hdescent : baseEnd_7259186 < baseStart_7259186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259196 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 8]
def baseStart_7259196 : Nat := 118140960795 + 7259196 * 2 ^ 59
def prefixEnd_7259196 : Nat := 4983230072969 + 3 ^ 40 * 7259196 * 2
def baseEnd_7259196 : Nat := 1242485571065161865321857

theorem tailTrace_7259196 : CollatzResearch.WordTrace tailWord_7259196 prefixEnd_7259196 1242485571065161865321857 := by
  unfold tailWord_7259196
  simp only [CollatzResearch.WordTrace]
  refine ⟨132382314704590069409310721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176509752939453425879080961 132382314704590069409310721)
  ·
    refine ⟨99286736028442552056983041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132382314704590069409310721 99286736028442552056983041)
    ·
      refine ⟨74465052021331914042737281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99286736028442552056983041 74465052021331914042737281)
      ·
        refine ⟨55848789015998935532052961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74465052021331914042737281 55848789015998935532052961)
        ·
          refine ⟨41886591761999201649039721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55848789015998935532052961 41886591761999201649039721)
          ·
            refine ⟨31414943821499401236779791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41886591761999201649039721 31414943821499401236779791)
            ·
              refine ⟨47122415732249101855169687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31414943821499401236779791 47122415732249101855169687)
              ·
                refine ⟨70683623598373652782754531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47122415732249101855169687 70683623598373652782754531)
                ·
                  refine ⟨106025435397560479174131797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70683623598373652782754531 106025435397560479174131797)
                  ·
                    refine ⟨1242485571065161865321857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106025435397560479174131797 1242485571065161865321857)
                    ·
                      rfl

theorem cell23_7259196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_7259196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259196 prefixEnd_7259196 := by exact prefixLift 7259196
  have htrace : WordTrace (prefixWord ++ tailWord_7259196) baseStart_7259196 baseEnd_7259196 := by
    simpa [prefixWord, tailWord_7259196, baseEnd_7259196] using wordTrace_append hprefix tailTrace_7259196
  have hstable : (prefixWord ++ tailWord_7259196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259196).length < 2 ^ (prefixWord ++ tailWord_7259196).sum := by decide
  have hdescent : baseEnd_7259196 < baseStart_7259196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259220 : List Nat := [2, 4, 1, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_7259220 : Nat := 118140960795 + 7259220 * 2 ^ 59
def prefixEnd_7259220 : Nat := 4983230072969 + 3 ^ 40 * 7259220 * 2
def baseEnd_7259220 : Nat := 3727469036731193502065461

theorem tailTrace_7259220 : CollatzResearch.WordTrace tailWord_7259220 prefixEnd_7259220 3727469036731193502065461 := by
  unfold tailWord_7259220
  simp only [CollatzResearch.WordTrace]
  refine ⟨132382752380546595458747557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176510336507395460611663409 132382752380546595458747557)
  ·
    refine ⟨24821766071352486648515167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132382752380546595458747557 24821766071352486648515167)
    ·
      refine ⟨37232649107028729972772751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24821766071352486648515167 37232649107028729972772751)
      ·
        refine ⟨55848973660543094959159127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37232649107028729972772751 55848973660543094959159127)
        ·
          refine ⟨83773460490814642438738691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55848973660543094959159127 83773460490814642438738691)
          ·
            refine ⟨125660190736221963658108037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83773460490814642438738691 125660190736221963658108037)
            ·
              refine ⟨23561285763041618185895257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125660190736221963658108037 23561285763041618185895257)
              ·
                refine ⟨17670964322281213639421443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23561285763041618185895257 17670964322281213639421443)
                ·
                  refine ⟨26506446483421820459132165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17670964322281213639421443 26506446483421820459132165)
                  ·
                    refine ⟨4969958715641591336087281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26506446483421820459132165 4969958715641591336087281)
                    ·
                      refine ⟨3727469036731193502065461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4969958715641591336087281 3727469036731193502065461)
                      ·
                        rfl

theorem cell23_7259220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_7259220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259220 prefixEnd_7259220 := by exact prefixLift 7259220
  have htrace : WordTrace (prefixWord ++ tailWord_7259220) baseStart_7259220 baseEnd_7259220 := by
    simpa [prefixWord, tailWord_7259220, baseEnd_7259220] using wordTrace_append hprefix tailTrace_7259220
  have hstable : (prefixWord ++ tailWord_7259220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259220).length < 2 ^ (prefixWord ++ tailWord_7259220).sum := by decide
  have hdescent : baseEnd_7259220 < baseStart_7259220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259256 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 7]
def baseStart_7259256 : Nat := 118140960795 + 7259256 * 2 ^ 59
def prefixEnd_7259256 : Nat := 4983230072969 + 3 ^ 40 * 7259256 * 2
def baseEnd_7259256 : Nat := 1242495840678251787071765

theorem tailTrace_7259256 : CollatzResearch.WordTrace tailWord_7259256 prefixEnd_7259256 1242495840678251787071765 := by
  unfold tailWord_7259256
  simp only [CollatzResearch.WordTrace]
  refine ⟨132383408894481384532902811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176511211859308512710537081 132383408894481384532902811)
  ·
    refine ⟨198575113341722076799354217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132383408894481384532902811 198575113341722076799354217)
    ·
      refine ⟨148931335006291557599515663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198575113341722076799354217 148931335006291557599515663)
      ·
        refine ⟨223397002509437336399273495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148931335006291557599515663 223397002509437336399273495)
        ·
          refine ⟨335095503764156004598910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223397002509437336399273495 335095503764156004598910243)
          ·
            refine ⟨502643255646234006898365365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335095503764156004598910243 502643255646234006898365365)
            ·
              refine ⟨47122805216834438146721753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 502643255646234006898365365 47122805216834438146721753)
              ·
                refine ⟨35342103912625828610041315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47122805216834438146721753 35342103912625828610041315)
                ·
                  refine ⟨53013155868938742915061973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35342103912625828610041315 53013155868938742915061973)
                  ·
                    refine ⟨1242495840678251787071765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53013155868938742915061973 1242495840678251787071765)
                    ·
                      rfl

theorem cell23_7259256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 7].length) (baseStart_7259256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259256 prefixEnd_7259256 := by exact prefixLift 7259256
  have htrace : WordTrace (prefixWord ++ tailWord_7259256) baseStart_7259256 baseEnd_7259256 := by
    simpa [prefixWord, tailWord_7259256, baseEnd_7259256] using wordTrace_append hprefix tailTrace_7259256
  have hstable : (prefixWord ++ tailWord_7259256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259256).length < 2 ^ (prefixWord ++ tailWord_7259256).sum := by decide
  have hdescent : baseEnd_7259256 < baseStart_7259256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259290 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 2, 5]
def baseStart_7259290 : Nat := 118140960795 + 7259290 * 2 ^ 59
def prefixEnd_7259290 : Nat := 4983230072969 + 3 ^ 40 * 7259290 * 2
def baseEnd_7259290 : Nat := 1242501660125669409396713

theorem tailTrace_7259290 : CollatzResearch.WordTrace tailWord_7259290 prefixEnd_7259290 1242501660125669409396713 := by
  unfold tailWord_7259290
  simp only [CollatzResearch.WordTrace]
  refine ⟨66192014467709898218135831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176512038580559728581695549 66192014467709898218135831)
  ·
    refine ⟨99288021701564847327203747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66192014467709898218135831 99288021701564847327203747)
    ·
      refine ⟨148932032552347270990805621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99288021701564847327203747 148932032552347270990805621)
      ·
        refine ⟨13962378051782556655388027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148932032552347270990805621 13962378051782556655388027)
        ·
          refine ⟨20943567077673834983082041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13962378051782556655388027 20943567077673834983082041)
          ·
            refine ⟨15707675308255376237311531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20943567077673834983082041 15707675308255376237311531)
            ·
              refine ⟨23561512962383064355967297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15707675308255376237311531 23561512962383064355967297)
              ·
                refine ⟨17671134721787298266975473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23561512962383064355967297 17671134721787298266975473)
                ·
                  refine ⟨13253351041340473700231605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17671134721787298266975473 13253351041340473700231605)
                  ·
                    refine ⟨1242501660125669409396713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13253351041340473700231605 1242501660125669409396713)
                    ·
                      rfl

theorem cell23_7259290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 5].length) (baseStart_7259290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259290 prefixEnd_7259290 := by exact prefixLift 7259290
  have htrace : WordTrace (prefixWord ++ tailWord_7259290) baseStart_7259290 baseEnd_7259290 := by
    simpa [prefixWord, tailWord_7259290, baseEnd_7259290] using wordTrace_append hprefix tailTrace_7259290
  have hstable : (prefixWord ++ tailWord_7259290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259290).length < 2 ^ (prefixWord ++ tailWord_7259290).sum := by decide
  have hdescent : baseEnd_7259290 < baseStart_7259290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259294 : List Nat := [4, 3, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7259294 : Nat := 118140960795 + 7259294 * 2 ^ 59
def prefixEnd_7259294 : Nat := 4983230072969 + 3 ^ 40 * 7259294 * 2
def baseEnd_7259294 : Nat := 414167448255514023615569

theorem tailTrace_7259294 : CollatzResearch.WordTrace tailWord_7259294 prefixEnd_7259294 414167448255514023615569 := by
  unfold tailWord_7259294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33096025470353137694461117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176512135841883401037125957 33096025470353137694461117)
  ·
    refine ⟨12411009551382426635422919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33096025470353137694461117 12411009551382426635422919)
    ·
      refine ⟨18616514327073639953134379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12411009551382426635422919 18616514327073639953134379)
      ·
        refine ⟨27924771490610459929701569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18616514327073639953134379 27924771490610459929701569)
        ·
          refine ⟨20943578617957844947276177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27924771490610459929701569 20943578617957844947276177)
          ·
            refine ⟨15707683963468383710457133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20943578617957844947276177 15707683963468383710457133)
            ·
              refine ⟨5890381486300643891421425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15707683963468383710457133 5890381486300643891421425)
              ·
                refine ⟨4417786114725482918566069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890381486300643891421425 4417786114725482918566069)
                ·
                  refine ⟨414167448255514023615569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4417786114725482918566069 414167448255514023615569)
                  ·
                    rfl

theorem cell23_7259294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7259294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259294 prefixEnd_7259294 := by exact prefixLift 7259294
  have htrace : WordTrace (prefixWord ++ tailWord_7259294) baseStart_7259294 baseEnd_7259294 := by
    simpa [prefixWord, tailWord_7259294, baseEnd_7259294] using wordTrace_append hprefix tailTrace_7259294
  have hstable : (prefixWord ++ tailWord_7259294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259294).length < 2 ^ (prefixWord ++ tailWord_7259294).sum := by decide
  have hdescent : baseEnd_7259294 < baseStart_7259294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259413 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7259413 : Nat := 118140960795 + 7259413 * 2 ^ 59
def prefixEnd_7259413 : Nat := 4983230072969 + 3 ^ 40 * 7259413 * 2
def baseEnd_7259413 : Nat := 3727568138497511246952073

theorem tailTrace_7259413 : CollatzResearch.WordTrace tailWord_7259413 prefixEnd_7259413 3727568138497511246952073 := by
  unfold tailWord_7259413
  simp only [CollatzResearch.WordTrace]
  refine ⟨264772544049393984879270893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176515029366262656586180595 264772544049393984879270893)
  ·
    refine ⟨99289704018522744329726585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264772544049393984879270893 99289704018522744329726585)
    ·
      refine ⟨74467278013892058247294939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99289704018522744329726585 74467278013892058247294939)
      ·
        refine ⟨111700917020838087370942409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74467278013892058247294939 111700917020838087370942409)
        ·
          refine ⟨83775687765628565528206807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111700917020838087370942409 83775687765628565528206807)
          ·
            refine ⟨125663531648442848292310211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83775687765628565528206807 125663531648442848292310211)
            ·
              refine ⟨188495297472664272438465317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125663531648442848292310211 188495297472664272438465317)
              ·
                refine ⟨35342868276124551082212247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188495297472664272438465317 35342868276124551082212247)
                ·
                  refine ⟨53014302414186826623318371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35342868276124551082212247 53014302414186826623318371)
                  ·
                    refine ⟨79521453621280239934977557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53014302414186826623318371 79521453621280239934977557)
                    ·
                      refine ⟨3727568138497511246952073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79521453621280239934977557 3727568138497511246952073)
                      ·
                        rfl

theorem cell23_7259413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7259413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259413 prefixEnd_7259413 := by exact prefixLift 7259413
  have htrace : WordTrace (prefixWord ++ tailWord_7259413) baseStart_7259413 baseEnd_7259413 := by
    simpa [prefixWord, tailWord_7259413, baseEnd_7259413] using wordTrace_append hprefix tailTrace_7259413
  have hstable : (prefixWord ++ tailWord_7259413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259413).length < 2 ^ (prefixWord ++ tailWord_7259413).sum := by decide
  have hdescent : baseEnd_7259413 < baseStart_7259413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259420 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7259420 : Nat := 118140960795 + 7259420 * 2 ^ 59
def prefixEnd_7259420 : Nat := 4983230072969 + 3 ^ 40 * 7259420 * 2
def baseEnd_7259420 : Nat := 3727571732862092719564541

theorem tailTrace_7259420 : CollatzResearch.WordTrace tailWord_7259420 prefixEnd_7259420 3727571732862092719564541 := by
  unfold tailWord_7259420
  simp only [CollatzResearch.WordTrace]
  refine ⟨132386399680184312537387857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176515199573579083383183809 132386399680184312537387857)
  ·
    refine ⟨99289799760138234403040893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132386399680184312537387857 99289799760138234403040893)
    ·
      refine ⟨37233674910051837901140335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99289799760138234403040893 37233674910051837901140335)
      ·
        refine ⟨55850512365077756851710503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37233674910051837901140335 55850512365077756851710503)
        ·
          refine ⟨83775768547616635277565755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55850512365077756851710503 83775768547616635277565755)
          ·
            refine ⟨125663652821424952916348633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83775768547616635277565755 125663652821424952916348633)
            ·
              refine ⟨94247739616068714687261475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125663652821424952916348633 94247739616068714687261475)
              ·
                refine ⟨141371609424103072030892213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94247739616068714687261475 141371609424103072030892213)
                ·
                  refine ⟨13253588383509663002896145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 141371609424103072030892213 13253588383509663002896145)
                  ·
                    refine ⟨9940191287632247252172109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13253588383509663002896145 9940191287632247252172109)
                    ·
                      refine ⟨3727571732862092719564541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940191287632247252172109 3727571732862092719564541)
                      ·
                        rfl

theorem cell23_7259420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7259420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259420 prefixEnd_7259420 := by exact prefixLift 7259420
  have htrace : WordTrace (prefixWord ++ tailWord_7259420) baseStart_7259420 baseEnd_7259420 := by
    simpa [prefixWord, tailWord_7259420, baseEnd_7259420] using wordTrace_append hprefix tailTrace_7259420
  have hstable : (prefixWord ++ tailWord_7259420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259420).length < 2 ^ (prefixWord ++ tailWord_7259420).sum := by decide
  have hdescent : baseEnd_7259420 < baseStart_7259420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259434 : List Nat := [3, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7259434 : Nat := 118140960795 + 7259434 * 2 ^ 59
def prefixEnd_7259434 : Nat := 4983230072969 + 3 ^ 40 * 7259434 * 2
def baseEnd_7259434 : Nat := 3727578921591255664789477

theorem tailTrace_7259434 : CollatzResearch.WordTrace tailWord_7259434 prefixEnd_7259434 3727578921591255664789477 := by
  unfold tailWord_7259434
  simp only [CollatzResearch.WordTrace]
  refine ⟨66193327495579476366446339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176515539988211936977190237 66193327495579476366446339)
  ·
    refine ⟨99289991243369214549669509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66193327495579476366446339 99289991243369214549669509)
    ·
      refine ⟨18616873358131727728063033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99289991243369214549669509 18616873358131727728063033)
      ·
        refine ⟨13962655018598795796047275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18616873358131727728063033 13962655018598795796047275)
        ·
          refine ⟨20943982527898193694070913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13962655018598795796047275 20943982527898193694070913)
          ·
            refine ⟨15707986895923645270553185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20943982527898193694070913 15707986895923645270553185)
            ·
              refine ⟨11780990171942733952914889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15707986895923645270553185 11780990171942733952914889)
              ·
                refine ⟨8835742628957050464686167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780990171942733952914889 8835742628957050464686167)
                ·
                  refine ⟨13253613943435575697029251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835742628957050464686167 13253613943435575697029251)
                  ·
                    refine ⟨19880420915153363545543877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13253613943435575697029251 19880420915153363545543877)
                    ·
                      refine ⟨3727578921591255664789477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19880420915153363545543877 3727578921591255664789477)
                      ·
                        rfl

theorem cell23_7259434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7259434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259434 prefixEnd_7259434 := by exact prefixLift 7259434
  have htrace : WordTrace (prefixWord ++ tailWord_7259434) baseStart_7259434 baseEnd_7259434 := by
    simpa [prefixWord, tailWord_7259434, baseEnd_7259434] using wordTrace_append hprefix tailTrace_7259434
  have hstable : (prefixWord ++ tailWord_7259434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259434).length < 2 ^ (prefixWord ++ tailWord_7259434).sum := by decide
  have hdescent : baseEnd_7259434 < baseStart_7259434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259450 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3]
def baseStart_7259450 : Nat := 118140960795 + 7259450 * 2 ^ 59
def prefixEnd_7259450 : Nat := 4983230072969 + 3 ^ 40 * 7259450 * 2
def baseEnd_7259450 : Nat := 3727587137281727602189403

theorem tailTrace_7259450 : CollatzResearch.WordTrace tailWord_7259450 prefixEnd_7259450 3727587137281727602189403 := by
  unfold tailWord_7259450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66193473387564985049591951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176515929033506626798911869 66193473387564985049591951)
  ·
    refine ⟨99290210081347477574387927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66193473387564985049591951 99290210081347477574387927)
    ·
      refine ⟨148935315122021216361581891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99290210081347477574387927 148935315122021216361581891)
      ·
        refine ⟨223402972683031824542372837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148935315122021216361581891 223402972683031824542372837)
        ·
          refine ⟨41888057378068467101694907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223402972683031824542372837 41888057378068467101694907)
          ·
            refine ⟨62832086067102700652542361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41888057378068467101694907 62832086067102700652542361)
            ·
              refine ⟨47124064550327025489406771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62832086067102700652542361 47124064550327025489406771)
              ·
                refine ⟨70686096825490538234110157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47124064550327025489406771 70686096825490538234110157)
                ·
                  refine ⟨26507286309558951837791309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70686096825490538234110157 26507286309558951837791309)
                  ·
                    refine ⟨9940232366084606939171741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26507286309558951837791309 9940232366084606939171741)
                    ·
                      refine ⟨3727587137281727602189403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940232366084606939171741 3727587137281727602189403)
                      ·
                        rfl

theorem cell23_7259450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_7259450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259450 prefixEnd_7259450 := by exact prefixLift 7259450
  have htrace : WordTrace (prefixWord ++ tailWord_7259450) baseStart_7259450 baseEnd_7259450 := by
    simpa [prefixWord, tailWord_7259450, baseEnd_7259450] using wordTrace_append hprefix tailTrace_7259450
  have hstable : (prefixWord ++ tailWord_7259450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259450).length < 2 ^ (prefixWord ++ tailWord_7259450).sum := by decide
  have hdescent : baseEnd_7259450 < baseStart_7259450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259462 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7259462 : Nat := 118140960795 + 7259462 * 2 ^ 59
def prefixEnd_7259462 : Nat := 4983230072969 + 3 ^ 40 * 7259462 * 2
def baseEnd_7259462 : Nat := 3727593299049581555239349

theorem tailTrace_7259462 : CollatzResearch.WordTrace tailWord_7259462 prefixEnd_7259462 3727593299049581555239349 := by
  unfold tailWord_7259462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8274197850819264570243895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176516220817477644165203093 8274197850819264570243895)
  ·
    refine ⟨12411296776228896855365843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8274197850819264570243895 12411296776228896855365843)
    ·
      refine ⟨18616945164343345283048765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12411296776228896855365843 18616945164343345283048765)
      ·
        refine ⟨6981354436628754481143287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18616945164343345283048765 6981354436628754481143287)
        ·
          refine ⟨10472031654943131721714931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981354436628754481143287 10472031654943131721714931)
          ·
            refine ⟨15708047482414697582572397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472031654943131721714931 15708047482414697582572397)
            ·
              refine ⟨5890517805905511593464649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15708047482414697582572397 5890517805905511593464649)
              ·
                refine ⟨4417888354429133695098487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890517805905511593464649 4417888354429133695098487)
                ·
                  refine ⟨6626832531643700542647731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417888354429133695098487 6626832531643700542647731)
                  ·
                    refine ⟨9940248797465550813971597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6626832531643700542647731 9940248797465550813971597)
                    ·
                      refine ⟨3727593299049581555239349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940248797465550813971597 3727593299049581555239349)
                      ·
                        rfl

theorem cell23_7259462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7259462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259462 prefixEnd_7259462 := by exact prefixLift 7259462
  have htrace : WordTrace (prefixWord ++ tailWord_7259462) baseStart_7259462 baseEnd_7259462 := by
    simpa [prefixWord, tailWord_7259462, baseEnd_7259462] using wordTrace_append hprefix tailTrace_7259462
  have hstable : (prefixWord ++ tailWord_7259462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259462).length < 2 ^ (prefixWord ++ tailWord_7259462).sum := by decide
  have hdescent : baseEnd_7259462 < baseStart_7259462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259468 : List Nat := [2, 2, 1, 3, 2, 3, 3, 2, 1, 2, 2]
def baseStart_7259468 : Nat := 118140960795 + 7259468 * 2 ^ 59
def prefixEnd_7259468 : Nat := 4983230072969 + 3 ^ 40 * 7259468 * 2
def baseEnd_7259468 : Nat := 3727596379933508531764321

theorem tailTrace_7259468 : CollatzResearch.WordTrace tailWord_7259468 prefixEnd_7259468 3727596379933508531764321 := by
  unfold tailWord_7259468
  simp only [CollatzResearch.WordTrace]
  refine ⟨132387275032097364636261529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176516366709463152848348705 132387275032097364636261529)
  ·
    refine ⟨99290456274073023477196147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132387275032097364636261529 99290456274073023477196147)
    ·
      refine ⟨148935684411109535215794221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99290456274073023477196147 148935684411109535215794221)
      ·
        refine ⟨55850881654166075705922833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148935684411109535215794221 55850881654166075705922833)
        ·
          refine ⟨41888161240624556779442125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55850881654166075705922833 41888161240624556779442125)
          ·
            refine ⟨15708060465234208792290797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41888161240624556779442125 15708060465234208792290797)
            ·
              refine ⟨5890522674462828297109049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15708060465234208792290797 5890522674462828297109049)
              ·
                refine ⟨4417892005847121222831787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5890522674462828297109049 4417892005847121222831787)
                ·
                  refine ⟨6626838008770681834247681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4417892005847121222831787 6626838008770681834247681)
                  ·
                    refine ⟨4970128506578011375685761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6626838008770681834247681 4970128506578011375685761)
                    ·
                      refine ⟨3727596379933508531764321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970128506578011375685761 3727596379933508531764321)
                      ·
                        rfl

theorem cell23_7259468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_7259468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259468 prefixEnd_7259468 := by exact prefixLift 7259468
  have htrace : WordTrace (prefixWord ++ tailWord_7259468) baseStart_7259468 baseEnd_7259468 := by
    simpa [prefixWord, tailWord_7259468, baseEnd_7259468] using wordTrace_append hprefix tailTrace_7259468
  have hstable : (prefixWord ++ tailWord_7259468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259468).length < 2 ^ (prefixWord ++ tailWord_7259468).sum := by decide
  have hdescent : baseEnd_7259468 < baseStart_7259468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259485 : List Nat := [1, 4, 5, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_7259485 : Nat := 118140960795 + 7259485 * 2 ^ 59
def prefixEnd_7259485 : Nat := 4983230072969 + 3 ^ 40 * 7259485 * 2
def baseEnd_7259485 : Nat := 3727605109104634965251743

theorem tailTrace_7259485 : CollatzResearch.WordTrace tailWord_7259485 prefixEnd_7259485 3727605109104634965251743 := by
  unfold tailWord_7259485
  simp only [CollatzResearch.WordTrace]
  refine ⟨264775170105133141175891909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176516780070088760783927939 264775170105133141175891909)
  ·
    refine ⟨49645344394712463970479733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264775170105133141175891909 49645344394712463970479733)
    ·
      refine ⟨4654251037004293497232475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49645344394712463970479733 4654251037004293497232475)
      ·
        refine ⟨6981376555506440245848713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654251037004293497232475 6981376555506440245848713)
        ·
          refine ⟨5236032416629830184386535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6981376555506440245848713 5236032416629830184386535)
          ·
            refine ⟨7854048624944745276579803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236032416629830184386535 7854048624944745276579803)
            ·
              refine ⟨11781072937417117914869705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854048624944745276579803 11781072937417117914869705)
              ·
                refine ⟨8835804703062838436152279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11781072937417117914869705 8835804703062838436152279)
                ·
                  refine ⟨13253707054594257654228419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8835804703062838436152279 13253707054594257654228419)
                  ·
                    refine ⟨19880560581891386481342629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13253707054594257654228419 19880560581891386481342629)
                    ·
                      refine ⟨3727605109104634965251743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19880560581891386481342629 3727605109104634965251743)
                      ·
                        rfl

theorem cell23_7259485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_7259485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259485 prefixEnd_7259485 := by exact prefixLift 7259485
  have htrace : WordTrace (prefixWord ++ tailWord_7259485) baseStart_7259485 baseEnd_7259485 := by
    simpa [prefixWord, tailWord_7259485, baseEnd_7259485] using wordTrace_append hprefix tailTrace_7259485
  have hstable : (prefixWord ++ tailWord_7259485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259485).length < 2 ^ (prefixWord ++ tailWord_7259485).sum := by decide
  have hdescent : baseEnd_7259485 < baseStart_7259485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259570 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_7259570 : Nat := 118140960795 + 7259570 * 2 ^ 59
def prefixEnd_7259570 : Nat := 4983230072969 + 3 ^ 40 * 7259570 * 2
def baseEnd_7259570 : Nat := 3727648754960267132688851

theorem tailTrace_7259570 : CollatzResearch.WordTrace tailWord_7259570 prefixEnd_7259570 3727648754960267132688851 := by
  unfold tailWord_7259570
  simp only [CollatzResearch.WordTrace]
  refine ⟨66194567577456300173184041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176518846873216800461824109 66194567577456300173184041)
  ·
    refine ⟨49645925683092225129888031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66194567577456300173184041 49645925683092225129888031)
    ·
      refine ⟨74468888524638337694832047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49645925683092225129888031 74468888524638337694832047)
      ·
        refine ⟨111703332786957506542248071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74468888524638337694832047 111703332786957506542248071)
        ·
          refine ⟨167554999180436259813372107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111703332786957506542248071 167554999180436259813372107)
          ·
            refine ⟨251332498770654389720058161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167554999180436259813372107 251332498770654389720058161)
            ·
              refine ⟨188499374077990792290043621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251332498770654389720058161 188499374077990792290043621)
              ·
                refine ⟨35343632639623273554383179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188499374077990792290043621 35343632639623273554383179)
                ·
                  refine ⟨53015448959434910331574769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35343632639623273554383179 53015448959434910331574769)
                  ·
                    refine ⟨39761586719576182748681077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53015448959434910331574769 39761586719576182748681077)
                    ·
                      refine ⟨3727648754960267132688851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39761586719576182748681077 3727648754960267132688851)
                      ·
                        rfl

theorem cell23_7259570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_7259570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259570 prefixEnd_7259570 := by exact prefixLift 7259570
  have htrace : WordTrace (prefixWord ++ tailWord_7259570) baseStart_7259570 baseEnd_7259570 := by
    simpa [prefixWord, tailWord_7259570, baseEnd_7259570] using wordTrace_append hprefix tailTrace_7259570
  have hstable : (prefixWord ++ tailWord_7259570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259570).length < 2 ^ (prefixWord ++ tailWord_7259570).sum := by decide
  have hdescent : baseEnd_7259570 < baseStart_7259570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259617 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_7259617 : Nat := 118140960795 + 7259617 * 2 ^ 59
def prefixEnd_7259617 : Nat := 4983230072969 + 3 ^ 40 * 7259617 * 2
def baseEnd_7259617 : Nat := 3727672888551028448801135

theorem tailTrace_7259617 : CollatzResearch.WordTrace tailWord_7259617 prefixEnd_7259617 3727672888551028448801135 := by
  unfold tailWord_7259617
  simp only [CollatzResearch.WordTrace]
  refine ⟨264779984540654927719697105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176519989693769951813131403 264779984540654927719697105)
  ·
    refine ⟨198584988405491195789772829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264779984540654927719697105 198584988405491195789772829)
    ·
      refine ⟨74469370652059198421164811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198584988405491195789772829 74469370652059198421164811)
      ·
        refine ⟨111704055978088797631747217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74469370652059198421164811 111704055978088797631747217)
        ·
          refine ⟨83778041983566598223810413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111704055978088797631747217 83778041983566598223810413)
          ·
            refine ⟨31416765743837474333928905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83778041983566598223810413 31416765743837474333928905)
            ·
              refine ⟨23562574307878105750446679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31416765743837474333928905 23562574307878105750446679)
              ·
                refine ⟨35343861461817158625670019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23562574307878105750446679 35343861461817158625670019)
                ·
                  refine ⟨53015792192725737938505029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35343861461817158625670019 53015792192725737938505029)
                  ·
                    refine ⟨9940461036136075863469693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53015792192725737938505029 9940461036136075863469693)
                    ·
                      refine ⟨3727672888551028448801135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940461036136075863469693 3727672888551028448801135)
                      ·
                        rfl

theorem cell23_7259617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_7259617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259617 prefixEnd_7259617 := by exact prefixLift 7259617
  have htrace : WordTrace (prefixWord ++ tailWord_7259617) baseStart_7259617 baseEnd_7259617 := by
    simpa [prefixWord, tailWord_7259617, baseEnd_7259617] using wordTrace_append hprefix tailTrace_7259617
  have hstable : (prefixWord ++ tailWord_7259617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259617).length < 2 ^ (prefixWord ++ tailWord_7259617).sum := by decide
  have hdescent : baseEnd_7259617 < baseStart_7259617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259634 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_7259634 : Nat := 118140960795 + 7259634 * 2 ^ 59
def prefixEnd_7259634 : Nat := 4983230072969 + 3 ^ 40 * 7259634 * 2
def baseEnd_7259634 : Nat := 3727681617722154882288557

theorem tailTrace_7259634 : CollatzResearch.WordTrace tailWord_7259634 prefixEnd_7259634 3727681617722154882288557 := by
  unfold tailWord_7259634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66195151145398334905766489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176520403054395559748710637 66195151145398334905766489)
  ·
    refine ⟨49646363359048751179324867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66195151145398334905766489 49646363359048751179324867)
    ·
      refine ⟨74469545038573126768987301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49646363359048751179324867 74469545038573126768987301)
      ·
        refine ⟨13963039694732461269185119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74469545038573126768987301 13963039694732461269185119)
        ·
          refine ⟨20944559542098691903777679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13963039694732461269185119 20944559542098691903777679)
          ·
            refine ⟨31416839313148037855666519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20944559542098691903777679 31416839313148037855666519)
            ·
              refine ⟨47125258969722056783499779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31416839313148037855666519 47125258969722056783499779)
              ·
                refine ⟨70687888454583085175249669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47125258969722056783499779 70687888454583085175249669)
                ·
                  refine ⟨13253979085234328470359313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70687888454583085175249669 13253979085234328470359313)
                  ·
                    refine ⟨9940484313925746352769485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13253979085234328470359313 9940484313925746352769485)
                    ·
                      refine ⟨3727681617722154882288557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940484313925746352769485 3727681617722154882288557)
                      ·
                        rfl

theorem cell23_7259634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_7259634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259634 prefixEnd_7259634 := by exact prefixLift 7259634
  have htrace : WordTrace (prefixWord ++ tailWord_7259634) baseStart_7259634 baseEnd_7259634 := by
    simpa [prefixWord, tailWord_7259634, baseEnd_7259634] using wordTrace_append hprefix tailTrace_7259634
  have hstable : (prefixWord ++ tailWord_7259634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259634).length < 2 ^ (prefixWord ++ tailWord_7259634).sum := by decide
  have hdescent : baseEnd_7259634 < baseStart_7259634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259667 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 3, 5]
def baseStart_7259667 : Nat := 118140960795 + 7259667 * 2 ^ 59
def prefixEnd_7259667 : Nat := 4983230072969 + 3 ^ 40 * 7259667 * 2
def baseEnd_7259667 : Nat := 1242566187527917751058635

theorem tailTrace_7259667 : CollatzResearch.WordTrace tailWord_7259667 prefixEnd_7259667 1242566187527917751058635 := by
  unfold tailWord_7259667
  simp only [CollatzResearch.WordTrace]
  refine ⟨264781808190473786259017255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176521205460315857506011503 264781808190473786259017255)
  ·
    refine ⟨397172712285710679388525883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264781808190473786259017255 397172712285710679388525883)
    ·
      refine ⟨595759068428566019082788825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397172712285710679388525883 595759068428566019082788825)
      ·
        refine ⟨446819301321424514312091619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595759068428566019082788825 446819301321424514312091619)
        ·
          refine ⟨670228951982136771468137429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446819301321424514312091619 670228951982136771468137429)
          ·
            refine ⟨15708491062081330581284471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 670228951982136771468137429 15708491062081330581284471)
            ·
              refine ⟨23562736593121995871926707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15708491062081330581284471 23562736593121995871926707)
              ·
                refine ⟨35344104889682993807890061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23562736593121995871926707 35344104889682993807890061)
                ·
                  refine ⟨13254039333631122677958773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35344104889682993807890061 13254039333631122677958773)
                  ·
                    refine ⟨1242566187527917751058635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13254039333631122677958773 1242566187527917751058635)
                    ·
                      rfl

theorem cell23_7259667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 5].length) (baseStart_7259667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259667 prefixEnd_7259667 := by exact prefixLift 7259667
  have htrace : WordTrace (prefixWord ++ tailWord_7259667) baseStart_7259667 baseEnd_7259667 := by
    simpa [prefixWord, tailWord_7259667, baseEnd_7259667] using wordTrace_append hprefix tailTrace_7259667
  have hstable : (prefixWord ++ tailWord_7259667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259667).length < 2 ^ (prefixWord ++ tailWord_7259667).sum := by decide
  have hdescent : baseEnd_7259667 < baseStart_7259667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259668 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_7259668 : Nat := 118140960795 + 7259668 * 2 ^ 59
def prefixEnd_7259668 : Nat := 4983230072969 + 3 ^ 40 * 7259668 * 2
def baseEnd_7259668 : Nat := 3727699076064407749263401

theorem tailTrace_7259668 : CollatzResearch.WordTrace tailWord_7259668 prefixEnd_7259668 3727699076064407749263401 := by
  unfold tailWord_7259668
  simp only [CollatzResearch.WordTrace]
  refine ⟨132390922331735081714901829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176521229775646775619869105 132390922331735081714901829)
  ·
    refine ⟨24823297937200327821544093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132390922331735081714901829 24823297937200327821544093)
    ·
      refine ⟨9308736726450122933079035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24823297937200327821544093 9308736726450122933079035)
      ·
        refine ⟨13963105089675184399618553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9308736726450122933079035 13963105089675184399618553)
        ·
          refine ⟨10472328817256388299713915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13963105089675184399618553 10472328817256388299713915)
          ·
            refine ⟨15708493225884582449570873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472328817256388299713915 15708493225884582449570873)
            ·
              refine ⟨11781369919413436837178155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15708493225884582449570873 11781369919413436837178155)
              ·
                refine ⟨17672054879120155255767233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11781369919413436837178155 17672054879120155255767233)
                ·
                  refine ⟨13254041159340116441825425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17672054879120155255767233 13254041159340116441825425)
                  ·
                    refine ⟨9940530869505087331369069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13254041159340116441825425 9940530869505087331369069)
                    ·
                      refine ⟨3727699076064407749263401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940530869505087331369069 3727699076064407749263401)
                      ·
                        rfl

theorem cell23_7259668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_7259668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259668 prefixEnd_7259668 := by exact prefixLift 7259668
  have htrace : WordTrace (prefixWord ++ tailWord_7259668) baseStart_7259668 baseEnd_7259668 := by
    simpa [prefixWord, tailWord_7259668, baseEnd_7259668] using wordTrace_append hprefix tailTrace_7259668
  have hstable : (prefixWord ++ tailWord_7259668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259668).length < 2 ^ (prefixWord ++ tailWord_7259668).sum := by decide
  have hdescent : baseEnd_7259668 < baseStart_7259668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259724 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 3, 2, 3]
def baseStart_7259724 : Nat := 118140960795 + 7259724 * 2 ^ 59
def prefixEnd_7259724 : Nat := 4983230072969 + 3 ^ 40 * 7259724 * 2
def baseEnd_7259724 : Nat := 3727727830981059530163143

theorem tailTrace_7259724 : CollatzResearch.WordTrace tailWord_7259724 prefixEnd_7259724 3727727830981059530163143 := by
  unfold tailWord_7259724
  simp only [CollatzResearch.WordTrace]
  refine ⟨132391943575633642496921113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176522591434178189995894817 132391943575633642496921113)
  ·
    refine ⟨99293957681725231872690835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132391943575633642496921113 99293957681725231872690835)
    ·
      refine ⟨148940936522587847809036253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99293957681725231872690835 148940936522587847809036253)
      ·
        refine ⟨55852851195970442928388595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148940936522587847809036253 55852851195970442928388595)
        ·
          refine ⟨83779276793955664392582893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55852851195970442928388595 83779276793955664392582893)
          ·
            refine ⟨31417228797733374147218585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83779276793955664392582893 31417228797733374147218585)
            ·
              refine ⟨23562921598300030610413939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31417228797733374147218585 23562921598300030610413939)
              ·
                refine ⟨35344382397450045915620909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23562921598300030610413939 35344382397450045915620909)
                ·
                  refine ⟨13254143399043767218357841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35344382397450045915620909 13254143399043767218357841)
                  ·
                    refine ⟨9940607549282825413768381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13254143399043767218357841 9940607549282825413768381)
                    ·
                      refine ⟨3727727830981059530163143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940607549282825413768381 3727727830981059530163143)
                      ·
                        rfl

theorem cell23_7259724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_7259724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259724 prefixEnd_7259724 := by exact prefixLift 7259724
  have htrace : WordTrace (prefixWord ++ tailWord_7259724) baseStart_7259724 baseEnd_7259724 := by
    simpa [prefixWord, tailWord_7259724, baseEnd_7259724] using wordTrace_append hprefix tailTrace_7259724
  have hstable : (prefixWord ++ tailWord_7259724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259724).length < 2 ^ (prefixWord ++ tailWord_7259724).sum := by decide
  have hdescent : baseEnd_7259724 < baseStart_7259724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259725 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_7259725 : Nat := 118140960795 + 7259725 * 2 ^ 59
def prefixEnd_7259725 : Nat := 4983230072969 + 3 ^ 40 * 7259725 * 2
def baseEnd_7259725 : Nat := 3727728344461714026250639

theorem tailTrace_7259725 : CollatzResearch.WordTrace tailWord_7259725 prefixEnd_7259725 3727728344461714026250639 := by
  unfold tailWord_7259725
  simp only [CollatzResearch.WordTrace]
  refine ⟨264783923624263662164628629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176522615749509108109752419 264783923624263662164628629)
  ·
    refine ⟨12411746419887359163966967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 264783923624263662164628629 12411746419887359163966967)
    ·
      refine ⟨18617619629831038745950451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12411746419887359163966967 18617619629831038745950451)
      ·
        refine ⟨27926429444746558118925677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18617619629831038745950451 27926429444746558118925677)
        ·
          refine ⟨10472411041779959294597129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27926429444746558118925677 10472411041779959294597129)
          ·
            refine ⟨7854308281334969470947847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10472411041779959294597129 7854308281334969470947847)
            ·
              refine ⟨11781462422002454206421771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854308281334969470947847 11781462422002454206421771)
              ·
                refine ⟨17672193633003681309632657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11781462422002454206421771 17672193633003681309632657)
                ·
                  refine ⟨13254145224752760982224493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17672193633003681309632657 13254145224752760982224493)
                  ·
                    refine ⟨4970304459282285368334185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13254145224752760982224493 4970304459282285368334185)
                    ·
                      refine ⟨3727728344461714026250639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970304459282285368334185 3727728344461714026250639)
                      ·
                        rfl

theorem cell23_7259725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_7259725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259725 prefixEnd_7259725 := by exact prefixLift 7259725
  have htrace : WordTrace (prefixWord ++ tailWord_7259725) baseStart_7259725 baseEnd_7259725 := by
    simpa [prefixWord, tailWord_7259725, baseEnd_7259725] using wordTrace_append hprefix tailTrace_7259725
  have hstable : (prefixWord ++ tailWord_7259725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259725).length < 2 ^ (prefixWord ++ tailWord_7259725).sum := by decide
  have hdescent : baseEnd_7259725 < baseStart_7259725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259811 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 4, 2, 2]
def baseStart_7259811 : Nat := 118140960795 + 7259811 * 2 ^ 59
def prefixEnd_7259811 : Nat := 4983230072969 + 3 ^ 40 * 7259811 * 2
def baseEnd_7259811 : Nat := 3727772503798000689775243

theorem tailTrace_7259811 : CollatzResearch.WordTrace tailWord_7259811 prefixEnd_7259811 3727772503798000689775243 := by
  unfold tailWord_7259811
  simp only [CollatzResearch.WordTrace]
  refine ⟨264787060301952098852259287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176524706867968065901506191 264787060301952098852259287)
  ·
    refine ⟨397180590452928148278388931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264787060301952098852259287 397180590452928148278388931)
    ·
      refine ⟨595770885679392222417583397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397180590452928148278388931 595770885679392222417583397)
      ·
        refine ⟨111707041064886041703296887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 595770885679392222417583397 111707041064886041703296887)
        ·
          refine ⟨167560561597329062554945331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111707041064886041703296887 167560561597329062554945331)
          ·
            refine ⟨251340842395993593832417997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167560561597329062554945331 251340842395993593832417997)
            ·
              refine ⟨94252815898497597687156749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 251340842395993593832417997 94252815898497597687156749)
              ·
                refine ⟨35344805961936599132683781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94252815898497597687156749 35344805961936599132683781)
                ·
                  refine ⟨6627151117863112337378209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35344805961936599132683781 6627151117863112337378209)
                  ·
                    refine ⟨4970363338397334253033657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6627151117863112337378209 4970363338397334253033657)
                    ·
                      refine ⟨3727772503798000689775243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970363338397334253033657 3727772503798000689775243)
                      ·
                        rfl

theorem cell23_7259811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_7259811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259811 prefixEnd_7259811 := by exact prefixLift 7259811
  have htrace : WordTrace (prefixWord ++ tailWord_7259811) baseStart_7259811 baseEnd_7259811 := by
    simpa [prefixWord, tailWord_7259811, baseEnd_7259811] using wordTrace_append hprefix tailTrace_7259811
  have hstable : (prefixWord ++ tailWord_7259811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259811).length < 2 ^ (prefixWord ++ tailWord_7259811).sum := by decide
  have hdescent : baseEnd_7259811 < baseStart_7259811 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259864 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 2, 5]
def baseStart_7259864 : Nat := 118140960795 + 7259864 * 2 ^ 59
def prefixEnd_7259864 : Nat := 4983230072969 + 3 ^ 40 * 7259864 * 2
def baseEnd_7259864 : Nat := 1242599906090896327470833

theorem tailTrace_7259864 : CollatzResearch.WordTrace tailWord_7259864 prefixEnd_7259864 1242599906090896327470833 := by
  unfold tailWord_7259864
  simp only [CollatzResearch.WordTrace]
  refine ⟨132394496685380044451969323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176525995580506725935959097 132394496685380044451969323)
  ·
    refine ⟨198591745028070066677953985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132394496685380044451969323 198591745028070066677953985)
    ·
      refine ⟨148943808771052550008465489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198591745028070066677953985 148943808771052550008465489)
      ·
        refine ⟨111707856578289412506349117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148943808771052550008465489 111707856578289412506349117)
        ·
          refine ⟨41890446216858529689880919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111707856578289412506349117 41890446216858529689880919)
          ·
            refine ⟨62835669325287794534821379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41890446216858529689880919 62835669325287794534821379)
            ·
              refine ⟨94253503987931691802232069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62835669325287794534821379 94253503987931691802232069)
              ·
                refine ⟨17672531997737192212918513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94253503987931691802232069 17672531997737192212918513)
                ·
                  refine ⟨13254398998302894159688885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17672531997737192212918513 13254398998302894159688885)
                  ·
                    refine ⟨1242599906090896327470833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13254398998302894159688885 1242599906090896327470833)
                    ·
                      rfl

theorem cell23_7259864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_7259864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259864 prefixEnd_7259864 := by exact prefixLift 7259864
  have htrace : WordTrace (prefixWord ++ tailWord_7259864) baseStart_7259864 baseEnd_7259864 := by
    simpa [prefixWord, tailWord_7259864, baseEnd_7259864] using wordTrace_append hprefix tailTrace_7259864
  have hstable : (prefixWord ++ tailWord_7259864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259864).length < 2 ^ (prefixWord ++ tailWord_7259864).sum := by decide
  have hdescent : baseEnd_7259864 < baseStart_7259864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259884 : List Nat := [2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 4]
def baseStart_7259884 : Nat := 118140960795 + 7259884 * 2 ^ 59
def prefixEnd_7259884 : Nat := 4983230072969 + 3 ^ 40 * 7259884 * 2
def baseEnd_7259884 : Nat := 3727809987885778904162407

theorem tailTrace_7259884 : CollatzResearch.WordTrace tailWord_7259884 prefixEnd_7259884 3727809987885778904162407 := by
  unfold tailWord_7259884
  simp only [CollatzResearch.WordTrace]
  refine ⟨132394861415343816159833353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176526481887125088213111137 132394861415343816159833353)
  ·
    refine ⟨99296146061507862119875015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132394861415343816159833353 99296146061507862119875015)
    ·
      refine ⟨148944219092261793179812523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99296146061507862119875015 148944219092261793179812523)
      ·
        refine ⟨223416328638392689769718785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148944219092261793179812523 223416328638392689769718785)
        ·
          refine ⟨167562246478794517327289089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223416328638392689769718785 167562246478794517327289089)
          ·
            refine ⟨125671684859095887995466817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167562246478794517327289089 125671684859095887995466817)
            ·
              refine ⟨94253763644321915996600113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125671684859095887995466817 94253763644321915996600113)
              ·
                refine ⟨70690322733241436997450085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94253763644321915996600113 70690322733241436997450085)
                ·
                  refine ⟨13254435512482769437021891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70690322733241436997450085 13254435512482769437021891)
                  ·
                    refine ⟨19881653268724154155532837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13254435512482769437021891 19881653268724154155532837)
                    ·
                      refine ⟨3727809987885778904162407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19881653268724154155532837 3727809987885778904162407)
                      ·
                        rfl

theorem cell23_7259884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 4].length) (baseStart_7259884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259884 prefixEnd_7259884 := by exact prefixLift 7259884
  have htrace : WordTrace (prefixWord ++ tailWord_7259884) baseStart_7259884 baseEnd_7259884 := by
    simpa [prefixWord, tailWord_7259884, baseEnd_7259884] using wordTrace_append hprefix tailTrace_7259884
  have hstable : (prefixWord ++ tailWord_7259884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259884).length < 2 ^ (prefixWord ++ tailWord_7259884).sum := by decide
  have hdescent : baseEnd_7259884 < baseStart_7259884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259904 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3]
def baseStart_7259904 : Nat := 118140960795 + 7259904 * 2 ^ 59
def prefixEnd_7259904 : Nat := 4983230072969 + 3 ^ 40 * 7259904 * 2
def baseEnd_7259904 : Nat := 3727820257498868825912315

theorem tailTrace_7259904 : CollatzResearch.WordTrace tailWord_7259904 prefixEnd_7259904 3727820257498868825912315 := by
  unfold tailWord_7259904
  simp only [CollatzResearch.WordTrace]
  refine ⟨132395226145307587867697383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176526968193743450490263177 132395226145307587867697383)
  ·
    refine ⟨198592839217961381801546075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132395226145307587867697383 198592839217961381801546075)
    ·
      refine ⟨297889258826942072702319113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198592839217961381801546075 297889258826942072702319113)
      ·
        refine ⟨223416944120206554526739335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297889258826942072702319113 223416944120206554526739335)
        ·
          refine ⟨335125416180309831790109003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223416944120206554526739335 335125416180309831790109003)
          ·
            refine ⟨502688124270464747685163505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335125416180309831790109003 502688124270464747685163505)
            ·
              refine ⟨377016093202848560763872629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 502688124270464747685163505 377016093202848560763872629)
              ·
                refine ⟨35345258737767052571613059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377016093202848560763872629 35345258737767052571613059)
                ·
                  refine ⟨53017888106650578857419589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35345258737767052571613059 53017888106650578857419589)
                  ·
                    refine ⟨9940854019996983535766173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53017888106650578857419589 9940854019996983535766173)
                    ·
                      refine ⟨3727820257498868825912315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940854019996983535766173 3727820257498868825912315)
                      ·
                        rfl

theorem cell23_7259904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_7259904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259904 prefixEnd_7259904 := by exact prefixLift 7259904
  have htrace : WordTrace (prefixWord ++ tailWord_7259904) baseStart_7259904 baseEnd_7259904 := by
    simpa [prefixWord, tailWord_7259904, baseEnd_7259904] using wordTrace_append hprefix tailTrace_7259904
  have hstable : (prefixWord ++ tailWord_7259904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259904).length < 2 ^ (prefixWord ++ tailWord_7259904).sum := by decide
  have hdescent : baseEnd_7259904 < baseStart_7259904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259914 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7259914 : Nat := 118140960795 + 7259914 * 2 ^ 59
def prefixEnd_7259914 : Nat := 4983230072969 + 3 ^ 40 * 7259914 * 2
def baseEnd_7259914 : Nat := 3727825392305413786787269

theorem tailTrace_7259914 : CollatzResearch.WordTrace tailWord_7259914 prefixEnd_7259914 3727825392305413786787269 := by
  unfold tailWord_7259914
  simp only [CollatzResearch.WordTrace]
  refine ⟨66197704255144736860814699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176527211347052631628839197 66197704255144736860814699)
  ·
    refine ⟨99296556382717105291222049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66197704255144736860814699 99296556382717105291222049)
    ·
      refine ⟨74472417287037828968416537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99296556382717105291222049 74472417287037828968416537)
      ·
        refine ⟨55854312965278371726312403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74472417287037828968416537 55854312965278371726312403)
        ·
          refine ⟨83781469447917557589468605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55854312965278371726312403 83781469447917557589468605)
          ·
            refine ⟨31418051042969084096050727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83781469447917557589468605 31418051042969084096050727)
            ·
              refine ⟨47127076564453626144076091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31418051042969084096050727 47127076564453626144076091)
              ·
                refine ⟨70690614846680439216114137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47127076564453626144076091 70690614846680439216114137)
                ·
                  refine ⟨53017961135010329412085603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70690614846680439216114137 53017961135010329412085603)
                  ·
                    refine ⟨79526941702515494118128405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53017961135010329412085603 79526941702515494118128405)
                    ·
                      refine ⟨3727825392305413786787269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79526941702515494118128405 3727825392305413786787269)
                      ·
                        rfl

theorem cell23_7259914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7259914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259914 prefixEnd_7259914 := by exact prefixLift 7259914
  have htrace : WordTrace (prefixWord ++ tailWord_7259914) baseStart_7259914 baseEnd_7259914 := by
    simpa [prefixWord, tailWord_7259914, baseEnd_7259914] using wordTrace_append hprefix tailTrace_7259914
  have hstable : (prefixWord ++ tailWord_7259914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259914).length < 2 ^ (prefixWord ++ tailWord_7259914).sum := by decide
  have hdescent : baseEnd_7259914 < baseStart_7259914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259928 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 1, 4]
def baseStart_7259928 : Nat := 118140960795 + 7259928 * 2 ^ 59
def prefixEnd_7259928 : Nat := 4983230072969 + 3 ^ 40 * 7259928 * 2
def baseEnd_7259928 : Nat := 1242610860344858910670735

theorem tailTrace_7259928 : CollatzResearch.WordTrace tailWord_7259928 prefixEnd_7259928 1242610860344858910670735 := by
  unfold tailWord_7259928
  simp only [CollatzResearch.WordTrace]
  refine ⟨132395663821264113917134219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176527551761685485222845625 132395663821264113917134219)
  ·
    refine ⟨198593495731896170875701329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132395663821264113917134219 198593495731896170875701329)
    ·
      refine ⟨148945121798922128156775997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198593495731896170875701329 148945121798922128156775997)
      ·
        refine ⟨55854420674595798058790999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148945121798922128156775997 55854420674595798058790999)
        ·
          refine ⟨83781631011893697088186499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55854420674595798058790999 83781631011893697088186499)
          ·
            refine ⟨125672446517840545632279749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83781631011893697088186499 125672446517840545632279749)
            ·
              refine ⟨23563583722095102306052453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125672446517840545632279749 23563583722095102306052453)
              ·
                refine ⟨4418171947892831682384835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23563583722095102306052453 4418171947892831682384835)
                ·
                  refine ⟨6627257921839247523577253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418171947892831682384835 6627257921839247523577253)
                  ·
                    refine ⟨1242610860344858910670735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6627257921839247523577253 1242610860344858910670735)
                    ·
                      rfl

theorem cell23_7259928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 4].length) (baseStart_7259928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259928 prefixEnd_7259928 := by exact prefixLift 7259928
  have htrace : WordTrace (prefixWord ++ tailWord_7259928) baseStart_7259928 baseEnd_7259928 := by
    simpa [prefixWord, tailWord_7259928, baseEnd_7259928] using wordTrace_append hprefix tailTrace_7259928
  have hstable : (prefixWord ++ tailWord_7259928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259928).length < 2 ^ (prefixWord ++ tailWord_7259928).sum := by decide
  have hdescent : baseEnd_7259928 < baseStart_7259928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259971 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 1, 5]
def baseStart_7259971 : Nat := 118140960795 + 7259971 * 2 ^ 59
def prefixEnd_7259971 : Nat := 4983230072969 + 3 ^ 40 * 7259971 * 2
def baseEnd_7259971 : Nat := 1242618220234240021258169

theorem tailTrace_7259971 : CollatzResearch.WordTrace tailWord_7259971 prefixEnd_7259971 1242618220234240021258169 := by
  unfold tailWord_7259971
  simp only [CollatzResearch.WordTrace]
  refine ⟨264792895981372446178083767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176528597320914964118722511 264792895981372446178083767)
  ·
    refine ⟨397189343972058669267125651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264792895981372446178083767 397189343972058669267125651)
    ·
      refine ⟨595784015958088003900688477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397189343972058669267125651 595784015958088003900688477)
      ·
        refine ⟨223419005984283001462758179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 595784015958088003900688477 223419005984283001462758179)
        ·
          refine ⟨335128508976424502194137269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223419005984283001462758179 335128508976424502194137269)
          ·
            refine ⟨31418297716539797080700369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 335128508976424502194137269 31418297716539797080700369)
            ·
              refine ⟨23563723287404847810525277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31418297716539797080700369 23563723287404847810525277)
              ·
                refine ⟨8836396232776817928946979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23563723287404847810525277 8836396232776817928946979)
                ·
                  refine ⟨13254594349165226893420469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8836396232776817928946979 13254594349165226893420469)
                  ·
                    refine ⟨1242618220234240021258169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13254594349165226893420469 1242618220234240021258169)
                    ·
                      rfl

theorem cell23_7259971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 5].length) (baseStart_7259971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259971 prefixEnd_7259971 := by exact prefixLift 7259971
  have htrace : WordTrace (prefixWord ++ tailWord_7259971) baseStart_7259971 baseEnd_7259971 := by
    simpa [prefixWord, tailWord_7259971, baseEnd_7259971] using wordTrace_append hprefix tailTrace_7259971
  have hstable : (prefixWord ++ tailWord_7259971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259971).length < 2 ^ (prefixWord ++ tailWord_7259971).sum := by decide
  have hdescent : baseEnd_7259971 < baseStart_7259971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259978 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_7259978 : Nat := 118140960795 + 7259978 * 2 ^ 59
def prefixEnd_7259978 : Nat := 4983230072969 + 3 ^ 40 * 7259978 * 2
def baseEnd_7259978 : Nat := 3727858255067301536386975

theorem tailTrace_7259978 : CollatzResearch.WordTrace tailWord_7259978 prefixEnd_7259978 3727858255067301536386975 := by
  unfold tailWord_7259978
  simp only [CollatzResearch.WordTrace]
  refine ⟨66198287823086771593397147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176528767528231390915725725 66198287823086771593397147)
  ·
    refine ⟨99297431734630157390095721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66198287823086771593397147 99297431734630157390095721)
    ·
      refine ⟨74473073800972618042571791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99297431734630157390095721 74473073800972618042571791)
      ·
        refine ⟨111709610701458927063857687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74473073800972618042571791 111709610701458927063857687)
        ·
          refine ⟨167564416052188390595786531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111709610701458927063857687 167564416052188390595786531)
          ·
            refine ⟨251346624078282585893679797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167564416052188390595786531 251346624078282585893679797)
            ·
              refine ⟨23563746007338992427532481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251346624078282585893679797 23563746007338992427532481)
              ·
                refine ⟨17672809505504244320649361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23563746007338992427532481 17672809505504244320649361)
                ·
                  refine ⟨13254607129128183240487021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17672809505504244320649361 13254607129128183240487021)
                  ·
                    refine ⟨4970477673423068715182633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13254607129128183240487021 4970477673423068715182633)
                    ·
                      refine ⟨3727858255067301536386975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970477673423068715182633 3727858255067301536386975)
                      ·
                        rfl

theorem cell23_7259978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_7259978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259978 prefixEnd_7259978 := by exact prefixLift 7259978
  have htrace : WordTrace (prefixWord ++ tailWord_7259978) baseStart_7259978 baseEnd_7259978 := by
    simpa [prefixWord, tailWord_7259978, baseEnd_7259978] using wordTrace_append hprefix tailTrace_7259978
  have hstable : (prefixWord ++ tailWord_7259978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259978).length < 2 ^ (prefixWord ++ tailWord_7259978).sum := by decide
  have hdescent : baseEnd_7259978 < baseStart_7259978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7259985 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_7259985 : Nat := 118140960795 + 7259985 * 2 ^ 59
def prefixEnd_7259985 : Nat := 4983230072969 + 3 ^ 40 * 7259985 * 2
def baseEnd_7259985 : Nat := 3727861849431883008999443

theorem tailTrace_7259985 : CollatzResearch.WordTrace tailWord_7259985 prefixEnd_7259985 3727861849431883008999443 := by
  unfold tailWord_7259985
  simp only [CollatzResearch.WordTrace]
  refine ⟨264793406603321726569093409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176528937735547817712728939 264793406603321726569093409)
  ·
    refine ⟨198595054952491294926820057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264793406603321726569093409 198595054952491294926820057)
    ·
      refine ⟨148946291214368471195115043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198595054952491294926820057 148946291214368471195115043)
      ·
        refine ⟨223419436821552706792672565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148946291214368471195115043 223419436821552706792672565)
        ·
          refine ⟨20945572202020566261813053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 223419436821552706792672565 20945572202020566261813053)
          ·
            refine ⟨7854589575757712348179895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20945572202020566261813053 7854589575757712348179895)
            ·
              refine ⟨11781884363636568522269843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7854589575757712348179895 11781884363636568522269843)
              ·
                refine ⟨17672826545454852783404765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11781884363636568522269843 17672826545454852783404765)
                ·
                  refine ⟨6627309954545569793776787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17672826545454852783404765 6627309954545569793776787)
                  ·
                    refine ⟨9940964931818354690665181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627309954545569793776787 9940964931818354690665181)
                    ·
                      refine ⟨3727861849431883008999443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9940964931818354690665181 3727861849431883008999443)
                      ·
                        rfl

theorem cell23_7259985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_7259985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7259985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7259985 prefixEnd_7259985 := by exact prefixLift 7259985
  have htrace : WordTrace (prefixWord ++ tailWord_7259985) baseStart_7259985 baseEnd_7259985 := by
    simpa [prefixWord, tailWord_7259985, baseEnd_7259985] using wordTrace_append hprefix tailTrace_7259985
  have hstable : (prefixWord ++ tailWord_7259985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7259985).length < 2 ^ (prefixWord ++ tailWord_7259985).sum := by decide
  have hdescent : baseEnd_7259985 < baseStart_7259985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7259985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260022 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 1, 5]
def baseStart_7260022 : Nat := 118140960795 + 7260022 * 2 ^ 59
def prefixEnd_7260022 : Nat := 4983230072969 + 3 ^ 40 * 7260022 * 2
def baseEnd_7260022 : Nat := 1242626949405366454745591

theorem tailTrace_7260022 : CollatzResearch.WordTrace tailWord_7260022 prefixEnd_7260022 1242626949405366454745591 := by
  unfold tailWord_7260022
  simp only [CollatzResearch.WordTrace]
  refine ⟨16549672256511730118011895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176529837402791787925460213 16549672256511730118011895)
  ·
    refine ⟨24824508384767595177017843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16549672256511730118011895 24824508384767595177017843)
    ·
      refine ⟨37236762577151392765526765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24824508384767595177017843 37236762577151392765526765)
      ·
        refine ⟨13963785966431772287072537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37236762577151392765526765 13963785966431772287072537)
        ·
          refine ⟨10472839474823829215304403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13963785966431772287072537 10472839474823829215304403)
          ·
            refine ⟨15709259212235743822956605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472839474823829215304403 15709259212235743822956605)
            ·
              refine ⟨5890972204588403933608727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15709259212235743822956605 5890972204588403933608727)
              ·
                refine ⟨8836458306882605900413091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5890972204588403933608727 8836458306882605900413091)
                ·
                  refine ⟨13254687460323908850619637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8836458306882605900413091 13254687460323908850619637)
                  ·
                    refine ⟨1242626949405366454745591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13254687460323908850619637 1242626949405366454745591)
                    ·
                      rfl

theorem cell23_7260022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_7260022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260022 prefixEnd_7260022 := by exact prefixLift 7260022
  have htrace : WordTrace (prefixWord ++ tailWord_7260022) baseStart_7260022 baseEnd_7260022 := by
    simpa [prefixWord, tailWord_7260022, baseEnd_7260022] using wordTrace_append hprefix tailTrace_7260022
  have hstable : (prefixWord ++ tailWord_7260022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260022).length < 2 ^ (prefixWord ++ tailWord_7260022).sum := by decide
  have hdescent : baseEnd_7260022 < baseStart_7260022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260041 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 3]
def baseStart_7260041 : Nat := 118140960795 + 7260041 * 2 ^ 59
def prefixEnd_7260041 : Nat := 4983230072969 + 3 ^ 40 * 7260041 * 2
def baseEnd_7260041 : Nat := 3727890604348534789899185

theorem tailTrace_7260041 : CollatzResearch.WordTrace tailWord_7260041 prefixEnd_7260041 3727890604348534789899185 := by
  unfold tailWord_7260041
  simp only [CollatzResearch.WordTrace]
  refine ⟨264795449091118848133131977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176530299394079232088754651 264795449091118848133131977)
  ·
    refine ⟨198596586818339136099848983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264795449091118848133131977 198596586818339136099848983)
    ·
      refine ⟨297894880227508704149773475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198596586818339136099848983 297894880227508704149773475)
      ·
        refine ⟨446842320341263056224660213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297894880227508704149773475 446842320341263056224660213)
        ·
          refine ⟨41891467531993411521061895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446842320341263056224660213 41891467531993411521061895)
          ·
            refine ⟨62837201297990117281592843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41891467531993411521061895 62837201297990117281592843)
            ·
              refine ⟨94255801946985175922389265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62837201297990117281592843 94255801946985175922389265)
              ·
                refine ⟨70691851460238881941791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94255801946985175922389265 70691851460238881941791949)
                ·
                  refine ⟨26509444297589580728171981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70691851460238881941791949 26509444297589580728171981)
                  ·
                    refine ⟨9941041611596092773064493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26509444297589580728171981 9941041611596092773064493)
                    ·
                      refine ⟨3727890604348534789899185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941041611596092773064493 3727890604348534789899185)
                      ·
                        rfl

theorem cell23_7260041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 3, 3].length) (baseStart_7260041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260041 prefixEnd_7260041 := by exact prefixLift 7260041
  have htrace : WordTrace (prefixWord ++ tailWord_7260041) baseStart_7260041 baseEnd_7260041 := by
    simpa [prefixWord, tailWord_7260041, baseEnd_7260041] using wordTrace_append hprefix tailTrace_7260041
  have hstable : (prefixWord ++ tailWord_7260041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260041).length < 2 ^ (prefixWord ++ tailWord_7260041).sum := by decide
  have hdescent : baseEnd_7260041 < baseStart_7260041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260058 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3]
def baseStart_7260058 : Nat := 118140960795 + 7260058 * 2 ^ 59
def prefixEnd_7260058 : Nat := 4983230072969 + 3 ^ 40 * 7260058 * 2
def baseEnd_7260058 : Nat := 3727899333519661223386607

theorem tailTrace_7260058 : CollatzResearch.WordTrace tailWord_7260058 prefixEnd_7260058 3727899333519661223386607 := by
  unfold tailWord_7260058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66199017283014315009125207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176530712754704840024333885 66199017283014315009125207)
  ·
    refine ⟨99298525924521472513687811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66199017283014315009125207 99298525924521472513687811)
    ·
      refine ⟨148947788886782208770531717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99298525924521472513687811 148947788886782208770531717)
      ·
        refine ⟨27927710416271664144474697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148947788886782208770531717 27927710416271664144474697)
        ·
          refine ⟨20945782812203748108356023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27927710416271664144474697 20945782812203748108356023)
          ·
            refine ⟨31418674218305622162534035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20945782812203748108356023 31418674218305622162534035)
            ·
              refine ⟨47128011327458433243801053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31418674218305622162534035 47128011327458433243801053)
              ·
                refine ⟨17673004247796912466425395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47128011327458433243801053 17673004247796912466425395)
                ·
                  refine ⟨26509506371695368699638093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17673004247796912466425395 26509506371695368699638093)
                  ·
                    refine ⟨9941064889385763262364285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26509506371695368699638093 9941064889385763262364285)
                    ·
                      refine ⟨3727899333519661223386607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941064889385763262364285 3727899333519661223386607)
                      ·
                        rfl

theorem cell23_7260058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_7260058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260058 prefixEnd_7260058 := by exact prefixLift 7260058
  have htrace : WordTrace (prefixWord ++ tailWord_7260058) baseStart_7260058 baseEnd_7260058 := by
    simpa [prefixWord, tailWord_7260058, baseEnd_7260058] using wordTrace_append hprefix tailTrace_7260058
  have hstable : (prefixWord ++ tailWord_7260058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260058).length < 2 ^ (prefixWord ++ tailWord_7260058).sum := by decide
  have hdescent : baseEnd_7260058 < baseStart_7260058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260092 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7260092 : Nat := 118140960795 + 7260092 * 2 ^ 59
def prefixEnd_7260092 : Nat := 4983230072969 + 3 ^ 40 * 7260092 * 2
def baseEnd_7260092 : Nat := 3727916791861914090361451

theorem tailTrace_7260092 : CollatzResearch.WordTrace tailWord_7260092 prefixEnd_7260092 3727916791861914090361451 := by
  unfold tailWord_7260092
  simp only [CollatzResearch.WordTrace]
  refine ⟨132398654606967041921619265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176531539475956055895492353 132398654606967041921619265)
  ·
    refine ⟨99298990955225281441214449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132398654606967041921619265 99298990955225281441214449)
    ·
      refine ⟨74474243216418961080910837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99298990955225281441214449 74474243216418961080910837)
      ·
        refine ⟨6981960301539277601335391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74474243216418961080910837 6981960301539277601335391)
        ·
          refine ⟨10472940452308916402003087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6981960301539277601335391 10472940452308916402003087)
          ·
            refine ⟨15709410678463374603004631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10472940452308916402003087 15709410678463374603004631)
            ·
              refine ⟨23564116017695061904506947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15709410678463374603004631 23564116017695061904506947)
              ·
                refine ⟨35346174026542592856760421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23564116017695061904506947 35346174026542592856760421)
                ·
                  refine ⟨6627407629976736160642579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35346174026542592856760421 6627407629976736160642579)
                  ·
                    refine ⟨9941111444965104240963869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627407629976736160642579 9941111444965104240963869)
                    ·
                      refine ⟨3727916791861914090361451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941111444965104240963869 3727916791861914090361451)
                      ·
                        rfl

theorem cell23_7260092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7260092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260092 prefixEnd_7260092 := by exact prefixLift 7260092
  have htrace : WordTrace (prefixWord ++ tailWord_7260092) baseStart_7260092 baseEnd_7260092 := by
    simpa [prefixWord, tailWord_7260092, baseEnd_7260092] using wordTrace_append hprefix tailTrace_7260092
  have hstable : (prefixWord ++ tailWord_7260092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260092).length < 2 ^ (prefixWord ++ tailWord_7260092).sum := by decide
  have hdescent : baseEnd_7260092 < baseStart_7260092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260101 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 3]
def baseStart_7260101 : Nat := 118140960795 + 7260101 * 2 ^ 59
def prefixEnd_7260101 : Nat := 4983230072969 + 3 ^ 40 * 7260101 * 2
def baseEnd_7260101 : Nat := 3727921413187804555148909

theorem tailTrace_7260101 : CollatzResearch.WordTrace tailWord_7260101 prefixEnd_7260101 3727921413187804555148909 := by
  unfold tailWord_7260101
  simp only [CollatzResearch.WordTrace]
  refine ⟨264797637470901478380316157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176531758313934318920210771 264797637470901478380316157)
  ·
    refine ⟨99299114051588054392618559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264797637470901478380316157 99299114051588054392618559)
    ·
      refine ⟨148948671077382081588927839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99299114051588054392618559 148948671077382081588927839)
      ·
        refine ⟨223423006616073122383391759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148948671077382081588927839 223423006616073122383391759)
        ·
          refine ⟨335134509924109683575087639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223423006616073122383391759 335134509924109683575087639)
          ·
            refine ⟨502701764886164525362631459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335134509924109683575087639 502701764886164525362631459)
            ·
              refine ⟨754052647329246788043947189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502701764886164525362631459 754052647329246788043947189)
              ·
                refine ⟨70692435687116886379120049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754052647329246788043947189 70692435687116886379120049)
                ·
                  refine ⟨53019326765337664784340037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70692435687116886379120049 53019326765337664784340037)
                  ·
                    refine ⟨9941123768500812147063757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53019326765337664784340037 9941123768500812147063757)
                    ·
                      refine ⟨3727921413187804555148909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941123768500812147063757 3727921413187804555148909)
                      ·
                        rfl

theorem cell23_7260101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 4, 3].length) (baseStart_7260101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260101 prefixEnd_7260101 := by exact prefixLift 7260101
  have htrace : WordTrace (prefixWord ++ tailWord_7260101) baseStart_7260101 baseEnd_7260101 := by
    simpa [prefixWord, tailWord_7260101, baseEnd_7260101] using wordTrace_append hprefix tailTrace_7260101
  have hstable : (prefixWord ++ tailWord_7260101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260101).length < 2 ^ (prefixWord ++ tailWord_7260101).sum := by decide
  have hdescent : baseEnd_7260101 < baseStart_7260101 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260111 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4]
def baseStart_7260111 : Nat := 118140960795 + 7260111 * 2 ^ 59
def prefixEnd_7260111 : Nat := 4983230072969 + 3 ^ 40 * 7260111 * 2
def baseEnd_7260111 : Nat := 3727926547994349516023863

theorem tailTrace_7260111 : CollatzResearch.WordTrace tailWord_7260111 prefixEnd_7260111 3727926547994349516023863 := by
  unfold tailWord_7260111
  simp only [CollatzResearch.WordTrace]
  refine ⟨264798002200865250088180187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176532001467243500058786791 264798002200865250088180187)
  ·
    refine ⟨397197003301297875132270281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264798002200865250088180187 397197003301297875132270281)
    ·
      refine ⟨297897752475973406349202711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397197003301297875132270281 297897752475973406349202711)
      ·
        refine ⟨446846628713960109523804067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297897752475973406349202711 446846628713960109523804067)
        ·
          refine ⟨670269943070940164285706101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446846628713960109523804067 670269943070940164285706101)
          ·
            refine ⟨62837807162900640401784947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 670269943070940164285706101 62837807162900640401784947)
            ·
              refine ⟨94256710744350960602677421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62837807162900640401784947 94256710744350960602677421)
              ·
                refine ⟨35346266529131610226004033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94256710744350960602677421 35346266529131610226004033)
                ·
                  refine ⟨26509699896848707669503025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35346266529131610226004033 26509699896848707669503025)
                  ·
                    refine ⟨19882274922636530752127269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26509699896848707669503025 19882274922636530752127269)
                    ·
                      refine ⟨3727926547994349516023863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19882274922636530752127269 3727926547994349516023863)
                      ·
                        rfl

theorem cell23_7260111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 2, 4].length) (baseStart_7260111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260111 prefixEnd_7260111 := by exact prefixLift 7260111
  have htrace : WordTrace (prefixWord ++ tailWord_7260111) baseStart_7260111 baseEnd_7260111 := by
    simpa [prefixWord, tailWord_7260111, baseEnd_7260111] using wordTrace_append hprefix tailTrace_7260111
  have hstable : (prefixWord ++ tailWord_7260111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260111).length < 2 ^ (prefixWord ++ tailWord_7260111).sum := by decide
  have hdescent : baseEnd_7260111 < baseStart_7260111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260201 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 4]
def baseStart_7260201 : Nat := 118140960795 + 7260201 * 2 ^ 59
def prefixEnd_7260201 : Nat := 4983230072969 + 3 ^ 40 * 7260201 * 2
def baseEnd_7260201 : Nat := 3727972761253254163898449

theorem tailTrace_7260201 : CollatzResearch.WordTrace tailWord_7260201 prefixEnd_7260201 3727972761253254163898449 := by
  unfold tailWord_7260201
  simp only [CollatzResearch.WordTrace]
  refine ⟨264801284770539195458956457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176534189847026130305970971 264801284770539195458956457)
  ·
    refine ⟨198600963577904396594217343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264801284770539195458956457 198600963577904396594217343)
    ·
      refine ⟨297901445366856594891326015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198600963577904396594217343 297901445366856594891326015)
      ·
        refine ⟨446852168050284892336989023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297901445366856594891326015 446852168050284892336989023)
        ·
          refine ⟨670278252075427338505483535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446852168050284892336989023 670278252075427338505483535)
          ·
            refine ⟨1005417378113141007758225303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670278252075427338505483535 1005417378113141007758225303)
            ·
              refine ⟨1508126067169711511637337955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005417378113141007758225303 1508126067169711511637337955)
              ·
                refine ⟨2262189100754567267456006933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1508126067169711511637337955 2262189100754567267456006933)
                ·
                  refine ⟨106040114097870340662000325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2262189100754567267456006933 106040114097870340662000325)
                  ·
                    refine ⟨19882521393350688874125061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106040114097870340662000325 19882521393350688874125061)
                    ·
                      refine ⟨3727972761253254163898449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19882521393350688874125061 3727972761253254163898449)
                      ·
                        rfl

theorem cell23_7260201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 4, 4].length) (baseStart_7260201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260201 prefixEnd_7260201 := by exact prefixLift 7260201
  have htrace : WordTrace (prefixWord ++ tailWord_7260201) baseStart_7260201 baseEnd_7260201 := by
    simpa [prefixWord, tailWord_7260201, baseEnd_7260201] using wordTrace_append hprefix tailTrace_7260201
  have hstable : (prefixWord ++ tailWord_7260201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260201).length < 2 ^ (prefixWord ++ tailWord_7260201).sum := by decide
  have hdescent : baseEnd_7260201 < baseStart_7260201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260211 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 8]
def baseStart_7260211 : Nat := 118140960795 + 7260211 * 2 ^ 59
def prefixEnd_7260211 : Nat := 4983230072969 + 3 ^ 40 * 7260211 * 2
def baseEnd_7260211 : Nat := 414219766228866569419267

theorem tailTrace_7260211 : CollatzResearch.WordTrace tailWord_7260211 prefixEnd_7260211 414219766228866569419267 := by
  unfold tailWord_7260211
  simp only [CollatzResearch.WordTrace]
  refine ⟨264801649500502967166820487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176534433000335311444546991 264801649500502967166820487)
  ·
    refine ⟨397202474250754450750230731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264801649500502967166820487 397202474250754450750230731)
    ·
      refine ⟨595803711376131676125346097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397202474250754450750230731 595803711376131676125346097)
      ·
        refine ⟨446852783532098757094009573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595803711376131676125346097 446852783532098757094009573)
        ·
          refine ⟨83784896912268516955126795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446852783532098757094009573 83784896912268516955126795)
          ·
            refine ⟨125677345368402775432690193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83784896912268516955126795 125677345368402775432690193)
            ·
              refine ⟨94258009026302081574517645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125677345368402775432690193 94258009026302081574517645)
              ·
                refine ⟨35346753384863280590444117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94258009026302081574517645 35346753384863280590444117)
                ·
                  refine ⟨414219766228866569419267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35346753384863280590444117 414219766228866569419267)
                  ·
                    rfl

theorem cell23_7260211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 8].length) (baseStart_7260211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260211 prefixEnd_7260211 := by exact prefixLift 7260211
  have htrace : WordTrace (prefixWord ++ tailWord_7260211) baseStart_7260211 baseEnd_7260211 := by
    simpa [prefixWord, tailWord_7260211, baseEnd_7260211] using wordTrace_append hprefix tailTrace_7260211
  have hstable : (prefixWord ++ tailWord_7260211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260211).length < 2 ^ (prefixWord ++ tailWord_7260211).sum := by decide
  have hdescent : baseEnd_7260211 < baseStart_7260211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260265 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 4, 3, 2]
def baseStart_7260265 : Nat := 118140960795 + 7260265 * 2 ^ 59
def prefixEnd_7260265 : Nat := 4983230072969 + 3 ^ 40 * 7260265 * 2
def baseEnd_7260265 : Nat := 3728005624015141913498155

theorem tailTrace_7260265 : CollatzResearch.WordTrace tailWord_7260265 prefixEnd_7260265 3728005624015141913498155 := by
  unfold tailWord_7260265
  simp only [CollatzResearch.WordTrace]
  refine ⟨264803619042307334389286249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176535746028204889592857499 264803619042307334389286249)
  ·
    refine ⟨198602714281730500791964687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264803619042307334389286249 198602714281730500791964687)
    ·
      refine ⟨297904071422595751187947031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198602714281730500791964687 297904071422595751187947031)
      ·
        refine ⟨446856107133893626781920547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297904071422595751187947031 446856107133893626781920547)
        ·
          refine ⟨670284160700840440172880821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446856107133893626781920547 670284160700840440172880821)
          ·
            refine ⟨62839140065703791266207577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 670284160700840440172880821 62839140065703791266207577)
            ·
              refine ⟨47129355049277843449655683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62839140065703791266207577 47129355049277843449655683)
              ·
                refine ⟨70694032573916765174483525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47129355049277843449655683 70694032573916765174483525)
                ·
                  refine ⟨13255131107609393470215661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70694032573916765174483525 13255131107609393470215661)
                  ·
                    refine ⟨4970674165353522551330873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13255131107609393470215661 4970674165353522551330873)
                    ·
                      refine ⟨3728005624015141913498155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970674165353522551330873 3728005624015141913498155)
                      ·
                        rfl

theorem cell23_7260265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3, 2].length) (baseStart_7260265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260265 prefixEnd_7260265 := by exact prefixLift 7260265
  have htrace : WordTrace (prefixWord ++ tailWord_7260265) baseStart_7260265 baseEnd_7260265 := by
    simpa [prefixWord, tailWord_7260265, baseEnd_7260265] using wordTrace_append hprefix tailTrace_7260265
  have hstable : (prefixWord ++ tailWord_7260265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260265).length < 2 ^ (prefixWord ++ tailWord_7260265).sum := by decide
  have hdescent : baseEnd_7260265 < baseStart_7260265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260272 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3]
def baseStart_7260272 : Nat := 118140960795 + 7260272 * 2 ^ 59
def prefixEnd_7260272 : Nat := 4983230072969 + 3 ^ 40 * 7260272 * 2
def baseEnd_7260272 : Nat := 3728009218379723386110623

theorem tailTrace_7260272 : CollatzResearch.WordTrace tailWord_7260272 prefixEnd_7260272 3728009218379723386110623 := by
  unfold tailWord_7260272
  simp only [CollatzResearch.WordTrace]
  refine ⟨132401937176640987292395535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176535916235521316389860713 132401937176640987292395535)
  ·
    refine ⟨198602905764961480938593303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132401937176640987292395535 198602905764961480938593303)
    ·
      refine ⟨297904358647442221407889955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198602905764961480938593303 297904358647442221407889955)
      ·
        refine ⟨446856537971163332111834933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297904358647442221407889955 446856537971163332111834933)
        ·
          refine ⟨41892800434796562385484525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 446856537971163332111834933 41892800434796562385484525)
          ·
            refine ⟨15709800163048710894556697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41892800434796562385484525 15709800163048710894556697)
            ·
              refine ⟨11782350122286533170917523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15709800163048710894556697 11782350122286533170917523)
              ·
                refine ⟨17673525183429799756376285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11782350122286533170917523 17673525183429799756376285)
                ·
                  refine ⟨6627571943786174908641107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17673525183429799756376285 6627571943786174908641107)
                  ·
                    refine ⟨9941357915679262362961661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627571943786174908641107 9941357915679262362961661)
                    ·
                      refine ⟨3728009218379723386110623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941357915679262362961661 3728009218379723386110623)
                      ·
                        rfl

theorem cell23_7260272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 1, 3].length) (baseStart_7260272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260272 prefixEnd_7260272 := by exact prefixLift 7260272
  have htrace : WordTrace (prefixWord ++ tailWord_7260272) baseStart_7260272 baseEnd_7260272 := by
    simpa [prefixWord, tailWord_7260272, baseEnd_7260272] using wordTrace_append hprefix tailTrace_7260272
  have hstable : (prefixWord ++ tailWord_7260272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260272).length < 2 ^ (prefixWord ++ tailWord_7260272).sum := by decide
  have hdescent : baseEnd_7260272 < baseStart_7260272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260295 : List Nat := [1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_7260295 : Nat := 118140960795 + 7260295 * 2 ^ 59
def prefixEnd_7260295 : Nat := 4983230072969 + 3 ^ 40 * 7260295 * 2
def baseEnd_7260295 : Nat := 3728021028434776796123017

theorem tailTrace_7260295 : CollatzResearch.WordTrace tailWord_7260295 prefixEnd_7260295 3728021028434776796123017 := by
  unfold tailWord_7260295
  simp only [CollatzResearch.WordTrace]
  refine ⟨264804713232198649512878339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176536475488132433008585559 264804713232198649512878339)
  ·
    refine ⟨397207069848297974269317509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264804713232198649512878339 397207069848297974269317509)
    ·
      refine ⟨74476325596555870175497033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397207069848297974269317509 74476325596555870175497033)
      ·
        refine ⟨55857244197416902631622775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74476325596555870175497033 55857244197416902631622775)
        ·
          refine ⟨83785866296125353947434163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55857244197416902631622775 83785866296125353947434163)
          ·
            refine ⟨125678799444188030921151245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83785866296125353947434163 125678799444188030921151245)
            ·
              refine ⟨47129549791570511595431717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125678799444188030921151245 47129549791570511595431717)
              ·
                refine ⟨8836790585919470924143447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47129549791570511595431717 8836790585919470924143447)
                ·
                  refine ⟨13255185878879206386215171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8836790585919470924143447 13255185878879206386215171)
                  ·
                    refine ⟨19882778818318809579322757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13255185878879206386215171 19882778818318809579322757)
                    ·
                      refine ⟨3728021028434776796123017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19882778818318809579322757 3728021028434776796123017)
                      ·
                        rfl

theorem cell23_7260295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_7260295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260295 prefixEnd_7260295 := by exact prefixLift 7260295
  have htrace : WordTrace (prefixWord ++ tailWord_7260295) baseStart_7260295 baseEnd_7260295 := by
    simpa [prefixWord, tailWord_7260295, baseEnd_7260295] using wordTrace_append hprefix tailTrace_7260295
  have hstable : (prefixWord ++ tailWord_7260295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260295).length < 2 ^ (prefixWord ++ tailWord_7260295).sum := by decide
  have hdescent : baseEnd_7260295 < baseStart_7260295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260315 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 3]
def baseStart_7260315 : Nat := 118140960795 + 7260315 * 2 ^ 59
def prefixEnd_7260315 : Nat := 4983230072969 + 3 ^ 40 * 7260315 * 2
def baseEnd_7260315 : Nat := 3728031298047866717872925

theorem tailTrace_7260315 : CollatzResearch.WordTrace tailWord_7260315 prefixEnd_7260315 3728031298047866717872925 := by
  unfold tailWord_7260315
  simp only [CollatzResearch.WordTrace]
  refine ⟨264805442692126192928606399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176536961794750795285737599 264805442692126192928606399)
  ·
    refine ⟨397208164038189289392909599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264805442692126192928606399 397208164038189289392909599)
    ·
      refine ⟨595812246057283934089364399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397208164038189289392909599 595812246057283934089364399)
      ·
        refine ⟨893718369085925901134046599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595812246057283934089364399 893718369085925901134046599)
        ·
          refine ⟨1340577553628888851701069899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893718369085925901134046599 1340577553628888851701069899)
          ·
            refine ⟨2010866330443333277551604849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340577553628888851701069899 2010866330443333277551604849)
            ·
              refine ⟨1508149747832499958163703637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2010866330443333277551604849 1508149747832499958163703637)
              ·
                refine ⟨8836814928706054442365451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1508149747832499958163703637 8836814928706054442365451)
                ·
                  refine ⟨13255222393059081663548177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8836814928706054442365451 13255222393059081663548177)
                  ·
                    refine ⟨9941416794794311247661133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13255222393059081663548177 9941416794794311247661133)
                    ·
                      refine ⟨3728031298047866717872925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941416794794311247661133 3728031298047866717872925)
                      ·
                        rfl

theorem cell23_7260315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 2, 3].length) (baseStart_7260315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260315 prefixEnd_7260315 := by exact prefixLift 7260315
  have htrace : WordTrace (prefixWord ++ tailWord_7260315) baseStart_7260315 baseEnd_7260315 := by
    simpa [prefixWord, tailWord_7260315, baseEnd_7260315] using wordTrace_append hprefix tailTrace_7260315
  have hstable : (prefixWord ++ tailWord_7260315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260315).length < 2 ^ (prefixWord ++ tailWord_7260315).sum := by decide
  have hdescent : baseEnd_7260315 < baseStart_7260315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260322 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7260322 : Nat := 118140960795 + 7260322 * 2 ^ 59
def prefixEnd_7260322 : Nat := 4983230072969 + 3 ^ 40 * 7260322 * 2
def baseEnd_7260322 : Nat := 1242678297470816063495131

theorem tailTrace_7260322 : CollatzResearch.WordTrace tailWord_7260322 prefixEnd_7260322 1242678297470816063495131 := by
  unfold tailWord_7260322
  simp only [CollatzResearch.WordTrace]
  refine ⟨66201424500775208281027805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176537132002067222082740813 66201424500775208281027805)
  ·
    refine ⟨24825534187790703105385427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66201424500775208281027805 24825534187790703105385427)
    ·
      refine ⟨37238301281686054658078141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24825534187790703105385427 37238301281686054658078141)
      ·
        refine ⟨13964362980632270496779303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37238301281686054658078141 13964362980632270496779303)
        ·
          refine ⟨20946544470948405745168955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13964362980632270496779303 20946544470948405745168955)
          ·
            refine ⟨31419816706422608617753433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20946544470948405745168955 31419816706422608617753433)
            ·
              refine ⟨23564862529816956463315075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31419816706422608617753433 23564862529816956463315075)
              ·
                refine ⟨35347293794725434694972613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23564862529816956463315075 35347293794725434694972613)
                ·
                  refine ⟨6627617586511019005307365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35347293794725434694972613 6627617586511019005307365)
                  ·
                    refine ⟨1242678297470816063495131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6627617586511019005307365 1242678297470816063495131)
                    ·
                      rfl

theorem cell23_7260322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7260322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260322 prefixEnd_7260322 := by exact prefixLift 7260322
  have htrace : WordTrace (prefixWord ++ tailWord_7260322) baseStart_7260322 baseEnd_7260322 := by
    simpa [prefixWord, tailWord_7260322, baseEnd_7260322] using wordTrace_append hprefix tailTrace_7260322
  have hstable : (prefixWord ++ tailWord_7260322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260322).length < 2 ^ (prefixWord ++ tailWord_7260322).sum := by decide
  have hdescent : baseEnd_7260322 < baseStart_7260322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260338 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_7260338 : Nat := 118140960795 + 7260338 * 2 ^ 59
def prefixEnd_7260338 : Nat := 4983230072969 + 3 ^ 40 * 7260338 * 2
def baseEnd_7260338 : Nat := 3728043108102920127885319

theorem tailTrace_7260338 : CollatzResearch.WordTrace tailWord_7260338 prefixEnd_7260338 3728043108102920127885319 := by
  unfold tailWord_7260338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66201570392760716964173417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176537521047361911904462445 66201570392760716964173417)
  ·
    refine ⟨49651177794570537723130063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66201570392760716964173417 49651177794570537723130063)
    ·
      refine ⟨74476766691855806584695095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49651177794570537723130063 74476766691855806584695095)
      ·
        refine ⟨111715150037783709877042643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74476766691855806584695095 111715150037783709877042643)
        ·
          refine ⟨167572725056675564815563965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111715150037783709877042643 167572725056675564815563965)
          ·
            refine ⟨62839771896253336805836487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167572725056675564815563965 62839771896253336805836487)
            ·
              refine ⟨94259657844380005208754731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62839771896253336805836487 94259657844380005208754731)
              ·
                refine ⟨141389486766570007813132097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94259657844380005208754731 141389486766570007813132097)
                ·
                  refine ⟨106042115074927505859849073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141389486766570007813132097 106042115074927505859849073)
                  ·
                    refine ⟨79531586306195629394886805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106042115074927505859849073 79531586306195629394886805)
                    ·
                      refine ⟨3728043108102920127885319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79531586306195629394886805 3728043108102920127885319)
                      ·
                        rfl

theorem cell23_7260338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_7260338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260338 prefixEnd_7260338 := by exact prefixLift 7260338
  have htrace : WordTrace (prefixWord ++ tailWord_7260338) baseStart_7260338 baseEnd_7260338 := by
    simpa [prefixWord, tailWord_7260338, baseEnd_7260338] using wordTrace_append hprefix tailTrace_7260338
  have hstable : (prefixWord ++ tailWord_7260338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260338).length < 2 ^ (prefixWord ++ tailWord_7260338).sum := by decide
  have hdescent : baseEnd_7260338 < baseStart_7260338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260345 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7260345 : Nat := 118140960795 + 7260345 * 2 ^ 59
def prefixEnd_7260345 : Nat := 4983230072969 + 3 ^ 40 * 7260345 * 2
def baseEnd_7260345 : Nat := 3728046702467501600497787

theorem tailTrace_7260345 : CollatzResearch.WordTrace tailWord_7260345 prefixEnd_7260345 3728046702467501600497787 := by
  unfold tailWord_7260345
  simp only [CollatzResearch.WordTrace]
  refine ⟨264806536882017508052198489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176537691254678338701465659 264806536882017508052198489)
  ·
    refine ⟨198604902661513131039148867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264806536882017508052198489 198604902661513131039148867)
    ·
      refine ⟨297907353992269696558723301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198604902661513131039148867 297907353992269696558723301)
      ·
        refine ⟨55857628873550568104760619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297907353992269696558723301 55857628873550568104760619)
        ·
          refine ⟨83786443310325852157140929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55857628873550568104760619 83786443310325852157140929)
          ·
            refine ⟨62839832482744389117855697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83786443310325852157140929 62839832482744389117855697)
            ·
              refine ⟨47129874362058291838391773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62839832482744389117855697 47129874362058291838391773)
              ·
                refine ⟨17673702885771859439396915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47129874362058291838391773 17673702885771859439396915)
                ·
                  refine ⟨26510554328657789159095373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17673702885771859439396915 26510554328657789159095373)
                  ·
                    refine ⟨9941457873246670934660765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26510554328657789159095373 9941457873246670934660765)
                    ·
                      refine ⟨3728046702467501600497787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941457873246670934660765 3728046702467501600497787)
                      ·
                        rfl

theorem cell23_7260345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7260345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260345 prefixEnd_7260345 := by exact prefixLift 7260345
  have htrace : WordTrace (prefixWord ++ tailWord_7260345) baseStart_7260345 baseEnd_7260345 := by
    simpa [prefixWord, tailWord_7260345, baseEnd_7260345] using wordTrace_append hprefix tailTrace_7260345
  have hstable : (prefixWord ++ tailWord_7260345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260345).length < 2 ^ (prefixWord ++ tailWord_7260345).sum := by decide
  have hdescent : baseEnd_7260345 < baseStart_7260345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260368 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4]
def baseStart_7260368 : Nat := 118140960795 + 7260368 * 2 ^ 59
def prefixEnd_7260368 : Nat := 4983230072969 + 3 ^ 40 * 7260368 * 2
def baseEnd_7260368 : Nat := 3728058512522555010510181

theorem tailTrace_7260368 : CollatzResearch.WordTrace tailWord_7260368 prefixEnd_7260368 3728058512522555010510181 := by
  unfold tailWord_7260368
  simp only [CollatzResearch.WordTrace]
  refine ⟨132403687880467091490142879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176538250507289455320190505 132403687880467091490142879)
  ·
    refine ⟨198605531820700637235214319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132403687880467091490142879 198605531820700637235214319)
    ·
      refine ⟨297908297731050955852821479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198605531820700637235214319 297908297731050955852821479)
      ·
        refine ⟨446862446596576433779232219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297908297731050955852821479 446862446596576433779232219)
        ·
          refine ⟨670293669894864650668848329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446862446596576433779232219 670293669894864650668848329)
          ·
            refine ⟨502720252421148488001636247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670293669894864650668848329 502720252421148488001636247)
            ·
              refine ⟨754080378631722732002454371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502720252421148488001636247 754080378631722732002454371)
              ·
                refine ⟨1131120567947584098003681557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754080378631722732002454371 1131120567947584098003681557)
                ·
                  refine ⟨53021276622543004593922573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1131120567947584098003681557 53021276622543004593922573)
                  ·
                    refine ⟨19882978733453626722720965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53021276622543004593922573 19882978733453626722720965)
                    ·
                      refine ⟨3728058512522555010510181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19882978733453626722720965 3728058512522555010510181)
                      ·
                        rfl

theorem cell23_7260368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 4].length) (baseStart_7260368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260368 prefixEnd_7260368 := by exact prefixLift 7260368
  have htrace : WordTrace (prefixWord ++ tailWord_7260368) baseStart_7260368 baseEnd_7260368 := by
    simpa [prefixWord, tailWord_7260368, baseEnd_7260368] using wordTrace_append hprefix tailTrace_7260368
  have hstable : (prefixWord ++ tailWord_7260368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260368).length < 2 ^ (prefixWord ++ tailWord_7260368).sum := by decide
  have hdescent : baseEnd_7260368 < baseStart_7260368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260380 : List Nat := [2, 2, 5, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7260380 : Nat := 118140960795 + 7260380 * 2 ^ 59
def prefixEnd_7260380 : Nat := 4983230072969 + 3 ^ 40 * 7260380 * 2
def baseEnd_7260380 : Nat := 3728064674290408963560127

theorem tailTrace_7260380 : CollatzResearch.WordTrace tailWord_7260380 prefixEnd_7260380 3728064674290408963560127 := by
  unfold tailWord_7260380
  simp only [CollatzResearch.WordTrace]
  refine ⟨132403906718445354514861297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176538542291260472686481729 132403906718445354514861297)
  ·
    refine ⟨99302930038834015886145973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132403906718445354514861297 99302930038834015886145973)
    ·
      refine ⟨9309649691140688989326185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99302930038834015886145973 9309649691140688989326185)
      ·
        refine ⟨6982237268355516741994639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9309649691140688989326185 6982237268355516741994639)
        ·
          refine ⟨10473355902533275112991959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982237268355516741994639 10473355902533275112991959)
          ·
            refine ⟨15710033853799912669487939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473355902533275112991959 15710033853799912669487939)
            ·
              refine ⟨23565050780699869004231909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710033853799912669487939 23565050780699869004231909)
              ·
                refine ⟨4418447021381225438293483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23565050780699869004231909 4418447021381225438293483)
                ·
                  refine ⟨6627670532071838157440225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418447021381225438293483 6627670532071838157440225)
                  ·
                    refine ⟨4970752899053878618080169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6627670532071838157440225 4970752899053878618080169)
                    ·
                      refine ⟨3728064674290408963560127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970752899053878618080169 3728064674290408963560127)
                      ·
                        rfl

theorem cell23_7260380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7260380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260380 prefixEnd_7260380 := by exact prefixLift 7260380
  have htrace : WordTrace (prefixWord ++ tailWord_7260380) baseStart_7260380 baseEnd_7260380 := by
    simpa [prefixWord, tailWord_7260380, baseEnd_7260380] using wordTrace_append hprefix tailTrace_7260380
  have hstable : (prefixWord ++ tailWord_7260380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260380).length < 2 ^ (prefixWord ++ tailWord_7260380).sum := by decide
  have hdescent : baseEnd_7260380 < baseStart_7260380 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260386 : List Nat := [3, 3, 4, 1, 1, 2, 1, 8]
def baseStart_7260386 : Nat := 118140960795 + 7260386 * 2 ^ 59
def prefixEnd_7260386 : Nat := 4983230072969 + 3 ^ 40 * 7260386 * 2
def baseEnd_7260386 : Nat := 138076583524975405188337

theorem tailTrace_7260386 : CollatzResearch.WordTrace tailWord_7260386 prefixEnd_7260386 138076583524975405188337 := by
  unfold tailWord_7260386
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202008068717243013610253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176538688183245981369627341 66202008068717243013610253)
  ·
    refine ⟨24825753025768966130103845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66202008068717243013610253 24825753025768966130103845)
    ·
      refine ⟨4654828692331681149394471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24825753025768966130103845 4654828692331681149394471)
      ·
        refine ⟨6982243038497521724091707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4654828692331681149394471 6982243038497521724091707)
        ·
          refine ⟨10473364557746282586137561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982243038497521724091707 10473364557746282586137561)
          ·
            refine ⟨7855023418309711939603171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10473364557746282586137561 7855023418309711939603171)
            ·
              refine ⟨11782535127464567909404757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7855023418309711939603171 11782535127464567909404757)
              ·
                refine ⟨138076583524975405188337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11782535127464567909404757 138076583524975405188337)
                ·
                  rfl

theorem cell23_7260386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 8].length) (baseStart_7260386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260386 prefixEnd_7260386 := by exact prefixLift 7260386
  have htrace : WordTrace (prefixWord ++ tailWord_7260386) baseStart_7260386 baseEnd_7260386 := by
    simpa [prefixWord, tailWord_7260386, baseEnd_7260386] using wordTrace_append hprefix tailTrace_7260386
  have hstable : (prefixWord ++ tailWord_7260386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260386).length < 2 ^ (prefixWord ++ tailWord_7260386).sum := by decide
  have hdescent : baseEnd_7260386 < baseStart_7260386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260442 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_7260442 : Nat := 118140960795 + 7260442 * 2 ^ 59
def prefixEnd_7260442 : Nat := 4983230072969 + 3 ^ 40 * 7260442 * 2
def baseEnd_7260442 : Nat := 414232945565665302331649

theorem tailTrace_7260442 : CollatzResearch.WordTrace tailWord_7260442 prefixEnd_7260442 414232945565665302331649 := by
  unfold tailWord_7260442
  simp only [CollatzResearch.WordTrace]
  refine ⟨66202518690666523404619895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176540049841777395745653053 66202518690666523404619895)
  ·
    refine ⟨99303778035999785106929843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66202518690666523404619895 99303778035999785106929843)
    ·
      refine ⟨148955667053999677660394765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99303778035999785106929843 148955667053999677660394765)
      ·
        refine ⟨55858375145249879122648037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148955667053999677660394765 55858375145249879122648037)
        ·
          refine ⟨10473445339734352335496507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55858375145249879122648037 10473445339734352335496507)
          ·
            refine ⟨15710168009601528503244761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473445339734352335496507 15710168009601528503244761)
            ·
              refine ⟨11782626007201146377433571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710168009601528503244761 11782626007201146377433571)
              ·
                refine ⟨17673939010801719566150357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11782626007201146377433571 17673939010801719566150357)
                ·
                  refine ⟨414232945565665302331649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17673939010801719566150357 414232945565665302331649)
                  ·
                    rfl

theorem cell23_7260442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_7260442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260442 prefixEnd_7260442 := by exact prefixLift 7260442
  have htrace : WordTrace (prefixWord ++ tailWord_7260442) baseStart_7260442 baseEnd_7260442 := by
    simpa [prefixWord, tailWord_7260442, baseEnd_7260442] using wordTrace_append hprefix tailTrace_7260442
  have hstable : (prefixWord ++ tailWord_7260442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260442).length < 2 ^ (prefixWord ++ tailWord_7260442).sum := by decide
  have hdescent : baseEnd_7260442 < baseStart_7260442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260452 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_7260452 : Nat := 118140960795 + 7260452 * 2 ^ 59
def prefixEnd_7260452 : Nat := 4983230072969 + 3 ^ 40 * 7260452 * 2
def baseEnd_7260452 : Nat := 3728101644897532681859795

theorem tailTrace_7260452 : CollatzResearch.WordTrace tailWord_7260452 prefixEnd_7260452 3728101644897532681859795 := by
  unfold tailWord_7260452
  simp only [CollatzResearch.WordTrace]
  refine ⟨132405219746314932663171805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176540292995086576884229073 132405219746314932663171805)
  ·
    refine ⟨49651957404868099748689427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132405219746314932663171805 49651957404868099748689427)
    ·
      refine ⟨74477936107302149623034141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49651957404868099748689427 74477936107302149623034141)
      ·
        refine ⟨27929226040238306108637803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74477936107302149623034141 27929226040238306108637803)
        ·
          refine ⟨41893839060357459162956705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27929226040238306108637803 41893839060357459162956705)
          ·
            refine ⟨31420379295268094372217529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41893839060357459162956705 31420379295268094372217529)
            ·
              refine ⟨23565284471451070779163147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31420379295268094372217529 23565284471451070779163147)
              ·
                refine ⟨35347926707176606168744721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23565284471451070779163147 35347926707176606168744721)
                ·
                  refine ⟨26510945030382454626558541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35347926707176606168744721 26510945030382454626558541)
                  ·
                    refine ⟨9941604386393420484959453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26510945030382454626558541 9941604386393420484959453)
                    ·
                      refine ⟨3728101644897532681859795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941604386393420484959453 3728101644897532681859795)
                      ·
                        rfl

theorem cell23_7260452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_7260452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260452 prefixEnd_7260452 := by exact prefixLift 7260452
  have htrace : WordTrace (prefixWord ++ tailWord_7260452) baseStart_7260452 baseEnd_7260452 := by
    simpa [prefixWord, tailWord_7260452, baseEnd_7260452] using wordTrace_append hprefix tailTrace_7260452
  have hstable : (prefixWord ++ tailWord_7260452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260452).length < 2 ^ (prefixWord ++ tailWord_7260452).sum := by decide
  have hdescent : baseEnd_7260452 < baseStart_7260452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260453 : List Nat := [1, 3, 1, 2, 5, 1, 3, 1, 2, 2, 2]
def baseStart_7260453 : Nat := 118140960795 + 7260453 * 2 ^ 59
def prefixEnd_7260453 : Nat := 4983230072969 + 3 ^ 40 * 7260453 * 2
def baseEnd_7260453 : Nat := 3728102158378187177947291

theorem tailTrace_7260453 : CollatzResearch.WordTrace tailWord_7260453 prefixEnd_7260453 3728102158378187177947291 := by
  unfold tailWord_7260453
  simp only [CollatzResearch.WordTrace]
  refine ⟨264810475965626242497130013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176540317310417494998086675 264810475965626242497130013)
  ·
    refine ⟨99303928487109840936423755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264810475965626242497130013 99303928487109840936423755)
    ·
      refine ⟨148955892730664761404635633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99303928487109840936423755 148955892730664761404635633)
      ·
        refine ⟨111716919547998571053476725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148955892730664761404635633 111716919547998571053476725)
        ·
          refine ⟨10473461207624866036263443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111716919547998571053476725 10473461207624866036263443)
          ·
            refine ⟨15710191811437299054395165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10473461207624866036263443 15710191811437299054395165)
            ·
              refine ⟨5891321929288987145398187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15710191811437299054395165 5891321929288987145398187)
              ·
                refine ⟨8836982893933480718097281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891321929288987145398187 8836982893933480718097281)
                ·
                  refine ⟨6627737170450110538572961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8836982893933480718097281 6627737170450110538572961)
                  ·
                    refine ⟨4970802877837582903929721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6627737170450110538572961 4970802877837582903929721)
                    ·
                      refine ⟨3728102158378187177947291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970802877837582903929721 3728102158378187177947291)
                      ·
                        rfl

theorem cell23_7260453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 1, 2, 2, 2].length) (baseStart_7260453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260453 prefixEnd_7260453 := by exact prefixLift 7260453
  have htrace : WordTrace (prefixWord ++ tailWord_7260453) baseStart_7260453 baseEnd_7260453 := by
    simpa [prefixWord, tailWord_7260453, baseEnd_7260453] using wordTrace_append hprefix tailTrace_7260453
  have hstable : (prefixWord ++ tailWord_7260453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260453).length < 2 ^ (prefixWord ++ tailWord_7260453).sum := by decide
  have hdescent : baseEnd_7260453 < baseStart_7260453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260492 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_7260492 : Nat := 118140960795 + 7260492 * 2 ^ 59
def prefixEnd_7260492 : Nat := 4983230072969 + 3 ^ 40 * 7260492 * 2
def baseEnd_7260492 : Nat := 3728122184123712525359611

theorem tailTrace_7260492 : CollatzResearch.WordTrace tailWord_7260492 prefixEnd_7260492 3728122184123712525359611 := by
  unfold tailWord_7260492
  simp only [CollatzResearch.WordTrace]
  refine ⟨132405949206242476078899865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176541265608323301438533153 132405949206242476078899865)
  ·
    refine ⟨99304461904681857059174899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132405949206242476078899865 99304461904681857059174899)
    ·
      refine ⟨148956692857022785588762349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99304461904681857059174899 148956692857022785588762349)
      ·
        refine ⟨55858759821383544595785881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148956692857022785588762349 55858759821383544595785881)
        ·
          refine ⟨41894069866037658446839411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55858759821383544595785881 41894069866037658446839411)
          ·
            refine ⟨62841104799056487670259117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41894069866037658446839411 62841104799056487670259117)
            ·
              refine ⟨23565414299646182876347169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62841104799056487670259117 23565414299646182876347169)
              ·
                refine ⟨17674060724734637157260377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23565414299646182876347169 17674060724734637157260377)
                ·
                  refine ⟨13255545543550977867945283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17674060724734637157260377 13255545543550977867945283)
                  ·
                    refine ⟨19883318315326466801917925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13255545543550977867945283 19883318315326466801917925)
                    ·
                      refine ⟨3728122184123712525359611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19883318315326466801917925 3728122184123712525359611)
                      ·
                        rfl

theorem cell23_7260492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_7260492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260492 prefixEnd_7260492 := by exact prefixLift 7260492
  have htrace : WordTrace (prefixWord ++ tailWord_7260492) baseStart_7260492 baseEnd_7260492 := by
    simpa [prefixWord, tailWord_7260492, baseEnd_7260492] using wordTrace_append hprefix tailTrace_7260492
  have hstable : (prefixWord ++ tailWord_7260492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260492).length < 2 ^ (prefixWord ++ tailWord_7260492).sum := by decide
  have hdescent : baseEnd_7260492 < baseStart_7260492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260495 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3]
def baseStart_7260495 : Nat := 118140960795 + 7260495 * 2 ^ 59
def prefixEnd_7260495 : Nat := 4983230072969 + 3 ^ 40 * 7260495 * 2
def baseEnd_7260495 : Nat := 3728123724565676013622097

theorem tailTrace_7260495 : CollatzResearch.WordTrace tailWord_7260495 prefixEnd_7260495 3728123724565676013622097 := by
  unfold tailWord_7260495
  simp only [CollatzResearch.WordTrace]
  refine ⟨264812007831474083670158939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176541338554316055780105959 264812007831474083670158939)
  ·
    refine ⟨397218011747211125505238409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264812007831474083670158939 397218011747211125505238409)
    ·
      refine ⟨297913508810408344128928807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397218011747211125505238409 297913508810408344128928807)
      ·
        refine ⟨446870263215612516193393211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297913508810408344128928807 446870263215612516193393211)
        ·
          refine ⟨670305394823418774290089817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446870263215612516193393211 670305394823418774290089817)
          ·
            refine ⟨502729046117564080717567363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670305394823418774290089817 502729046117564080717567363)
            ·
              refine ⟨754093569176346121076351045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502729046117564080717567363 754093569176346121076351045)
              ·
                refine ⟨141392544220564897701815821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754093569176346121076351045 141392544220564897701815821)
                ·
                  refine ⟨53022204082711836638180933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141392544220564897701815821 53022204082711836638180933)
                  ·
                    refine ⟨9941663265508469369658925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53022204082711836638180933 9941663265508469369658925)
                    ·
                      refine ⟨3728123724565676013622097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941663265508469369658925 3728123724565676013622097)
                      ·
                        rfl

theorem cell23_7260495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 4, 3].length) (baseStart_7260495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260495 prefixEnd_7260495 := by exact prefixLift 7260495
  have htrace : WordTrace (prefixWord ++ tailWord_7260495) baseStart_7260495 baseEnd_7260495 := by
    simpa [prefixWord, tailWord_7260495, baseEnd_7260495] using wordTrace_append hprefix tailTrace_7260495
  have hstable : (prefixWord ++ tailWord_7260495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260495).length < 2 ^ (prefixWord ++ tailWord_7260495).sum := by decide
  have hdescent : baseEnd_7260495 < baseStart_7260495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260553 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 1, 4]
def baseStart_7260553 : Nat := 118140960795 + 7260553 * 2 ^ 59
def prefixEnd_7260553 : Nat := 4983230072969 + 3 ^ 40 * 7260553 * 2
def baseEnd_7260553 : Nat := 1242717835481212262232277

theorem tailTrace_7260553 : CollatzResearch.WordTrace tailWord_7260553 prefixEnd_7260553 1242717835481212262232277 := by
  unfold tailWord_7260553
  simp only [CollatzResearch.WordTrace]
  refine ⟨264814123265263959575770313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176542748843509306383846875 264814123265263959575770313)
  ·
    refine ⟨198610592448947969681827735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264814123265263959575770313 198610592448947969681827735)
    ·
      refine ⟨297915888673421954522741603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198610592448947969681827735 297915888673421954522741603)
      ·
        refine ⟨446873833010132931784112405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297915888673421954522741603 446873833010132931784112405)
        ·
          refine ⟨20947210922349981177380269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446873833010132931784112405 20947210922349981177380269)
          ·
            refine ⟨7855204095881242941517601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20947210922349981177380269 7855204095881242941517601)
            ·
              refine ⟨5891403071910932206138201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7855204095881242941517601 5891403071910932206138201)
              ·
                refine ⟨4418552303933199154603651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891403071910932206138201 4418552303933199154603651)
                ·
                  refine ⟨6627828455899798731905477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418552303933199154603651 6627828455899798731905477)
                  ·
                    refine ⟨1242717835481212262232277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6627828455899798731905477 1242717835481212262232277)
                    ·
                      rfl

theorem cell23_7260553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 4].length) (baseStart_7260553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260553 prefixEnd_7260553 := by exact prefixLift 7260553
  have htrace : WordTrace (prefixWord ++ tailWord_7260553) baseStart_7260553 baseEnd_7260553 := by
    simpa [prefixWord, tailWord_7260553, baseEnd_7260553] using wordTrace_append hprefix tailTrace_7260553
  have hstable : (prefixWord ++ tailWord_7260553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260553).length < 2 ^ (prefixWord ++ tailWord_7260553).sum := by decide
  have hdescent : baseEnd_7260553 < baseStart_7260553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260593 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 1, 1, 3]
def baseStart_7260593 : Nat := 118140960795 + 7260593 * 2 ^ 59
def prefixEnd_7260593 : Nat := 4983230072969 + 3 ^ 40 * 7260593 * 2
def baseEnd_7260593 : Nat := 3728174045669816630196647

theorem tailTrace_7260593 : CollatzResearch.WordTrace tailWord_7260593 prefixEnd_7260593 3728174045669816630196647 := by
  unfold tailWord_7260593
  simp only [CollatzResearch.WordTrace]
  refine ⟨264815582185119046407226433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176543721456746030938150955 264815582185119046407226433)
  ·
    refine ⟨198611686638839284805419825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264815582185119046407226433 198611686638839284805419825)
    ·
      refine ⟨148958764979129463604064869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198611686638839284805419825 148958764979129463604064869)
      ·
        refine ⟨27929768433586774425762163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148958764979129463604064869 27929768433586774425762163)
        ·
          refine ⟨41894652650380161638643245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27929768433586774425762163 41894652650380161638643245)
          ·
            refine ⟨15710494743892560614491217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41894652650380161638643245 15710494743892560614491217)
            ·
              refine ⟨11782871057919420460868413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15710494743892560614491217 11782871057919420460868413)
              ·
                refine ⟨4418576646719782672825655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11782871057919420460868413 4418576646719782672825655)
                ·
                  refine ⟨6627864970079674009238483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418576646719782672825655 6627864970079674009238483)
                  ·
                    refine ⟨9941797455119511013857725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627864970079674009238483 9941797455119511013857725)
                    ·
                      refine ⟨3728174045669816630196647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941797455119511013857725 3728174045669816630196647)
                      ·
                        rfl

theorem cell23_7260593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_7260593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260593 prefixEnd_7260593 := by exact prefixLift 7260593
  have htrace : WordTrace (prefixWord ++ tailWord_7260593) baseStart_7260593 baseEnd_7260593 := by
    simpa [prefixWord, tailWord_7260593, baseEnd_7260593] using wordTrace_append hprefix tailTrace_7260593
  have hstable : (prefixWord ++ tailWord_7260593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260593).length < 2 ^ (prefixWord ++ tailWord_7260593).sum := by decide
  have hdescent : baseEnd_7260593 < baseStart_7260593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260595 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_7260595 : Nat := 118140960795 + 7260595 * 2 ^ 59
def prefixEnd_7260595 : Nat := 4983230072969 + 3 ^ 40 * 7260595 * 2
def baseEnd_7260595 : Nat := 3728175072631125622371637

theorem tailTrace_7260595 : CollatzResearch.WordTrace tailWord_7260595 prefixEnd_7260595 3728175072631125622371637 := by
  unfold tailWord_7260595
  simp only [CollatzResearch.WordTrace]
  refine ⟨264815655131111800748799239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176543770087407867165866159 264815655131111800748799239)
  ·
    refine ⟨397223482696667701123198859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264815655131111800748799239 397223482696667701123198859)
    ·
      refine ⟨595835224045001551684798289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397223482696667701123198859 595835224045001551684798289)
      ·
        refine ⟨446876418033751163763598717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595835224045001551684798289 446876418033751163763598717)
        ·
          refine ⟨167578656762656686411349519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446876418033751163763598717 167578656762656686411349519)
          ·
            refine ⟨251367985143985029617024279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167578656762656686411349519 251367985143985029617024279)
            ·
              refine ⟨377051977715977544425536419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251367985143985029617024279 377051977715977544425536419)
              ·
                refine ⟨565577966573966316638304629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377051977715977544425536419 565577966573966316638304629)
                ·
                  refine ⟨53022934366309342184841059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 565577966573966316638304629 53022934366309342184841059)
                  ·
                    refine ⟨79534401549464013277261589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53022934366309342184841059 79534401549464013277261589)
                    ·
                      refine ⟨3728175072631125622371637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79534401549464013277261589 3728175072631125622371637)
                      ·
                        rfl

theorem cell23_7260595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_7260595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260595 prefixEnd_7260595 := by exact prefixLift 7260595
  have htrace : WordTrace (prefixWord ++ tailWord_7260595) baseStart_7260595 baseEnd_7260595 := by
    simpa [prefixWord, tailWord_7260595, baseEnd_7260595] using wordTrace_append hprefix tailTrace_7260595
  have hstable : (prefixWord ++ tailWord_7260595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260595).length < 2 ^ (prefixWord ++ tailWord_7260595).sum := by decide
  have hdescent : baseEnd_7260595 < baseStart_7260595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260599 : List Nat := [1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_7260599 : Nat := 118140960795 + 7260599 * 2 ^ 59
def prefixEnd_7260599 : Nat := 4983230072969 + 3 ^ 40 * 7260599 * 2
def baseEnd_7260599 : Nat := 3728177126553743606721619

theorem tailTrace_7260599 : CollatzResearch.WordTrace tailWord_7260599 prefixEnd_7260599 3728177126553743606721619 := by
  unfold tailWord_7260599
  simp only [CollatzResearch.WordTrace]
  refine ⟨264815801023097309431944851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176543867348731539621296567 264815801023097309431944851)
  ·
    refine ⟨397223701534645964147917277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264815801023097309431944851 397223701534645964147917277)
    ·
      refine ⟨148958888075492236555468979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397223701534645964147917277 148958888075492236555468979)
      ·
        refine ⟨223438332113238354833203469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148958888075492236555468979 223438332113238354833203469)
        ·
          refine ⟨83789374542464383062451301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223438332113238354833203469 83789374542464383062451301)
          ·
            refine ⟨15710507726712071824209619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 83789374542464383062451301 15710507726712071824209619)
            ·
              refine ⟨23565761590068107736314429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710507726712071824209619 23565761590068107736314429)
              ·
                refine ⟨8837160596275540401117911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23565761590068107736314429 8837160596275540401117911)
                ·
                  refine ⟨13255740894413310601676867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8837160596275540401117911 13255740894413310601676867)
                  ·
                    refine ⟨19883611341619965902515301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13255740894413310601676867 19883611341619965902515301)
                    ·
                      refine ⟨3728177126553743606721619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19883611341619965902515301 3728177126553743606721619)
                      ·
                        rfl

theorem cell23_7260599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_7260599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260599 prefixEnd_7260599 := by exact prefixLift 7260599
  have htrace : WordTrace (prefixWord ++ tailWord_7260599) baseStart_7260599 baseEnd_7260599 := by
    simpa [prefixWord, tailWord_7260599, baseEnd_7260599] using wordTrace_append hprefix tailTrace_7260599
  have hstable : (prefixWord ++ tailWord_7260599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260599).length < 2 ^ (prefixWord ++ tailWord_7260599).sum := by decide
  have hdescent : baseEnd_7260599 < baseStart_7260599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260616 : List Nat := [2, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2]
def baseStart_7260616 : Nat := 118140960795 + 7260616 * 2 ^ 59
def prefixEnd_7260616 : Nat := 4983230072969 + 3 ^ 40 * 7260616 * 2
def baseEnd_7260616 : Nat := 3728185855724870040209041

theorem tailTrace_7260616 : CollatzResearch.WordTrace tailWord_7260616 prefixEnd_7260616 3728185855724870040209041 := by
  unfold tailWord_7260616
  simp only [CollatzResearch.WordTrace]
  refine ⟨132408210532017860667656851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176544280709357147556875801 132408210532017860667656851)
  ·
    refine ⟨198612315798026791001485277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132408210532017860667656851 198612315798026791001485277)
    ·
      refine ⟨74479618424260046625556979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198612315798026791001485277 74479618424260046625556979)
      ·
        refine ⟨111719427636390069938335469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74479618424260046625556979 111719427636390069938335469)
        ·
          refine ⟨41894785363646276226875801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111719427636390069938335469 41894785363646276226875801)
          ·
            refine ⟨31421089022734707170156851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41894785363646276226875801 31421089022734707170156851)
            ·
              refine ⟨47131633534102060755235277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31421089022734707170156851 47131633534102060755235277)
              ·
                refine ⟨17674362575288272783213229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47131633534102060755235277 17674362575288272783213229)
                ·
                  refine ⟨6627885965733102293704961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17674362575288272783213229 6627885965733102293704961)
                  ·
                    refine ⟨4970914474299826720278721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6627885965733102293704961 4970914474299826720278721)
                    ·
                      refine ⟨3728185855724870040209041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970914474299826720278721 3728185855724870040209041)
                      ·
                        rfl

theorem cell23_7260616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_7260616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260616 prefixEnd_7260616 := by exact prefixLift 7260616
  have htrace : WordTrace (prefixWord ++ tailWord_7260616) baseStart_7260616 baseEnd_7260616 := by
    simpa [prefixWord, tailWord_7260616, baseEnd_7260616] using wordTrace_append hprefix tailTrace_7260616
  have hstable : (prefixWord ++ tailWord_7260616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260616).length < 2 ^ (prefixWord ++ tailWord_7260616).sum := by decide
  have hdescent : baseEnd_7260616 < baseStart_7260616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260629 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7260629 : Nat := 118140960795 + 7260629 * 2 ^ 59
def prefixEnd_7260629 : Nat := 4983230072969 + 3 ^ 40 * 7260629 * 2
def baseEnd_7260629 : Nat := 3728192530973378489346481

theorem tailTrace_7260629 : CollatzResearch.WordTrace tailWord_7260629 prefixEnd_7260629 3728192530973378489346481 := by
  unfold tailWord_7260629
  simp only [CollatzResearch.WordTrace]
  refine ⟨264816895212988624555536941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176544596808659083037024627 264816895212988624555536941)
  ·
    refine ⟨99306335704870734208326353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264816895212988624555536941 99306335704870734208326353)
    ·
      refine ⟨74479751778653050656244765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99306335704870734208326353 74479751778653050656244765)
      ·
        refine ⟨27929906916994893996091787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74479751778653050656244765 27929906916994893996091787)
        ·
          refine ⟨41894860375492340994137681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27929906916994893996091787 41894860375492340994137681)
          ·
            refine ⟨31421145281619255745603261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41894860375492340994137681 31421145281619255745603261)
            ·
              refine ⟨11782929480607220904601223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31421145281619255745603261 11782929480607220904601223)
              ·
                refine ⟨17674394220910831356901835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11782929480607220904601223 17674394220910831356901835)
                ·
                  refine ⟨26511591331366247035352753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17674394220910831356901835 26511591331366247035352753)
                  ·
                    refine ⟨19883693498524685276514565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26511591331366247035352753 19883693498524685276514565)
                    ·
                      refine ⟨3728192530973378489346481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19883693498524685276514565 3728192530973378489346481)
                      ·
                        rfl

theorem cell23_7260629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7260629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260629 prefixEnd_7260629 := by exact prefixLift 7260629
  have htrace : WordTrace (prefixWord ++ tailWord_7260629) baseStart_7260629 baseEnd_7260629 := by
    simpa [prefixWord, tailWord_7260629, baseEnd_7260629] using wordTrace_append hprefix tailTrace_7260629
  have hstable : (prefixWord ++ tailWord_7260629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260629).length < 2 ^ (prefixWord ++ tailWord_7260629).sum := by decide
  have hdescent : baseEnd_7260629 < baseStart_7260629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260639 : List Nat := [1, 1, 2, 3, 3, 4, 2, 7]
def baseStart_7260639 : Nat := 118140960795 + 7260639 * 2 ^ 59
def prefixEnd_7260639 : Nat := 4983230072969 + 3 ^ 40 * 7260639 * 2
def baseEnd_7260639 : Nat := 138081395028886053711905

theorem tailTrace_7260639 : CollatzResearch.WordTrace tailWord_7260639 prefixEnd_7260639 138081395028886053711905 := by
  unfold tailWord_7260639
  simp only [CollatzResearch.WordTrace]
  refine ⟨264817259942952396263400971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176544839961968264175600647 264817259942952396263400971)
  ·
    refine ⟨397225889914428594395101457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264817259942952396263400971 397225889914428594395101457)
    ·
      refine ⟨297919417435821445796326093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397225889914428594395101457 297919417435821445796326093)
      ·
        refine ⟨111719781538433042173622285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297919417435821445796326093 111719781538433042173622285)
        ·
          refine ⟨41894918076912390815108357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111719781538433042173622285 41894918076912390815108357)
          ·
            refine ⟨7855297139421073277832817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41894918076912390815108357 7855297139421073277832817)
            ·
              refine ⟨5891472854565804958374613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7855297139421073277832817 5891472854565804958374613)
              ·
                refine ⟨138081395028886053711905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5891472854565804958374613 138081395028886053711905)
                ·
                  rfl

theorem cell23_7260639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 2, 7].length) (baseStart_7260639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260639 prefixEnd_7260639 := by exact prefixLift 7260639
  have htrace : WordTrace (prefixWord ++ tailWord_7260639) baseStart_7260639 baseEnd_7260639 := by
    simpa [prefixWord, tailWord_7260639, baseEnd_7260639] using wordTrace_append hprefix tailTrace_7260639
  have hstable : (prefixWord ++ tailWord_7260639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260639).length < 2 ^ (prefixWord ++ tailWord_7260639).sum := by decide
  have hdescent : baseEnd_7260639 < baseStart_7260639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260650 : List Nat := [3, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_7260650 : Nat := 118140960795 + 7260650 * 2 ^ 59
def prefixEnd_7260650 : Nat := 4983230072969 + 3 ^ 40 * 7260650 * 2
def baseEnd_7260650 : Nat := 3728203314067122907183885

theorem tailTrace_7260650 : CollatzResearch.WordTrace tailWord_7260650 prefixEnd_7260650 3728203314067122907183885 := by
  unfold tailWord_7260650
  simp only [CollatzResearch.WordTrace]
  refine ⟨66204415286478136285512851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176545107430608363428034269 66204415286478136285512851)
  ·
    refine ⟨99306622929717204428269277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66204415286478136285512851 99306622929717204428269277)
    ·
      refine ⟨37239983598643951660600979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99306622929717204428269277 37239983598643951660600979)
      ·
        refine ⟨55859975397965927490901469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37239983598643951660600979 55859975397965927490901469)
        ·
          refine ⟨20947490774237222809088051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55859975397965927490901469 20947490774237222809088051)
          ·
            refine ⟨31421236161355834213632077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20947490774237222809088051 31421236161355834213632077)
            ·
              refine ⟨11782963560508437830112029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31421236161355834213632077 11782963560508437830112029)
              ·
                refine ⟨4418611335190664186292011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11782963560508437830112029 4418611335190664186292011)
                ·
                  refine ⟨6627917002785996279438017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418611335190664186292011 6627917002785996279438017)
                  ·
                    refine ⟨4970937752089497209578513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6627917002785996279438017 4970937752089497209578513)
                    ·
                      refine ⟨3728203314067122907183885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970937752089497209578513 3728203314067122907183885)
                      ·
                        rfl

theorem cell23_7260650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_7260650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260650 prefixEnd_7260650 := by exact prefixLift 7260650
  have htrace : WordTrace (prefixWord ++ tailWord_7260650) baseStart_7260650 baseEnd_7260650 := by
    simpa [prefixWord, tailWord_7260650, baseEnd_7260650] using wordTrace_append hprefix tailTrace_7260650
  have hstable : (prefixWord ++ tailWord_7260650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260650).length < 2 ^ (prefixWord ++ tailWord_7260650).sum := by decide
  have hdescent : baseEnd_7260650 < baseStart_7260650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260682 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_7260682 : Nat := 118140960795 + 7260682 * 2 ^ 59
def prefixEnd_7260682 : Nat := 4983230072969 + 3 ^ 40 * 7260682 * 2
def baseEnd_7260682 : Nat := 1242739915149355593994579

theorem tailTrace_7260682 : CollatzResearch.WordTrace tailWord_7260682 prefixEnd_7260682 1242739915149355593994579 := by
  unfold tailWord_7260682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66204707070449153651804075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176545885521197743071477533 66204707070449153651804075)
  ·
    refine ⟨99307060605673730477706113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66204707070449153651804075 99307060605673730477706113)
    ·
      refine ⟨74480295454255297858279585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99307060605673730477706113 74480295454255297858279585)
      ·
        refine ⟨55860221590691473393709689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74480295454255297858279585 55860221590691473393709689)
        ·
          refine ⟨41895166193018605045282267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55860221590691473393709689 41895166193018605045282267)
          ·
            refine ⟨62842749289527907567923401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41895166193018605045282267 62842749289527907567923401)
            ·
              refine ⟨47132061967145930675942551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62842749289527907567923401 47132061967145930675942551)
              ·
                refine ⟨70698092950718896013913827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47132061967145930675942551 70698092950718896013913827)
                ·
                  refine ⟨106047139426078344020870741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70698092950718896013913827 106047139426078344020870741)
                  ·
                    refine ⟨1242739915149355593994579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 106047139426078344020870741 1242739915149355593994579)
                    ·
                      rfl

theorem cell23_7260682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_7260682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260682 prefixEnd_7260682 := by exact prefixLift 7260682
  have htrace : WordTrace (prefixWord ++ tailWord_7260682) baseStart_7260682 baseEnd_7260682 := by
    simpa [prefixWord, tailWord_7260682, baseEnd_7260682] using wordTrace_append hprefix tailTrace_7260682
  have hstable : (prefixWord ++ tailWord_7260682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260682).length < 2 ^ (prefixWord ++ tailWord_7260682).sum := by decide
  have hdescent : baseEnd_7260682 < baseStart_7260682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260683 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 2, 1, 3]
def baseStart_7260683 : Nat := 118140960795 + 7260683 * 2 ^ 59
def prefixEnd_7260683 : Nat := 4983230072969 + 3 ^ 40 * 7260683 * 2
def baseEnd_7260683 : Nat := 3728220258928721278071233

theorem tailTrace_7260683 : CollatzResearch.WordTrace tailWord_7260683 prefixEnd_7260683 3728220258928721278071233 := by
  unfold tailWord_7260683
  simp only [CollatzResearch.WordTrace]
  refine ⟨264818864754792991778002703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176545909836528661185335135 264818864754792991778002703)
  ·
    refine ⟨397228297132189487667004055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264818864754792991778002703 397228297132189487667004055)
    ·
      refine ⟨595842445698284231500506083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397228297132189487667004055 595842445698284231500506083)
      ·
        refine ⟨893763668547426347250759125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595842445698284231500506083 893763668547426347250759125)
        ·
          refine ⟨20947585981580305013689667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 893763668547426347250759125 20947585981580305013689667)
          ·
            refine ⟨31421378972370457520534501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20947585981580305013689667 31421378972370457520534501)
            ·
              refine ⟨5891508557319460785100219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31421378972370457520534501 5891508557319460785100219)
              ·
                refine ⟨8837262835979191177650329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891508557319460785100219 8837262835979191177650329)
                ·
                  refine ⟨6627947126984393383237747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8837262835979191177650329 6627947126984393383237747)
                  ·
                    refine ⟨9941920690476590074856621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6627947126984393383237747 9941920690476590074856621)
                    ·
                      refine ⟨3728220258928721278071233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941920690476590074856621 3728220258928721278071233)
                      ·
                        rfl

theorem cell23_7260683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 1, 3].length) (baseStart_7260683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260683 prefixEnd_7260683 := by exact prefixLift 7260683
  have htrace : WordTrace (prefixWord ++ tailWord_7260683) baseStart_7260683 baseEnd_7260683 := by
    simpa [prefixWord, tailWord_7260683, baseEnd_7260683] using wordTrace_append hprefix tailTrace_7260683
  have hstable : (prefixWord ++ tailWord_7260683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260683).length < 2 ^ (prefixWord ++ tailWord_7260683).sum := by decide
  have hdescent : baseEnd_7260683 < baseStart_7260683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260722 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_7260722 : Nat := 118140960795 + 7260722 * 2 ^ 59
def prefixEnd_7260722 : Nat := 4983230072969 + 3 ^ 40 * 7260722 * 2
def baseEnd_7260722 : Nat := 3728240284674246625483553

theorem tailTrace_7260722 : CollatzResearch.WordTrace tailWord_7260722 prefixEnd_7260722 3728240284674246625483553 := by
  unfold tailWord_7260722
  simp only [CollatzResearch.WordTrace]
  refine ⟨66205071800412925359668105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176546858134434467625781613 66205071800412925359668105)
  ·
    refine ⟨49653803850309694019751079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66205071800412925359668105 49653803850309694019751079)
    ·
      refine ⟨74480705775464541029626619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49653803850309694019751079 74480705775464541029626619)
      ·
        refine ⟨111721058663196811544439929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74480705775464541029626619 111721058663196811544439929)
        ·
          refine ⟨83790793997397608658329947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111721058663196811544439929 83790793997397608658329947)
          ·
            refine ⟨125686190996096412987494921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83790793997397608658329947 125686190996096412987494921)
            ·
              refine ⟨94264643247072309740621191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125686190996096412987494921 94264643247072309740621191)
              ·
                refine ⟨141396964870608464610931787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94264643247072309740621191 141396964870608464610931787)
                ·
                  refine ⟨212095447305912696916397681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141396964870608464610931787 212095447305912696916397681)
                  ·
                    refine ⟨159071585479434522687298261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212095447305912696916397681 159071585479434522687298261)
                    ·
                      refine ⟨3728240284674246625483553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159071585479434522687298261 3728240284674246625483553)
                      ·
                        rfl

theorem cell23_7260722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_7260722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260722 prefixEnd_7260722 := by exact prefixLift 7260722
  have htrace : WordTrace (prefixWord ++ tailWord_7260722) baseStart_7260722 baseEnd_7260722 := by
    simpa [prefixWord, tailWord_7260722, baseEnd_7260722] using wordTrace_append hprefix tailTrace_7260722
  have hstable : (prefixWord ++ tailWord_7260722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260722).length < 2 ^ (prefixWord ++ tailWord_7260722).sum := by decide
  have hdescent : baseEnd_7260722 < baseStart_7260722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260723 : List Nat := [1, 1, 1, 2, 4, 2, 4, 2, 2, 2, 2]
def baseStart_7260723 : Nat := 118140960795 + 7260723 * 2 ^ 59
def prefixEnd_7260723 : Nat := 4983230072969 + 3 ^ 40 * 7260723 * 2
def baseEnd_7260723 : Nat := 3728240798154901121571049

theorem tailTrace_7260723 : CollatzResearch.WordTrace tailWord_7260723 prefixEnd_7260723 3728240798154901121571049 := by
  unfold tailWord_7260723
  simp only [CollatzResearch.WordTrace]
  refine ⟨264820323674648078609458823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176546882449765385739639215 264820323674648078609458823)
  ·
    refine ⟨397230485511972117914188235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264820323674648078609458823 397230485511972117914188235)
    ·
      refine ⟨595845728267958176871282353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397230485511972117914188235 595845728267958176871282353)
      ·
        refine ⟨446884296200968632653461765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595845728267958176871282353 446884296200968632653461765)
        ·
          refine ⟨83790805537681618622524081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 446884296200968632653461765 83790805537681618622524081)
          ·
            refine ⟨62843104153261213966893061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83790805537681618622524081 62843104153261213966893061)
            ·
              refine ⟨11783082028736477618792449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62843104153261213966893061 11783082028736477618792449)
              ·
                refine ⟨8837311521552358214094337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11783082028736477618792449 8837311521552358214094337)
                ·
                  refine ⟨6627983641164268660570753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8837311521552358214094337 6627983641164268660570753)
                  ·
                    refine ⟨4970987730873201495428065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6627983641164268660570753 4970987730873201495428065)
                    ·
                      refine ⟨3728240798154901121571049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4970987730873201495428065 3728240798154901121571049)
                      ·
                        rfl

theorem cell23_7260723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 2, 2, 2, 2].length) (baseStart_7260723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260723 prefixEnd_7260723 := by exact prefixLift 7260723
  have htrace : WordTrace (prefixWord ++ tailWord_7260723) baseStart_7260723 baseEnd_7260723 := by
    simpa [prefixWord, tailWord_7260723, baseEnd_7260723] using wordTrace_append hprefix tailTrace_7260723
  have hstable : (prefixWord ++ tailWord_7260723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260723).length < 2 ^ (prefixWord ++ tailWord_7260723).sum := by decide
  have hdescent : baseEnd_7260723 < baseStart_7260723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260726 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7260726 : Nat := 118140960795 + 7260726 * 2 ^ 59
def prefixEnd_7260726 : Nat := 4983230072969 + 3 ^ 40 * 7260726 * 2
def baseEnd_7260726 : Nat := 3728242338596864609833535

theorem tailTrace_7260726 : CollatzResearch.WordTrace tailWord_7260726 prefixEnd_7260726 3728242338596864609833535 := by
  unfold tailWord_7260726
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551277068352325632613627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176546955395758140081212021 16551277068352325632613627)
  ·
    refine ⟨24826915602528488448920441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16551277068352325632613627 24826915602528488448920441)
    ·
      refine ⟨18620186701896366336690331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24826915602528488448920441 18620186701896366336690331)
      ·
        refine ⟨27930280052844549505035497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18620186701896366336690331 27930280052844549505035497)
        ·
          refine ⟨20947710039633412128776623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27930280052844549505035497 20947710039633412128776623)
          ·
            refine ⟨31421565059450118193164935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20947710039633412128776623 31421565059450118193164935)
            ·
              refine ⟨47132347589175177289747403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31421565059450118193164935 47132347589175177289747403)
              ·
                refine ⟨70698521383762765934621105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47132347589175177289747403 70698521383762765934621105)
                ·
                  refine ⟨53023891037822074450965829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70698521383762765934621105 53023891037822074450965829)
                  ·
                    refine ⟨9941979569591638959556093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53023891037822074450965829 9941979569591638959556093)
                    ·
                      refine ⟨3728242338596864609833535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9941979569591638959556093 3728242338596864609833535)
                      ·
                        rfl

theorem cell23_7260726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7260726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260726 prefixEnd_7260726 := by exact prefixLift 7260726
  have htrace : WordTrace (prefixWord ++ tailWord_7260726) baseStart_7260726 baseEnd_7260726 := by
    simpa [prefixWord, tailWord_7260726, baseEnd_7260726] using wordTrace_append hprefix tailTrace_7260726
  have hstable : (prefixWord ++ tailWord_7260726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260726).length < 2 ^ (prefixWord ++ tailWord_7260726).sum := by decide
  have hdescent : baseEnd_7260726 < baseStart_7260726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260752 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_7260752 : Nat := 118140960795 + 7260752 * 2 ^ 59
def prefixEnd_7260752 : Nat := 4983230072969 + 3 ^ 40 * 7260752 * 2
def baseEnd_7260752 : Nat := 3728255689093881508108415

theorem tailTrace_7260752 : CollatzResearch.WordTrace tailWord_7260752 prefixEnd_7260752 3728255689093881508108415 := by
  unfold tailWord_7260752
  simp only [CollatzResearch.WordTrace]
  refine ⟨132410690695771508281132255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176547587594362011041509673 132410690695771508281132255)
  ·
    refine ⟨198616036043657262421698383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132410690695771508281132255 198616036043657262421698383)
    ·
      refine ⟨297924054065485893632547575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198616036043657262421698383 297924054065485893632547575)
      ·
        refine ⟨446886081098228840448821363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297924054065485893632547575 446886081098228840448821363)
        ·
          refine ⟨670329121647343260673232045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446886081098228840448821363 670329121647343260673232045)
          ·
            refine ⟨251373420617753722752462017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670329121647343260673232045 251373420617753722752462017)
            ·
              refine ⟨188530065463315292064346513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251373420617753722752462017 188530065463315292064346513)
              ·
                refine ⟨141397549097486469048259885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188530065463315292064346513 141397549097486469048259885)
                ·
                  refine ⟨53024080911557425893097457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141397549097486469048259885 53024080911557425893097457)
                  ·
                    refine ⟨39768060683668069419823093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53024080911557425893097457 39768060683668069419823093)
                    ·
                      refine ⟨3728255689093881508108415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39768060683668069419823093 3728255689093881508108415)
                      ·
                        rfl

theorem cell23_7260752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_7260752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260752 prefixEnd_7260752 := by exact prefixLift 7260752
  have htrace : WordTrace (prefixWord ++ tailWord_7260752) baseStart_7260752 baseEnd_7260752 := by
    simpa [prefixWord, tailWord_7260752, baseEnd_7260752] using wordTrace_append hprefix tailTrace_7260752
  have hstable : (prefixWord ++ tailWord_7260752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260752).length < 2 ^ (prefixWord ++ tailWord_7260752).sum := by decide
  have hdescent : baseEnd_7260752 < baseStart_7260752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260796 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_7260796 : Nat := 118140960795 + 7260796 * 2 ^ 59
def prefixEnd_7260796 : Nat := 4983230072969 + 3 ^ 40 * 7260796 * 2
def baseEnd_7260796 : Nat := 3728278282242679335958213

theorem tailTrace_7260796 : CollatzResearch.WordTrace tailWord_7260796 prefixEnd_7260796 3728278282242679335958213 := by
  unfold tailWord_7260796
  simp only [CollatzResearch.WordTrace]
  refine ⟨132411493101691806038433121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176548657468922408051244161 132411493101691806038433121)
  ·
    refine ⟨99308619826268854528824841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132411493101691806038433121 99308619826268854528824841)
    ·
      refine ⟨74481464869701640896618631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99308619826268854528824841 74481464869701640896618631)
      ·
        refine ⟨111722197304552461344927947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74481464869701640896618631 111722197304552461344927947)
        ·
          refine ⟨167583295956828692017391921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111722197304552461344927947 167583295956828692017391921)
          ·
            refine ⟨125687471967621519013043941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167583295956828692017391921 125687471967621519013043941)
            ·
              refine ⟨23566400993929034814945739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125687471967621519013043941 23566400993929034814945739)
              ·
                refine ⟨35349601490893552222418609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23566400993929034814945739 35349601490893552222418609)
                ·
                  refine ⟨26512201118170164166813957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35349601490893552222418609 26512201118170164166813957)
                  ·
                    refine ⟨4971037709656905781277617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26512201118170164166813957 4971037709656905781277617)
                    ·
                      refine ⟨3728278282242679335958213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971037709656905781277617 3728278282242679335958213)
                      ·
                        rfl

theorem cell23_7260796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_7260796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260796 prefixEnd_7260796 := by exact prefixLift 7260796
  have htrace : WordTrace (prefixWord ++ tailWord_7260796) baseStart_7260796 baseEnd_7260796 := by
    simpa [prefixWord, tailWord_7260796, baseEnd_7260796] using wordTrace_append hprefix tailTrace_7260796
  have hstable : (prefixWord ++ tailWord_7260796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260796).length < 2 ^ (prefixWord ++ tailWord_7260796).sum := by decide
  have hdescent : baseEnd_7260796 < baseStart_7260796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260799 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3]
def baseStart_7260799 : Nat := 118140960795 + 7260799 * 2 ^ 59
def prefixEnd_7260799 : Nat := 4983230072969 + 3 ^ 40 * 7260799 * 2
def baseEnd_7260799 : Nat := 3728279822684642824220699

theorem tailTrace_7260799 : CollatzResearch.WordTrace tailWord_7260799 prefixEnd_7260799 3728279822684642824220699 := by
  unfold tailWord_7260799
  simp only [CollatzResearch.WordTrace]
  refine ⟨264823095622372743589225451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176548730414915162392816967 264823095622372743589225451)
  ·
    refine ⟨397234643433559115383838177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264823095622372743589225451 397234643433559115383838177)
    ·
      refine ⟨297925982575169336537878633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397234643433559115383838177 297925982575169336537878633)
      ·
        refine ⟨223444486931377002403408975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297925982575169336537878633 223444486931377002403408975)
        ·
          refine ⟨335166730397065503605113463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223444486931377002403408975 335166730397065503605113463)
          ·
            refine ⟨502750095595598255407670195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335166730397065503605113463 502750095595598255407670195)
            ·
              refine ⟨754125143393397383111505293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502750095595598255407670195 754125143393397383111505293)
              ·
                refine ⟨282796928772524018666814485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 754125143393397383111505293 282796928772524018666814485)
                ·
                  refine ⟨13256106036212063375006929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282796928772524018666814485 13256106036212063375006929)
                  ·
                    refine ⟨9942079527159047531255197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256106036212063375006929 9942079527159047531255197)
                    ·
                      refine ⟨3728279822684642824220699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942079527159047531255197 3728279822684642824220699)
                      ·
                        rfl

theorem cell23_7260799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 2, 3].length) (baseStart_7260799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260799 prefixEnd_7260799 := by exact prefixLift 7260799
  have htrace : WordTrace (prefixWord ++ tailWord_7260799) baseStart_7260799 baseEnd_7260799 := by
    simpa [prefixWord, tailWord_7260799, baseEnd_7260799] using wordTrace_append hprefix tailTrace_7260799
  have hstable : (prefixWord ++ tailWord_7260799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260799).length < 2 ^ (prefixWord ++ tailWord_7260799).sum := by decide
  have hdescent : baseEnd_7260799 < baseStart_7260799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260833 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_7260833 : Nat := 118140960795 + 7260833 * 2 ^ 59
def prefixEnd_7260833 : Nat := 4983230072969 + 3 ^ 40 * 7260833 * 2
def baseEnd_7260833 : Nat := 3728297281026895691195543

theorem tailTrace_7260833 : CollatzResearch.WordTrace tailWord_7260833 prefixEnd_7260833 3728297281026895691195543 := by
  unfold tailWord_7260833
  simp only [CollatzResearch.WordTrace]
  refine ⟨264824335704249567395963153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176549557136166378263975435 264824335704249567395963153)
  ·
    refine ⟨198618251778187175546972365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264824335704249567395963153 198618251778187175546972365)
    ·
      refine ⟨74481844416820190830114637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198618251778187175546972365 74481844416820190830114637)
      ·
        refine ⟨27930691656307571561292989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74481844416820190830114637 27930691656307571561292989)
        ·
          refine ⟨10474009371115339335484871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27930691656307571561292989 10474009371115339335484871)
          ·
            refine ⟨15711014056673009003227307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474009371115339335484871 15711014056673009003227307)
            ·
              refine ⟨23566521085009513504840961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15711014056673009003227307 23566521085009513504840961)
              ·
                refine ⟨17674890813757135128630721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23566521085009513504840961 17674890813757135128630721)
                ·
                  refine ⟨13256168110317851346473041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17674890813757135128630721 13256168110317851346473041)
                  ·
                    refine ⟨9942126082738388509854781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256168110317851346473041 9942126082738388509854781)
                    ·
                      refine ⟨3728297281026895691195543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942126082738388509854781 3728297281026895691195543)
                      ·
                        rfl

theorem cell23_7260833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_7260833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260833 prefixEnd_7260833 := by exact prefixLift 7260833
  have htrace : WordTrace (prefixWord ++ tailWord_7260833) baseStart_7260833 baseEnd_7260833 := by
    simpa [prefixWord, tailWord_7260833, baseEnd_7260833] using wordTrace_append hprefix tailTrace_7260833
  have hstable : (prefixWord ++ tailWord_7260833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260833).length < 2 ^ (prefixWord ++ tailWord_7260833).sum := by decide
  have hdescent : baseEnd_7260833 < baseStart_7260833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260853 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 6]
def baseStart_7260853 : Nat := 118140960795 + 7260853 * 2 ^ 59
def prefixEnd_7260853 : Nat := 4983230072969 + 3 ^ 40 * 7260853 * 2
def baseEnd_7260853 : Nat := 414256394515553956993939

theorem tailTrace_7260853 : CollatzResearch.WordTrace tailWord_7260853 prefixEnd_7260853 414256394515553956993939 := by
  unfold tailWord_7260853
  simp only [CollatzResearch.WordTrace]
  refine ⟨264825065164177110811691213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176550043442784740541127475 264825065164177110811691213)
  ·
    refine ⟨99309399436566416554384205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264825065164177110811691213 99309399436566416554384205)
    ·
      refine ⟨37241024788712406207894077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99309399436566416554384205 37241024788712406207894077)
      ·
        refine ⟨13965384295767152327960279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37241024788712406207894077 13965384295767152327960279)
        ·
          refine ⟨20948076443650728491940419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13965384295767152327960279 20948076443650728491940419)
          ·
            refine ⟨31422114665476092737910629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948076443650728491940419 31422114665476092737910629)
            ·
              refine ⟨5891646499776767388358243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31422114665476092737910629 5891646499776767388358243)
              ·
                refine ⟨8837469749665151082537365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891646499776767388358243 8837469749665151082537365)
                ·
                  refine ⟨414256394515553956993939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8837469749665151082537365 414256394515553956993939)
                  ·
                    rfl

theorem cell23_7260853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 6].length) (baseStart_7260853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260853 prefixEnd_7260853 := by exact prefixLift 7260853
  have htrace : WordTrace (prefixWord ++ tailWord_7260853) baseStart_7260853 baseEnd_7260853 := by
    simpa [prefixWord, tailWord_7260853, baseEnd_7260853] using wordTrace_append hprefix tailTrace_7260853
  have hstable : (prefixWord ++ tailWord_7260853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260853).length < 2 ^ (prefixWord ++ tailWord_7260853).sum := by decide
  have hdescent : baseEnd_7260853 < baseStart_7260853 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260897 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_7260897 : Nat := 118140960795 + 7260897 * 2 ^ 59
def prefixEnd_7260897 : Nat := 4983230072969 + 3 ^ 40 * 7260897 * 2
def baseEnd_7260897 : Nat := 3728330143788783440795249

theorem tailTrace_7260897 : CollatzResearch.WordTrace tailWord_7260897 prefixEnd_7260897 3728330143788783440795249 := by
  unfold tailWord_7260897
  simp only [CollatzResearch.WordTrace]
  refine ⟨264826669976017706326292945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176551113317345137550861963 264826669976017706326292945)
  ·
    refine ⟨198620002482013279744719709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264826669976017706326292945 198620002482013279744719709)
    ·
      refine ⟨74482500930754979904269891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198620002482013279744719709 74482500930754979904269891)
      ·
        refine ⟨111723751396132469856404837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74482500930754979904269891 111723751396132469856404837)
        ·
          refine ⟨20948203386774838098075907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111723751396132469856404837 20948203386774838098075907)
          ·
            refine ⟨31422305080162257147113861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948203386774838098075907 31422305080162257147113861)
            ·
              refine ⟨5891682202530423215083849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31422305080162257147113861 5891682202530423215083849)
              ·
                refine ⟨4418761651897817411312887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5891682202530423215083849 4418761651897817411312887)
                ·
                  refine ⟨6628142477846726116969331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418761651897817411312887 6628142477846726116969331)
                  ·
                    refine ⟨9942213716770089175453997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6628142477846726116969331 9942213716770089175453997)
                    ·
                      refine ⟨3728330143788783440795249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942213716770089175453997 3728330143788783440795249)
                      ·
                        rfl

theorem cell23_7260897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_7260897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260897 prefixEnd_7260897 := by exact prefixLift 7260897
  have htrace : WordTrace (prefixWord ++ tailWord_7260897) baseStart_7260897 baseEnd_7260897 := by
    simpa [prefixWord, tailWord_7260897, baseEnd_7260897] using wordTrace_append hprefix tailTrace_7260897
  have hstable : (prefixWord ++ tailWord_7260897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260897).length < 2 ^ (prefixWord ++ tailWord_7260897).sum := by decide
  have hdescent : baseEnd_7260897 < baseStart_7260897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7260953 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 3]
def baseStart_7260953 : Nat := 118140960795 + 7260953 * 2 ^ 59
def prefixEnd_7260953 : Nat := 4983230072969 + 3 ^ 40 * 7260953 * 2
def baseEnd_7260953 : Nat := 3728358898705435221694991

theorem tailTrace_7260953 : CollatzResearch.WordTrace tailWord_7260953 prefixEnd_7260953 3728358898705435221694991 := by
  unfold tailWord_7260953
  simp only [CollatzResearch.WordTrace]
  refine ⟨264828712463814827890331513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176552474975876551926887675 264828712463814827890331513)
  ·
    refine ⟨198621534347861120917748635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264828712463814827890331513 198621534347861120917748635)
    ·
      refine ⟨297932301521791681376622953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198621534347861120917748635 297932301521791681376622953)
      ·
        refine ⟨223449226141343761032467215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297932301521791681376622953 223449226141343761032467215)
        ·
          refine ⟨335173839212015641548700823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223449226141343761032467215 335173839212015641548700823)
          ·
            refine ⟨502760758818023462323051235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335173839212015641548700823 502760758818023462323051235)
            ·
              refine ⟨754141138227035193484576853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502760758818023462323051235 754141138227035193484576853)
              ·
                refine ⟨8837591463598068673647385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 754141138227035193484576853 8837591463598068673647385)
                ·
                  refine ⟨6628193597698551505235539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8837591463598068673647385 6628193597698551505235539)
                  ·
                    refine ⟨9942290396547827257853309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6628193597698551505235539 9942290396547827257853309)
                    ·
                      refine ⟨3728358898705435221694991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942290396547827257853309 3728358898705435221694991)
                      ·
                        rfl

theorem cell23_7260953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 1, 3].length) (baseStart_7260953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7260953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7260953 prefixEnd_7260953 := by exact prefixLift 7260953
  have htrace : WordTrace (prefixWord ++ tailWord_7260953) baseStart_7260953 baseEnd_7260953 := by
    simpa [prefixWord, tailWord_7260953, baseEnd_7260953] using wordTrace_append hprefix tailTrace_7260953
  have hstable : (prefixWord ++ tailWord_7260953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7260953).length < 2 ^ (prefixWord ++ tailWord_7260953).sum := by decide
  have hdescent : baseEnd_7260953 < baseStart_7260953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7260953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261006 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7261006 : Nat := 118140960795 + 7261006 * 2 ^ 59
def prefixEnd_7261006 : Nat := 4983230072969 + 3 ^ 40 * 7261006 * 2
def baseEnd_7261006 : Nat := 3728386113180123514332247

theorem tailTrace_7261006 : CollatzResearch.WordTrace tailWord_7261006 prefixEnd_7261006 3728386113180123514332247 := by
  unfold tailWord_7261006
  simp only [CollatzResearch.WordTrace]
  refine ⟨33103830691577852242751359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176553763688415211961340581 33103830691577852242751359)
  ·
    refine ⟨49655746037366778364127039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33103830691577852242751359 49655746037366778364127039)
    ·
      refine ⟨74483619056050167546190559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49655746037366778364127039 74483619056050167546190559)
      ·
        refine ⟨111725428584075251319285839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74483619056050167546190559 111725428584075251319285839)
        ·
          refine ⟨167588142876112876978928759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111725428584075251319285839 167588142876112876978928759)
          ·
            refine ⟨251382214314169315468393139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167588142876112876978928759 251382214314169315468393139)
            ·
              refine ⟨377073321471253973202589709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251382214314169315468393139 377073321471253973202589709)
              ·
                refine ⟨141402495551720239950971141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 377073321471253973202589709 141402495551720239950971141)
                ·
                  refine ⟨26512967915947544990807089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141402495551720239950971141 26512967915947544990807089)
                  ·
                    refine ⟨19884725936960658743105317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26512967915947544990807089 19884725936960658743105317)
                    ·
                      refine ⟨3728386113180123514332247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19884725936960658743105317 3728386113180123514332247)
                      ·
                        rfl

theorem cell23_7261006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7261006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261006 prefixEnd_7261006 := by exact prefixLift 7261006
  have htrace : WordTrace (prefixWord ++ tailWord_7261006) baseStart_7261006 baseEnd_7261006 := by
    simpa [prefixWord, tailWord_7261006, baseEnd_7261006] using wordTrace_append hprefix tailTrace_7261006
  have hstable : (prefixWord ++ tailWord_7261006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261006).length < 2 ^ (prefixWord ++ tailWord_7261006).sum := by decide
  have hdescent : baseEnd_7261006 < baseStart_7261006 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261010 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_7261010 : Nat := 118140960795 + 7261010 * 2 ^ 59
def prefixEnd_7261010 : Nat := 4983230072969 + 3 ^ 40 * 7261010 * 2
def baseEnd_7261010 : Nat := 3728388167102741498682229

theorem tailTrace_7261010 : CollatzResearch.WordTrace tailWord_7261010 prefixEnd_7261010 3728388167102741498682229 := by
  unfold tailWord_7261010
  simp only [CollatzResearch.WordTrace]
  refine ⟨66207697856152081656289121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176553860949738884416770989 66207697856152081656289121)
  ·
    refine ⟨49655773392114061242216841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66207697856152081656289121 49655773392114061242216841)
    ·
      refine ⟨37241830044085545931662631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49655773392114061242216841 37241830044085545931662631)
      ·
        refine ⟨55862745066128318897493947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37241830044085545931662631 55862745066128318897493947)
        ·
          refine ⟨83794117599192478346240921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55862745066128318897493947 83794117599192478346240921)
          ·
            refine ⟨62845588199394358759680691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83794117599192478346240921 62845588199394358759680691)
            ·
              refine ⟨94268382299091538139521037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62845588199394358759680691 94268382299091538139521037)
              ·
                refine ⟨35350643362159326802320389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94268382299091538139521037 35350643362159326802320389)
                ·
                  refine ⟨6628245630404873775435073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35350643362159326802320389 6628245630404873775435073)
                  ·
                    refine ⟨4971184222803655331576305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628245630404873775435073 4971184222803655331576305)
                    ·
                      refine ⟨3728388167102741498682229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971184222803655331576305 3728388167102741498682229)
                      ·
                        rfl

theorem cell23_7261010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_7261010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261010 prefixEnd_7261010 := by exact prefixLift 7261010
  have htrace : WordTrace (prefixWord ++ tailWord_7261010) baseStart_7261010 baseEnd_7261010 := by
    simpa [prefixWord, tailWord_7261010, baseEnd_7261010] using wordTrace_append hprefix tailTrace_7261010
  have hstable : (prefixWord ++ tailWord_7261010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261010).length < 2 ^ (prefixWord ++ tailWord_7261010).sum := by decide
  have hdescent : baseEnd_7261010 < baseStart_7261010 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261027 : List Nat := [1, 1, 1, 5, 3, 2, 1, 3, 2, 2, 2]
def baseStart_7261027 : Nat := 118140960795 + 7261027 * 2 ^ 59
def prefixEnd_7261027 : Nat := 4983230072969 + 3 ^ 40 * 7261027 * 2
def baseEnd_7261027 : Nat := 3728396896273867932169651

theorem tailTrace_7261027 : CollatzResearch.WordTrace tailWord_7261027 prefixEnd_7261027 3728396896273867932169651 := by
  unfold tailWord_7261027
  simp only [CollatzResearch.WordTrace]
  refine ⟨264831411465546738528525335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176554274310364492352350223 264831411465546738528525335)
  ·
    refine ⟨397247117198320107792788003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264831411465546738528525335 397247117198320107792788003)
    ·
      refine ⟨595870675797480161689182005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397247117198320107792788003 595870675797480161689182005)
      ·
        refine ⟨55862875856013765158360813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 595870675797480161689182005 55862875856013765158360813)
        ·
          refine ⟨20948578446005161934385305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55862875856013765158360813 20948578446005161934385305)
          ·
            refine ⟨15711433834503871450788979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20948578446005161934385305 15711433834503871450788979)
            ·
              refine ⟨23567150751755807176183469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15711433834503871450788979 23567150751755807176183469)
              ·
                refine ⟨8837681531908427691068801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23567150751755807176183469 8837681531908427691068801)
                ·
                  refine ⟨6628261148931320768301601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8837681531908427691068801 6628261148931320768301601)
                  ·
                    refine ⟨4971195861698490576226201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628261148931320768301601 4971195861698490576226201)
                    ·
                      refine ⟨3728396896273867932169651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971195861698490576226201 3728396896273867932169651)
                      ·
                        rfl

theorem cell23_7261027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_7261027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261027 prefixEnd_7261027 := by exact prefixLift 7261027
  have htrace : WordTrace (prefixWord ++ tailWord_7261027) baseStart_7261027 baseEnd_7261027 := by
    simpa [prefixWord, tailWord_7261027, baseEnd_7261027] using wordTrace_append hprefix tailTrace_7261027
  have hstable : (prefixWord ++ tailWord_7261027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261027).length < 2 ^ (prefixWord ++ tailWord_7261027).sum := by decide
  have hdescent : baseEnd_7261027 < baseStart_7261027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261063 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 2, 5]
def baseStart_7261063 : Nat := 118140960795 + 7261063 * 2 ^ 59
def prefixEnd_7261063 : Nat := 4983230072969 + 3 ^ 40 * 7261063 * 2
def baseEnd_7261063 : Nat := 1242805127192476597106495

theorem tailTrace_7261063 : CollatzResearch.WordTrace tailWord_7261063 prefixEnd_7261063 1242805127192476597106495 := by
  unfold tailWord_7261063
  simp only [CollatzResearch.WordTrace]
  refine ⟨264832724493416316676835843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176555149662277544451223895 264832724493416316676835843)
  ·
    refine ⟨397249086740124475015253765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264832724493416316676835843 397249086740124475015253765)
    ·
      refine ⟨74484203763773339065360081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397249086740124475015253765 74484203763773339065360081)
      ·
        refine ⟨55863152822830004299020061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74484203763773339065360081 55863152822830004299020061)
        ·
          refine ⟨20948682308561251612132523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55863152822830004299020061 20948682308561251612132523)
          ·
            refine ⟨31423023462841877418198785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948682308561251612132523 31423023462841877418198785)
            ·
              refine ⟨23567267597131408063649089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31423023462841877418198785 23567267597131408063649089)
              ·
                refine ⟨17675450697848556047736817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23567267597131408063649089 17675450697848556047736817)
                ·
                  refine ⟨13256588023386417035802613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17675450697848556047736817 13256588023386417035802613)
                  ·
                    refine ⟨1242805127192476597106495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13256588023386417035802613 1242805127192476597106495)
                    ·
                      rfl

theorem cell23_7261063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_7261063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261063 prefixEnd_7261063 := by exact prefixLift 7261063
  have htrace : WordTrace (prefixWord ++ tailWord_7261063) baseStart_7261063 baseEnd_7261063 := by
    simpa [prefixWord, tailWord_7261063, baseEnd_7261063] using wordTrace_append hprefix tailTrace_7261063
  have hstable : (prefixWord ++ tailWord_7261063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261063).length < 2 ^ (prefixWord ++ tailWord_7261063).sum := by decide
  have hdescent : baseEnd_7261063 < baseStart_7261063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261103 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3]
def baseStart_7261103 : Nat := 118140960795 + 7261103 * 2 ^ 59
def prefixEnd_7261103 : Nat := 4983230072969 + 3 ^ 40 * 7261103 * 2
def baseEnd_7261103 : Nat := 3728435920803609634819301

theorem tailTrace_7261103 : CollatzResearch.WordTrace tailWord_7261103 prefixEnd_7261103 3728435920803609634819301 := by
  unfold tailWord_7261103
  simp only [CollatzResearch.WordTrace]
  refine ⟨264834183413271403508291963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176556122275514269005527975 264834183413271403508291963)
  ·
    refine ⟨397251275119907105262437945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264834183413271403508291963 397251275119907105262437945)
    ·
      refine ⟨297938456339930328946828459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397251275119907105262437945 297938456339930328946828459)
      ·
        refine ⟨446907684509895493420242689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297938456339930328946828459 446907684509895493420242689)
        ·
          refine ⟨335180763382421620065182017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446907684509895493420242689 335180763382421620065182017)
          ·
            refine ⟨251385572536816215048886513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335180763382421620065182017 251385572536816215048886513)
            ·
              refine ⟨188539179402612161286664885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251385572536816215048886513 188539179402612161286664885)
              ·
                refine ⟨17675548068994890120624833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188539179402612161286664885 17675548068994890120624833)
                ·
                  refine ⟨13256661051746167590468625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17675548068994890120624833 13256661051746167590468625)
                  ·
                    refine ⟨9942495788809625692851469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256661051746167590468625 9942495788809625692851469)
                    ·
                      refine ⟨3728435920803609634819301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942495788809625692851469 3728435920803609634819301)
                      ·
                        rfl

theorem cell23_7261103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 3].length) (baseStart_7261103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261103 prefixEnd_7261103 := by exact prefixLift 7261103
  have htrace : WordTrace (prefixWord ++ tailWord_7261103) baseStart_7261103 baseEnd_7261103 := by
    simpa [prefixWord, tailWord_7261103, baseEnd_7261103] using wordTrace_append hprefix tailTrace_7261103
  have hstable : (prefixWord ++ tailWord_7261103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261103).length < 2 ^ (prefixWord ++ tailWord_7261103).sum := by decide
  have hdescent : baseEnd_7261103 < baseStart_7261103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261160 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2]
def baseStart_7261160 : Nat := 118140960795 + 7261160 * 2 ^ 59
def prefixEnd_7261160 : Nat := 4983230072969 + 3 ^ 40 * 7261160 * 2
def baseEnd_7261160 : Nat := 3728465189200915911806539

theorem tailTrace_7261160 : CollatzResearch.WordTrace tailWord_7261160 prefixEnd_7261160 3728465189200915911806539 := by
  unfold tailWord_7261160
  simp only [CollatzResearch.WordTrace]
  refine ⟨132418131187032451121558467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176557508249376601495411289 132418131187032451121558467)
  ·
    refine ⟨198627196780548676682337701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132418131187032451121558467 198627196780548676682337701)
    ·
      refine ⟨37242599396352876877938319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198627196780548676682337701 37242599396352876877938319)
      ·
        refine ⟨55863899094529315316907479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37242599396352876877938319 55863899094529315316907479)
        ·
          refine ⟨83795848641793972975361219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55863899094529315316907479 83795848641793972975361219)
          ·
            refine ⟨125693772962690959463041829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83795848641793972975361219 125693772962690959463041829)
            ·
              refine ⟨23567582430504554899320343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125693772962690959463041829 23567582430504554899320343)
              ·
                refine ⟨35351373645756832348980515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23567582430504554899320343 35351373645756832348980515)
                ·
                  refine ⟨53027060468635248523470773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35351373645756832348980515 53027060468635248523470773)
                  ·
                    refine ⟨4971286918934554549075385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53027060468635248523470773 4971286918934554549075385)
                    ·
                      refine ⟨3728465189200915911806539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971286918934554549075385 3728465189200915911806539)
                      ·
                        rfl

theorem cell23_7261160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_7261160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261160 prefixEnd_7261160 := by exact prefixLift 7261160
  have htrace : WordTrace (prefixWord ++ tailWord_7261160) baseStart_7261160 baseEnd_7261160 := by
    simpa [prefixWord, tailWord_7261160, baseEnd_7261160] using wordTrace_append hprefix tailTrace_7261160
  have hstable : (prefixWord ++ tailWord_7261160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261160).length < 2 ^ (prefixWord ++ tailWord_7261160).sum := by decide
  have hdescent : baseEnd_7261160 < baseStart_7261160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261203 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4]
def baseStart_7261203 : Nat := 118140960795 + 7261203 * 2 ^ 59
def prefixEnd_7261203 : Nat := 4983230072969 + 3 ^ 40 * 7261203 * 2
def baseEnd_7261203 : Nat := 3728487268869059243568841

theorem tailTrace_7261203 : CollatzResearch.WordTrace tailWord_7261203 prefixEnd_7261203 3728487268869059243568841 := by
  unfold tailWord_7261203
  simp only [CollatzResearch.WordTrace]
  refine ⟨264837830712909120586932263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176558553808606080391288175 264837830712909120586932263)
  ·
    refine ⟨397256746069363680880398395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264837830712909120586932263 397256746069363680880398395)
    ·
      refine ⟨595885119104045521320597593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397256746069363680880398395 595885119104045521320597593)
      ·
        refine ⟨446913839328034140990448195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 595885119104045521320597593 446913839328034140990448195)
        ·
          refine ⟨670370758992051211485672293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446913839328034140990448195 670370758992051211485672293)
          ·
            refine ⟨125694517311009602153563555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670370758992051211485672293 125694517311009602153563555)
            ·
              refine ⟨188541775966514403230345333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125694517311009602153563555 188541775966514403230345333)
              ·
                refine ⟨17675791496860725302844875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 188541775966514403230345333 17675791496860725302844875)
                ·
                  refine ⟨26513687245291087954267313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17675791496860725302844875 26513687245291087954267313)
                  ·
                    refine ⟨19885265433968315965700485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26513687245291087954267313 19885265433968315965700485)
                    ·
                      refine ⟨3728487268869059243568841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19885265433968315965700485 3728487268869059243568841)
                      ·
                        rfl

theorem cell23_7261203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_7261203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261203 prefixEnd_7261203 := by exact prefixLift 7261203
  have htrace : WordTrace (prefixWord ++ tailWord_7261203) baseStart_7261203 baseEnd_7261203 := by
    simpa [prefixWord, tailWord_7261203, baseEnd_7261203] using wordTrace_append hprefix tailTrace_7261203
  have hstable : (prefixWord ++ tailWord_7261203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261203).length < 2 ^ (prefixWord ++ tailWord_7261203).sum := by decide
  have hdescent : baseEnd_7261203 < baseStart_7261203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261207 : List Nat := [1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7261207 : Nat := 118140960795 + 7261207 * 2 ^ 59
def prefixEnd_7261207 : Nat := 4983230072969 + 3 ^ 40 * 7261207 * 2
def baseEnd_7261207 : Nat := 3728489322791677227918823

theorem tailTrace_7261207 : CollatzResearch.WordTrace tailWord_7261207 prefixEnd_7261207 3728489322791677227918823 := by
  unfold tailWord_7261207
  simp only [CollatzResearch.WordTrace]
  refine ⟨264837976604894629270077875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176558651069929752846718583 264837976604894629270077875)
  ·
    refine ⟨397256964907341943905116813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264837976604894629270077875 397256964907341943905116813)
    ·
      refine ⟨148971361840253228964418805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397256964907341943905116813 148971361840253228964418805)
      ·
        refine ⟨13966065172523740215414263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 148971361840253228964418805 13966065172523740215414263)
        ·
          refine ⟨20949097758785610323121395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966065172523740215414263 20949097758785610323121395)
          ·
            refine ⟨31423646638178415484682093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20949097758785610323121395 31423646638178415484682093)
            ·
              refine ⟨11783867489316905806755785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31423646638178415484682093 11783867489316905806755785)
              ·
                refine ⟨8837900616987679355066839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11783867489316905806755785 8837900616987679355066839)
                ·
                  refine ⟨13256850925481519032600259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8837900616987679355066839 13256850925481519032600259)
                  ·
                    refine ⟨19885276388222278548900389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13256850925481519032600259 19885276388222278548900389)
                    ·
                      refine ⟨3728489322791677227918823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19885276388222278548900389 3728489322791677227918823)
                      ·
                        rfl

theorem cell23_7261207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7261207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261207 prefixEnd_7261207 := by exact prefixLift 7261207
  have htrace : WordTrace (prefixWord ++ tailWord_7261207) baseStart_7261207 baseEnd_7261207 := by
    simpa [prefixWord, tailWord_7261207, baseEnd_7261207] using wordTrace_append hprefix tailTrace_7261207
  have hstable : (prefixWord ++ tailWord_7261207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261207).length < 2 ^ (prefixWord ++ tailWord_7261207).sum := by decide
  have hdescent : baseEnd_7261207 < baseStart_7261207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261210 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3]
def baseStart_7261210 : Nat := 118140960795 + 7261210 * 2 ^ 59
def prefixEnd_7261210 : Nat := 4983230072969 + 3 ^ 40 * 7261210 * 2
def baseEnd_7261210 : Nat := 3728490863233640716181309

theorem tailTrace_7261210 : CollatzResearch.WordTrace tailWord_7261210 prefixEnd_7261210 3728490863233640716181309 := by
  unfold tailWord_7261210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66209521505970940195609271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176558724015922507188291389 66209521505970940195609271)
  ·
    refine ⟨99314282258956410293413907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66209521505970940195609271 99314282258956410293413907)
    ·
      refine ⟨148971423388434615440120861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99314282258956410293413907 148971423388434615440120861)
      ·
        refine ⟨55864283770662980790045323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148971423388434615440120861 55864283770662980790045323)
        ·
          refine ⟨83796425655994471185067985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55864283770662980790045323 83796425655994471185067985)
          ·
            refine ⟨62847319241995853388800989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83796425655994471185067985 62847319241995853388800989)
            ·
              refine ⟨23567744715748445020800371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62847319241995853388800989 23567744715748445020800371)
              ·
                refine ⟨35351617073622667531200557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23567744715748445020800371 35351617073622667531200557)
                ·
                  refine ⟨13256856402608500324200209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35351617073622667531200557 13256856402608500324200209)
                  ·
                    refine ⟨9942642301956375243150157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256856402608500324200209 9942642301956375243150157)
                    ·
                      refine ⟨3728490863233640716181309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942642301956375243150157 3728490863233640716181309)
                      ·
                        rfl

theorem cell23_7261210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_7261210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261210 prefixEnd_7261210 := by exact prefixLift 7261210
  have htrace : WordTrace (prefixWord ++ tailWord_7261210) baseStart_7261210 baseEnd_7261210 := by
    simpa [prefixWord, tailWord_7261210, baseEnd_7261210] using wordTrace_append hprefix tailTrace_7261210
  have hstable : (prefixWord ++ tailWord_7261210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261210).length < 2 ^ (prefixWord ++ tailWord_7261210).sum := by decide
  have hdescent : baseEnd_7261210 < baseStart_7261210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261220 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7261220 : Nat := 118140960795 + 7261220 * 2 ^ 59
def prefixEnd_7261220 : Nat := 4983230072969 + 3 ^ 40 * 7261220 * 2
def baseEnd_7261220 : Nat := 3728495998040185677056263

theorem tailTrace_7261220 : CollatzResearch.WordTrace tailWord_7261220 prefixEnd_7261220 3728495998040185677056263 := by
  unfold tailWord_7261220
  simp only [CollatzResearch.WordTrace]
  refine ⟨132419225376923766245150557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176558967169231688326867409 132419225376923766245150557)
  ·
    refine ⟨49657209516346412341931459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132419225376923766245150557 49657209516346412341931459)
    ·
      refine ⟨74485814274519618512897189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49657209516346412341931459 74485814274519618512897189)
      ·
        refine ⟨13966090176472428471168223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74485814274519618512897189 13966090176472428471168223)
        ·
          refine ⟨20949135264708642706752335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966090176472428471168223 20949135264708642706752335)
          ·
            refine ⟨31423702897062964060128503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20949135264708642706752335 31423702897062964060128503)
            ·
              refine ⟨47135554345594446090192755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31423702897062964060128503 47135554345594446090192755)
              ·
                refine ⟨70703331518391669135289133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47135554345594446090192755 70703331518391669135289133)
                ·
                  refine ⟨26513749319396875925733425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70703331518391669135289133 26513749319396875925733425)
                  ·
                    refine ⟨19885311989547656944300069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26513749319396875925733425 19885311989547656944300069)
                    ·
                      refine ⟨3728495998040185677056263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19885311989547656944300069 3728495998040185677056263)
                      ·
                        rfl

theorem cell23_7261220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7261220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261220 prefixEnd_7261220 := by exact prefixLift 7261220
  have htrace : WordTrace (prefixWord ++ tailWord_7261220) baseStart_7261220 baseEnd_7261220 := by
    simpa [prefixWord, tailWord_7261220, baseEnd_7261220] using wordTrace_append hprefix tailTrace_7261220
  have hstable : (prefixWord ++ tailWord_7261220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261220).length < 2 ^ (prefixWord ++ tailWord_7261220).sum := by decide
  have hdescent : baseEnd_7261220 < baseStart_7261220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261227 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 1, 2, 3]
def baseStart_7261227 : Nat := 118140960795 + 7261227 * 2 ^ 59
def prefixEnd_7261227 : Nat := 4983230072969 + 3 ^ 40 * 7261227 * 2
def baseEnd_7261227 : Nat := 3728499592404767149668731

theorem tailTrace_7261227 : CollatzResearch.WordTrace tailWord_7261227 prefixEnd_7261227 3728499592404767149668731 := by
  unfold tailWord_7261227
  simp only [CollatzResearch.WordTrace]
  refine ⟨264838706064822172685805935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176559137376548115123870623 264838706064822172685805935)
  ·
    refine ⟨397258059097233259028708903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264838706064822172685805935 397258059097233259028708903)
    ·
      refine ⟨595887088645849888543063355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397258059097233259028708903 595887088645849888543063355)
      ·
        refine ⟨893830632968774832814595033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595887088645849888543063355 893830632968774832814595033)
        ·
          refine ⟨670372974726581124610946275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 893830632968774832814595033 670372974726581124610946275)
          ·
            refine ⟨1005559462089871686916419413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670372974726581124610946275 1005559462089871686916419413)
            ·
              refine ⟨5891949973182841915525895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1005559462089871686916419413 5891949973182841915525895)
              ·
                refine ⟨8837924959774262873288843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891949973182841915525895 8837924959774262873288843)
                ·
                  refine ⟨13256887439661394309933265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8837924959774262873288843 13256887439661394309933265)
                  ·
                    refine ⟨9942665579746045732449949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256887439661394309933265 9942665579746045732449949)
                    ·
                      refine ⟨3728499592404767149668731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942665579746045732449949 3728499592404767149668731)
                      ·
                        rfl

theorem cell23_7261227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 2, 3].length) (baseStart_7261227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261227 prefixEnd_7261227 := by exact prefixLift 7261227
  have htrace : WordTrace (prefixWord ++ tailWord_7261227) baseStart_7261227 baseEnd_7261227 := by
    simpa [prefixWord, tailWord_7261227, baseEnd_7261227] using wordTrace_append hprefix tailTrace_7261227
  have hstable : (prefixWord ++ tailWord_7261227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261227).length < 2 ^ (prefixWord ++ tailWord_7261227).sum := by decide
  have hdescent : baseEnd_7261227 < baseStart_7261227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261241 : List Nat := [1, 2, 1, 5, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7261241 : Nat := 118140960795 + 7261241 * 2 ^ 59
def prefixEnd_7261241 : Nat := 4983230072969 + 3 ^ 40 * 7261241 * 2
def baseEnd_7261241 : Nat := 3728506781133930094893667

theorem tailTrace_7261241 : CollatzResearch.WordTrace tailWord_7261241 prefixEnd_7261241 3728506781133930094893667 := by
  unfold tailWord_7261241
  simp only [CollatzResearch.WordTrace]
  refine ⟨264839216686771453076815577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176559477791180968717877051 264839216686771453076815577)
  ·
    refine ⟨198629412515078589807611683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264839216686771453076815577 198629412515078589807611683)
    ·
      refine ⟨297944118772617884711417525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198629412515078589807611683 297944118772617884711417525)
      ·
        refine ⟨27932261134932926691695393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 297944118772617884711417525 27932261134932926691695393)
        ·
          refine ⟨20949195851199695018771545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27932261134932926691695393 20949195851199695018771545)
          ·
            refine ⟨15711896888399771264078659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20949195851199695018771545 15711896888399771264078659)
            ·
              refine ⟨23567845332599656896117989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15711896888399771264078659 23567845332599656896117989)
              ·
                refine ⟨4418970999862435668022123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23567845332599656896117989 4418970999862435668022123)
                ·
                  refine ⟨6628456499793653502033185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4418970999862435668022123 6628456499793653502033185)
                  ·
                    refine ⟨4971342374845240126524889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628456499793653502033185 4971342374845240126524889)
                    ·
                      refine ⟨3728506781133930094893667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971342374845240126524889 3728506781133930094893667)
                      ·
                        rfl

theorem cell23_7261241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7261241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261241 prefixEnd_7261241 := by exact prefixLift 7261241
  have htrace : WordTrace (prefixWord ++ tailWord_7261241) baseStart_7261241 baseEnd_7261241 := by
    simpa [prefixWord, tailWord_7261241, baseEnd_7261241] using wordTrace_append hprefix tailTrace_7261241
  have hstable : (prefixWord ++ tailWord_7261241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261241).length < 2 ^ (prefixWord ++ tailWord_7261241).sum := by decide
  have hdescent : baseEnd_7261241 < baseStart_7261241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261254 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7261254 : Nat := 118140960795 + 7261254 * 2 ^ 59
def prefixEnd_7261254 : Nat := 4983230072969 + 3 ^ 40 * 7261254 * 2
def baseEnd_7261254 : Nat := 3728513456382438544031107

theorem tailTrace_7261254 : CollatzResearch.WordTrace tailWord_7261254 prefixEnd_7261254 3728513456382438544031107 := by
  unfold tailWord_7261254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276240338616386134282463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 176559793890482904198025877 8276240338616386134282463)
  ·
    refine ⟨12414360507924579201423695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8276240338616386134282463 12414360507924579201423695)
    ·
      refine ⟨18621540761886868802135543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12414360507924579201423695 18621540761886868802135543)
      ·
        refine ⟨27932311142830303203203315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18621540761886868802135543 27932311142830303203203315)
        ·
          refine ⟨41898466714245454804804973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27932311142830303203203315 41898466714245454804804973)
          ·
            refine ⟨15711925017842045551801865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41898466714245454804804973 15711925017842045551801865)
            ·
              refine ⟨11783943763381534163851399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15711925017842045551801865 11783943763381534163851399)
              ·
                refine ⟨17675915645072301245777099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11783943763381534163851399 17675915645072301245777099)
                ·
                  refine ⟨26513873467608451868665649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17675915645072301245777099 26513873467608451868665649)
                  ·
                    refine ⟨19885405100706338901499237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26513873467608451868665649 19885405100706338901499237)
                    ·
                      refine ⟨3728513456382438544031107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19885405100706338901499237 3728513456382438544031107)
                      ·
                        rfl

theorem cell23_7261254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7261254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261254 prefixEnd_7261254 := by exact prefixLift 7261254
  have htrace : WordTrace (prefixWord ++ tailWord_7261254) baseStart_7261254 baseEnd_7261254 := by
    simpa [prefixWord, tailWord_7261254, baseEnd_7261254] using wordTrace_append hprefix tailTrace_7261254
  have hstable : (prefixWord ++ tailWord_7261254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261254).length < 2 ^ (prefixWord ++ tailWord_7261254).sum := by decide
  have hdescent : baseEnd_7261254 < baseStart_7261254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261278 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7261278 : Nat := 118140960795 + 7261278 * 2 ^ 59
def prefixEnd_7261278 : Nat := 4983230072969 + 3 ^ 40 * 7261278 * 2
def baseEnd_7261278 : Nat := 3728525779918146450130997

theorem tailTrace_7261278 : CollatzResearch.WordTrace tailWord_7261278 prefixEnd_7261278 3728525779918146450130997 := by
  unfold tailWord_7261278
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105070773454676049489061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176560377458424938930608325 33105070773454676049489061)
  ·
    refine ⟨6207200770022751759279199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33105070773454676049489061 6207200770022751759279199)
    ·
      refine ⟨9310801155034127638918799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207200770022751759279199 9310801155034127638918799)
      ·
        refine ⟨13966201732551191458378199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310801155034127638918799 13966201732551191458378199)
        ·
          refine ⟨20949302598826787187567299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966201732551191458378199 20949302598826787187567299)
          ·
            refine ⟨31423953898240180781350949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20949302598826787187567299 31423953898240180781350949)
            ·
              refine ⟨5891991355920033896503303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31423953898240180781350949 5891991355920033896503303)
              ·
                refine ⟨8837987033880050844754955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5891991355920033896503303 8837987033880050844754955)
                ·
                  refine ⟨13256980550820076267132433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8837987033880050844754955 13256980550820076267132433)
                  ·
                    refine ⟨9942735413115057200349325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13256980550820076267132433 9942735413115057200349325)
                    ·
                      refine ⟨3728525779918146450130997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942735413115057200349325 3728525779918146450130997)
                      ·
                        rfl

theorem cell23_7261278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7261278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261278 prefixEnd_7261278 := by exact prefixLift 7261278
  have htrace : WordTrace (prefixWord ++ tailWord_7261278) baseStart_7261278 baseEnd_7261278 := by
    simpa [prefixWord, tailWord_7261278, baseEnd_7261278] using wordTrace_append hprefix tailTrace_7261278
  have hstable : (prefixWord ++ tailWord_7261278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261278).length < 2 ^ (prefixWord ++ tailWord_7261278).sum := by decide
  have hdescent : baseEnd_7261278 < baseStart_7261278 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261283 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_7261283 : Nat := 118140960795 + 7261283 * 2 ^ 59
def prefixEnd_7261283 : Nat := 4983230072969 + 3 ^ 40 * 7261283 * 2
def baseEnd_7261283 : Nat := 3728528347321418930568473

theorem tailTrace_7261283 : CollatzResearch.WordTrace tailWord_7261283 prefixEnd_7261283 3728528347321418930568473 := by
  unfold tailWord_7261283
  simp only [CollatzResearch.WordTrace]
  refine ⟨264840748552619294249844503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176560499035079529499896335 264840748552619294249844503)
  ·
    refine ⟨397261122828928941374766755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264840748552619294249844503 397261122828928941374766755)
    ·
      refine ⟨595891684243393412062150133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397261122828928941374766755 595891684243393412062150133)
      ·
        refine ⟨55864845397818132380826575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 595891684243393412062150133 55864845397818132380826575)
        ·
          refine ⟨83797268096727198571239863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55864845397818132380826575 83797268096727198571239863)
          ·
            refine ⟨125695902145090797856859795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83797268096727198571239863 125695902145090797856859795)
            ·
              refine ⟨188543853217636196785289693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125695902145090797856859795 188543853217636196785289693)
              ·
                refine ⟨70703944956613573794483635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188543853217636196785289693 70703944956613573794483635)
                ·
                  refine ⟨106055917434920360691725453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70703944956613573794483635 106055917434920360691725453)
                  ·
                    refine ⟨39770969038095135259397045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106055917434920360691725453 39770969038095135259397045)
                    ·
                      refine ⟨3728528347321418930568473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39770969038095135259397045 3728528347321418930568473)
                      ·
                        rfl

theorem cell23_7261283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_7261283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261283 prefixEnd_7261283 := by exact prefixLift 7261283
  have htrace : WordTrace (prefixWord ++ tailWord_7261283) baseStart_7261283 baseEnd_7261283 := by
    simpa [prefixWord, tailWord_7261283, baseEnd_7261283] using wordTrace_append hprefix tailTrace_7261283
  have hstable : (prefixWord ++ tailWord_7261283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261283).length < 2 ^ (prefixWord ++ tailWord_7261283).sum := by decide
  have hdescent : baseEnd_7261283 < baseStart_7261283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261290 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_7261290 : Nat := 118140960795 + 7261290 * 2 ^ 59
def prefixEnd_7261290 : Nat := 4983230072969 + 3 ^ 40 * 7261290 * 2
def baseEnd_7261290 : Nat := 1242843980562000134393647

theorem tailTrace_7261290 : CollatzResearch.WordTrace tailWord_7261290 prefixEnd_7261290 1242843980562000134393647 := by
  unfold tailWord_7261290
  simp only [CollatzResearch.WordTrace]
  refine ⟨66210250965898483611337331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176560669242395956296899549 66210250965898483611337331)
  ·
    refine ⟨99315376448847725417005997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66210250965898483611337331 99315376448847725417005997)
    ·
      refine ⟨37243266168317897031377249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99315376448847725417005997 37243266168317897031377249)
      ·
        refine ⟨27932449626238422773532937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37243266168317897031377249 27932449626238422773532937)
        ·
          refine ⟨20949337219678817080149703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27932449626238422773532937 20949337219678817080149703)
          ·
            refine ⟨31424005829518225620224555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20949337219678817080149703 31424005829518225620224555)
            ·
              refine ⟨47136008744277338430336833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31424005829518225620224555 47136008744277338430336833)
              ·
                refine ⟨35352006558208003822752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47136008744277338430336833 35352006558208003822752625)
                ·
                  refine ⟨26514004918656002867064469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35352006558208003822752625 26514004918656002867064469)
                  ·
                    refine ⟨1242843980562000134393647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26514004918656002867064469 1242843980562000134393647)
                    ·
                      rfl

theorem cell23_7261290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_7261290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261290 prefixEnd_7261290 := by exact prefixLift 7261290
  have htrace : WordTrace (prefixWord ++ tailWord_7261290) baseStart_7261290 baseEnd_7261290 := by
    simpa [prefixWord, tailWord_7261290, baseEnd_7261290] using wordTrace_append hprefix tailTrace_7261290
  have hstable : (prefixWord ++ tailWord_7261290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261290).length < 2 ^ (prefixWord ++ tailWord_7261290).sum := by decide
  have hdescent : baseEnd_7261290 < baseStart_7261290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261354 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 7]
def baseStart_7261354 : Nat := 118140960795 + 7261354 * 2 ^ 59
def prefixEnd_7261354 : Nat := 4983230072969 + 3 ^ 40 * 7261354 * 2
def baseEnd_7261354 : Nat := 414284978271987572531183

theorem tailTrace_7261354 : CollatzResearch.WordTrace tailWord_7261354 prefixEnd_7261354 414284978271987572531183 := by
  unfold tailWord_7261354
  simp only [CollatzResearch.WordTrace]
  refine ⟨66210834533840518343919779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176562225423574715583786077 66210834533840518343919779)
  ·
    refine ⟨99316251800760777515879669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66210834533840518343919779 99316251800760777515879669)
    ·
      refine ⟨9310898606321322892113719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99316251800760777515879669 9310898606321322892113719)
      ·
        refine ⟨13966347909481984338170579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310898606321322892113719 13966347909481984338170579)
        ·
          refine ⟨20949521864222976507255869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966347909481984338170579 20949521864222976507255869)
          ·
            refine ⟨7856070699083616190220951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20949521864222976507255869 7856070699083616190220951)
            ·
              refine ⟨11784106048625424285331427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856070699083616190220951 11784106048625424285331427)
              ·
                refine ⟨17676159072938136427997141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784106048625424285331427 17676159072938136427997141)
                ·
                  refine ⟨414284978271987572531183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17676159072938136427997141 414284978271987572531183)
                  ·
                    rfl

theorem cell23_7261354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 7].length) (baseStart_7261354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261354 prefixEnd_7261354 := by exact prefixLift 7261354
  have htrace : WordTrace (prefixWord ++ tailWord_7261354) baseStart_7261354 baseEnd_7261354 := by
    simpa [prefixWord, tailWord_7261354, baseEnd_7261354] using wordTrace_append hprefix tailTrace_7261354
  have hstable : (prefixWord ++ tailWord_7261354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261354).length < 2 ^ (prefixWord ++ tailWord_7261354).sum := by decide
  have hdescent : baseEnd_7261354 < baseStart_7261354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261370 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_7261370 : Nat := 118140960795 + 7261370 * 2 ^ 59
def prefixEnd_7261370 : Nat := 4983230072969 + 3 ^ 40 * 7261370 * 2
def baseEnd_7261370 : Nat := 3728573020138360090180573

theorem tailTrace_7261370 : CollatzResearch.WordTrace tailWord_7261370 prefixEnd_7261370 3728573020138360090180573 := by
  unfold tailWord_7261370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66210980425826027027065391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176562614468869405405507709 66210980425826027027065391)
  ·
    refine ⟨99316470638739040540598087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66210980425826027027065391 99316470638739040540598087)
    ·
      refine ⟨148974705958108560810897131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99316470638739040540598087 148974705958108560810897131)
      ·
        refine ⟨223462058937162841216345697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148974705958108560810897131 223462058937162841216345697)
        ·
          refine ⟨167596544202872130912259273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223462058937162841216345697 167596544202872130912259273)
          ·
            refine ⟨125697408152154098184194455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167596544202872130912259273 125697408152154098184194455)
            ·
              refine ⟨188546112228231147276291683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125697408152154098184194455 188546112228231147276291683)
              ·
                refine ⟨282819168342346720914437525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188546112228231147276291683 282819168342346720914437525)
                ·
                  refine ⟨13257148516047502542864259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 282819168342346720914437525 13257148516047502542864259)
                  ·
                    refine ⟨19885722774071253814296389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13257148516047502542864259 19885722774071253814296389)
                    ·
                      refine ⟨3728573020138360090180573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19885722774071253814296389 3728573020138360090180573)
                      ·
                        rfl

theorem cell23_7261370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_7261370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261370 prefixEnd_7261370 := by exact prefixLift 7261370
  have htrace : WordTrace (prefixWord ++ tailWord_7261370) baseStart_7261370 baseEnd_7261370 := by
    simpa [prefixWord, tailWord_7261370, baseEnd_7261370] using wordTrace_append hprefix tailTrace_7261370
  have hstable : (prefixWord ++ tailWord_7261370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261370).length < 2 ^ (prefixWord ++ tailWord_7261370).sum := by decide
  have hdescent : baseEnd_7261370 < baseStart_7261370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261407 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3]
def baseStart_7261407 : Nat := 118140960795 + 7261407 * 2 ^ 59
def prefixEnd_7261407 : Nat := 4983230072969 + 3 ^ 40 * 7261407 * 2
def baseEnd_7261407 : Nat := 3728592018922576445417903

theorem tailTrace_7261407 : CollatzResearch.WordTrace tailWord_7261407 prefixEnd_7261407 3728592018922576445417903 := by
  unfold tailWord_7261407
  simp only [CollatzResearch.WordTrace]
  refine ⟨264845271204170063427358475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176563514136113375618238983 264845271204170063427358475)
  ·
    refine ⟨397267906806255095141037713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264845271204170063427358475 397267906806255095141037713)
    ·
      refine ⟨297950930104691321355778285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397267906806255095141037713 297950930104691321355778285)
      ·
        refine ⟨111731598789259245508416857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 297950930104691321355778285 111731598789259245508416857)
        ·
          refine ⟨83798699091944434131312643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111731598789259245508416857 83798699091944434131312643)
          ·
            refine ⟨125698048637916651196968965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83798699091944434131312643 125698048637916651196968965)
            ·
              refine ⟨23568384119609372099431681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125698048637916651196968965 23568384119609372099431681)
              ·
                refine ⟨17676288089707029074573761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23568384119609372099431681 17676288089707029074573761)
                ·
                  refine ⟨13257216067280271805930321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17676288089707029074573761 13257216067280271805930321)
                  ·
                    refine ⟨9942912050460203854447741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13257216067280271805930321 9942912050460203854447741)
                    ·
                      refine ⟨3728592018922576445417903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942912050460203854447741 3728592018922576445417903)
                      ·
                        rfl

theorem cell23_7261407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_7261407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261407 prefixEnd_7261407 := by exact prefixLift 7261407
  have htrace : WordTrace (prefixWord ++ tailWord_7261407) baseStart_7261407 baseEnd_7261407 := by
    simpa [prefixWord, tailWord_7261407, baseEnd_7261407] using wordTrace_append hprefix tailTrace_7261407
  have hstable : (prefixWord ++ tailWord_7261407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261407).length < 2 ^ (prefixWord ++ tailWord_7261407).sum := by decide
  have hdescent : baseEnd_7261407 < baseStart_7261407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261450 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7261450 : Nat := 118140960795 + 7261450 * 2 ^ 59
def prefixEnd_7261450 : Nat := 4983230072969 + 3 ^ 40 * 7261450 * 2
def baseEnd_7261450 : Nat := 3728614098590719777180205

theorem tailTrace_7261450 : CollatzResearch.WordTrace tailWord_7261450 prefixEnd_7261450 3728614098590719777180205 := by
  unfold tailWord_7261450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66211709885753570442793451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176564559695342854514115869 66211709885753570442793451)
  ·
    refine ⟨99317564828630355664190177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66211709885753570442793451 99317564828630355664190177)
    ·
      refine ⟨74488173621472766748142633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99317564828630355664190177 74488173621472766748142633)
      ·
        refine ⟨55866130216104575061106975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74488173621472766748142633 55866130216104575061106975)
        ·
          refine ⟨83799195324156862591660463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55866130216104575061106975 83799195324156862591660463)
          ·
            refine ⟨125698792986235293887490695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83799195324156862591660463 125698792986235293887490695)
            ·
              refine ⟨188548189479352940831236043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125698792986235293887490695 188548189479352940831236043)
              ·
                refine ⟨282822284219029411246854065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188548189479352940831236043 282822284219029411246854065)
                ·
                  refine ⟨212116713164272058435140549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 282822284219029411246854065 212116713164272058435140549)
                  ·
                    refine ⟨39771883718301010956588853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212116713164272058435140549 39771883718301010956588853)
                    ·
                      refine ⟨3728614098590719777180205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39771883718301010956588853 3728614098590719777180205)
                      ·
                        rfl

theorem cell23_7261450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7261450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261450 prefixEnd_7261450 := by exact prefixLift 7261450
  have htrace : WordTrace (prefixWord ++ tailWord_7261450) baseStart_7261450 baseEnd_7261450 := by
    simpa [prefixWord, tailWord_7261450, baseEnd_7261450] using wordTrace_append hprefix tailTrace_7261450
  have hstable : (prefixWord ++ tailWord_7261450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261450).length < 2 ^ (prefixWord ++ tailWord_7261450).sum := by decide
  have hdescent : baseEnd_7261450 < baseStart_7261450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261457 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_7261457 : Nat := 118140960795 + 7261457 * 2 ^ 59
def prefixEnd_7261457 : Nat := 4983230072969 + 3 ^ 40 * 7261457 * 2
def baseEnd_7261457 : Nat := 1242872564318433749930891

theorem tailTrace_7261457 : CollatzResearch.WordTrace tailWord_7261457 prefixEnd_7261457 1242872564318433749930891 := by
  unfold tailWord_7261457
  simp only [CollatzResearch.WordTrace]
  refine ⟨264847094853988921966678625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176564729902659281311119083 264847094853988921966678625)
  ·
    refine ⟨198635321140491691475008969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264847094853988921966678625 198635321140491691475008969)
    ·
      refine ⟨148976490855368768606256727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198635321140491691475008969 148976490855368768606256727)
      ·
        refine ⟨223464736283053152909385091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148976490855368768606256727 223464736283053152909385091)
        ·
          refine ⟨335197104424579729364077637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223464736283053152909385091 335197104424579729364077637)
          ·
            refine ⟨62849457079608699255764557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335197104424579729364077637 62849457079608699255764557)
            ·
              refine ⟨23568546404853262220911709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62849457079608699255764557 23568546404853262220911709)
              ·
                refine ⟨8838204901819973332841891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23568546404853262220911709 8838204901819973332841891)
                ·
                  refine ⟨13257307352729959999262837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8838204901819973332841891 13257307352729959999262837)
                  ·
                    refine ⟨1242872564318433749930891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13257307352729959999262837 1242872564318433749930891)
                    ·
                      rfl

theorem cell23_7261457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_7261457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261457 prefixEnd_7261457 := by exact prefixLift 7261457
  have htrace : WordTrace (prefixWord ++ tailWord_7261457) baseStart_7261457 baseEnd_7261457 := by
    simpa [prefixWord, tailWord_7261457, baseEnd_7261457] using wordTrace_append hprefix tailTrace_7261457
  have hstable : (prefixWord ++ tailWord_7261457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261457).length < 2 ^ (prefixWord ++ tailWord_7261457).sum := by decide
  have hdescent : baseEnd_7261457 < baseStart_7261457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261471 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 3]
def baseStart_7261471 : Nat := 118140960795 + 7261471 * 2 ^ 59
def prefixEnd_7261471 : Nat := 4983230072969 + 3 ^ 40 * 7261471 * 2
def baseEnd_7261471 : Nat := 3728624881684464195017609

theorem tailTrace_7261471 : CollatzResearch.WordTrace tailWord_7261471 prefixEnd_7261471 3728624881684464195017609 := by
  unfold tailWord_7261471
  simp only [CollatzResearch.WordTrace]
  refine ⟨264847605475938202357688267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176565070317292134905125511 264847605475938202357688267)
  ·
    refine ⟨397271408213907303536532401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264847605475938202357688267 397271408213907303536532401)
    ·
      refine ⟨297953556160430477652399301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397271408213907303536532401 297953556160430477652399301)
      ·
        refine ⟨55866291780080714559824869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 297953556160430477652399301 55866291780080714559824869)
        ·
          refine ⟨10474929708765133979967163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55866291780080714559824869 10474929708765133979967163)
          ·
            refine ⟨15712394563147700969950745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10474929708765133979967163 15712394563147700969950745)
            ·
              refine ⟨11784295922360775727463059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15712394563147700969950745 11784295922360775727463059)
              ·
                refine ⟨17676443883541163591194589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784295922360775727463059 17676443883541163591194589)
                ·
                  refine ⟨6628666456327936346697971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17676443883541163591194589 6628666456327936346697971)
                  ·
                    refine ⟨9942999684491904520046957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6628666456327936346697971 9942999684491904520046957)
                    ·
                      refine ⟨3728624881684464195017609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9942999684491904520046957 3728624881684464195017609)
                      ·
                        rfl

theorem cell23_7261471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_7261471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261471 prefixEnd_7261471 := by exact prefixLift 7261471
  have htrace : WordTrace (prefixWord ++ tailWord_7261471) baseStart_7261471 baseEnd_7261471 := by
    simpa [prefixWord, tailWord_7261471, baseEnd_7261471] using wordTrace_append hprefix tailTrace_7261471
  have hstable : (prefixWord ++ tailWord_7261471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261471).length < 2 ^ (prefixWord ++ tailWord_7261471).sum := by decide
  have hdescent : baseEnd_7261471 < baseStart_7261471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261505 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7261505 : Nat := 118140960795 + 7261505 * 2 ^ 59
def prefixEnd_7261505 : Nat := 4983230072969 + 3 ^ 40 * 7261505 * 2
def baseEnd_7261505 : Nat := 3728642340026717061992453

theorem tailTrace_7261505 : CollatzResearch.WordTrace tailWord_7261505 prefixEnd_7261505 3728642340026717061992453 := by
  unfold tailWord_7261505
  simp only [CollatzResearch.WordTrace]
  refine ⟨264848845557815026164425969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176565897038543350776283979 264848845557815026164425969)
  ·
    refine ⟨198636634168361269623319477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264848845557815026164425969 198636634168361269623319477)
    ·
      refine ⟨18622184453283869027186201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198636634168361269623319477 18622184453283869027186201)
      ·
        refine ⟨13966638339962901770389651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18622184453283869027186201 13966638339962901770389651)
        ·
          refine ⟨20949957509944352655584477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13966638339962901770389651 20949957509944352655584477)
          ·
            refine ⟨7856234066229132245844179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20949957509944352655584477 7856234066229132245844179)
            ·
              refine ⟨11784351099343698368766269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856234066229132245844179 11784351099343698368766269)
              ·
                refine ⟨4419131662253886888287351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11784351099343698368766269 4419131662253886888287351)
                ·
                  refine ⟨6628697493380830332431027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419131662253886888287351 6628697493380830332431027)
                  ·
                    refine ⟨9943046240071245498646541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6628697493380830332431027 9943046240071245498646541)
                    ·
                      refine ⟨3728642340026717061992453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943046240071245498646541 3728642340026717061992453)
                      ·
                        rfl

theorem cell23_7261505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7261505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261505 prefixEnd_7261505 := by exact prefixLift 7261505
  have htrace : WordTrace (prefixWord ++ tailWord_7261505) baseStart_7261505 baseEnd_7261505 := by
    simpa [prefixWord, tailWord_7261505, baseEnd_7261505] using wordTrace_append hprefix tailTrace_7261505
  have hstable : (prefixWord ++ tailWord_7261505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261505).length < 2 ^ (prefixWord ++ tailWord_7261505).sum := by decide
  have hdescent : baseEnd_7261505 < baseStart_7261505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261624 : List Nat := [2, 1, 2, 1, 2, 2, 3, 5, 5]
def baseStart_7261624 : Nat := 118140960795 + 7261624 * 2 ^ 59
def prefixEnd_7261624 : Nat := 4983230072969 + 3 ^ 40 * 7261624 * 2
def baseEnd_7261624 : Nat := 414300382691622455156045

theorem tailTrace_7261624 : CollatzResearch.WordTrace tailWord_7261624 prefixEnd_7261624 414300382691622455156045 := by
  unfold tailWord_7261624
  simp only [CollatzResearch.WordTrace]
  refine ⟨132426592922191954744003963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176568790562922606325338617 132426592922191954744003963)
  ·
    refine ⟨198639889383287932116005945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132426592922191954744003963 198639889383287932116005945)
    ·
      refine ⟨148979917037465949087004459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198639889383287932116005945 148979917037465949087004459)
      ·
        refine ⟨223469875556198923630506689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148979917037465949087004459 223469875556198923630506689)
        ·
          refine ⟨167602406667149192722880017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223469875556198923630506689 167602406667149192722880017)
          ·
            refine ⟨125701805000361894542160013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167602406667149192722880017 125701805000361894542160013)
            ·
              refine ⟨47138176875135710453310005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125701805000361894542160013 47138176875135710453310005)
              ·
                refine ⟨4419204082043972854997813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47138176875135710453310005 4419204082043972854997813)
                ·
                  refine ⟨414300382691622455156045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4419204082043972854997813 414300382691622455156045)
                  ·
                    rfl

theorem cell23_7261624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 5].length) (baseStart_7261624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261624 prefixEnd_7261624 := by exact prefixLift 7261624
  have htrace : WordTrace (prefixWord ++ tailWord_7261624) baseStart_7261624 baseEnd_7261624 := by
    simpa [prefixWord, tailWord_7261624, baseEnd_7261624] using wordTrace_append hprefix tailTrace_7261624
  have hstable : (prefixWord ++ tailWord_7261624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261624).length < 2 ^ (prefixWord ++ tailWord_7261624).sum := by decide
  have hdescent : baseEnd_7261624 < baseStart_7261624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261647 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_7261647 : Nat := 118140960795 + 7261647 * 2 ^ 59
def prefixEnd_7261647 : Nat := 4983230072969 + 3 ^ 40 * 7261647 * 2
def baseEnd_7261647 : Nat := 3728715254279655506416799

theorem tailTrace_7261647 : CollatzResearch.WordTrace tailWord_7261647 prefixEnd_7261647 3728715254279655506416799 := by
  unfold tailWord_7261647
  simp only [CollatzResearch.WordTrace]
  refine ⟨264854024723300584416095195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176569349815533722944063463 264854024723300584416095195)
  ·
    refine ⟨397281037084950876624142793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264854024723300584416095195 397281037084950876624142793)
    ·
      refine ⟨297960777813713157468107095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397281037084950876624142793 297960777813713157468107095)
      ·
        refine ⟨446941166720569736202160643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297960777813713157468107095 446941166720569736202160643)
        ·
          refine ⟨670411750080854604303240965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446941166720569736202160643 670411750080854604303240965)
          ·
            refine ⟨125702203140160238306857681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670411750080854604303240965 125702203140160238306857681)
            ·
              refine ⟨94276652355120178730143261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125702203140160238306857681 94276652355120178730143261)
              ·
                refine ⟨35353744633170067023803723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94276652355120178730143261 35353744633170067023803723)
                ·
                  refine ⟨53030616949755100535705585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35353744633170067023803723 53030616949755100535705585)
                  ·
                    refine ⟨39772962712316325401779189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53030616949755100535705585 39772962712316325401779189)
                    ·
                      refine ⟨3728715254279655506416799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39772962712316325401779189 3728715254279655506416799)
                      ·
                        rfl

theorem cell23_7261647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_7261647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261647 prefixEnd_7261647 := by exact prefixLift 7261647
  have htrace : WordTrace (prefixWord ++ tailWord_7261647) baseStart_7261647 baseEnd_7261647 := by
    simpa [prefixWord, tailWord_7261647, baseEnd_7261647] using wordTrace_append hprefix tailTrace_7261647
  have hstable : (prefixWord ++ tailWord_7261647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261647).length < 2 ^ (prefixWord ++ tailWord_7261647).sum := by decide
  have hdescent : baseEnd_7261647 < baseStart_7261647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261652 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7261652 : Nat := 118140960795 + 7261652 * 2 ^ 59
def prefixEnd_7261652 : Nat := 4983230072969 + 3 ^ 40 * 7261652 * 2
def baseEnd_7261652 : Nat := 3728717821682927986854277

theorem tailTrace_7261652 : CollatzResearch.WordTrace tailWord_7261652 prefixEnd_7261652 3728717821682927986854277 := by
  unfold tailWord_7261652
  simp only [CollatzResearch.WordTrace]
  refine ⟨132427103544141235135013605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176569471392188313513351473 132427103544141235135013605)
  ·
    refine ⟨24830081914526481587815051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132427103544141235135013605 24830081914526481587815051)
    ·
      refine ⟨37245122871789722381722577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24830081914526481587815051 37245122871789722381722577)
      ·
        refine ⟨27933842153842291786291933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37245122871789722381722577 27933842153842291786291933)
        ·
          refine ⟨10475190807690859419859475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27933842153842291786291933 10475190807690859419859475)
          ·
            refine ⟨15712786211536289129789213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10475190807690859419859475 15712786211536289129789213)
            ·
              refine ⟨5892294829326108423670955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15712786211536289129789213 5892294829326108423670955)
              ·
                refine ⟨8838442243989162635506433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892294829326108423670955 8838442243989162635506433)
                ·
                  refine ⟨6628831682991871976629825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838442243989162635506433 6628831682991871976629825)
                  ·
                    refine ⟨4971623762243903982472369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6628831682991871976629825 4971623762243903982472369)
                    ·
                      refine ⟨3728717821682927986854277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971623762243903982472369 3728717821682927986854277)
                      ·
                        rfl

theorem cell23_7261652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7261652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261652 prefixEnd_7261652 := by exact prefixLift 7261652
  have htrace : WordTrace (prefixWord ++ tailWord_7261652) baseStart_7261652 baseEnd_7261652 := by
    simpa [prefixWord, tailWord_7261652, baseEnd_7261652] using wordTrace_append hprefix tailTrace_7261652
  have hstable : (prefixWord ++ tailWord_7261652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261652).length < 2 ^ (prefixWord ++ tailWord_7261652).sum := by decide
  have hdescent : baseEnd_7261652 < baseStart_7261652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261687 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_7261687 : Nat := 118140960795 + 7261687 * 2 ^ 59
def prefixEnd_7261687 : Nat := 4983230072969 + 3 ^ 40 * 7261687 * 2
def baseEnd_7261687 : Nat := 3728735793505835349916615

theorem tailTrace_7261687 : CollatzResearch.WordTrace tailWord_7261687 prefixEnd_7261687 3728735793505835349916615 := by
  unfold tailWord_7261687
  simp only [CollatzResearch.WordTrace]
  refine ⟨264855483643155671247551315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176570322428770447498367543 264855483643155671247551315)
  ·
    refine ⟨397283225464733506871326973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264855483643155671247551315 397283225464733506871326973)
    ·
      refine ⟨148981209549275065076747615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397283225464733506871326973 148981209549275065076747615)
      ·
        refine ⟨223471814323912597615121423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148981209549275065076747615 223471814323912597615121423)
        ·
          refine ⟨335207721485868896422682135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223471814323912597615121423 335207721485868896422682135)
          ·
            refine ⟨502811582228803344634023203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335207721485868896422682135 502811582228803344634023203)
            ·
              refine ⟨754217373343205016951034805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502811582228803344634023203 754217373343205016951034805)
              ·
                refine ⟨70707878750925470339159513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754217373343205016951034805 70707878750925470339159513)
                ·
                  refine ⟨53030909063194102754369635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70707878750925470339159513 53030909063194102754369635)
                  ·
                    refine ⟨79546363594791154131554453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53030909063194102754369635 79546363594791154131554453)
                    ·
                      refine ⟨3728735793505835349916615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79546363594791154131554453 3728735793505835349916615)
                      ·
                        rfl

theorem cell23_7261687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_7261687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261687 prefixEnd_7261687 := by exact prefixLift 7261687
  have htrace : WordTrace (prefixWord ++ tailWord_7261687) baseStart_7261687 baseEnd_7261687 := by
    simpa [prefixWord, tailWord_7261687, baseEnd_7261687] using wordTrace_append hprefix tailTrace_7261687
  have hstable : (prefixWord ++ tailWord_7261687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261687).length < 2 ^ (prefixWord ++ tailWord_7261687).sum := by decide
  have hdescent : baseEnd_7261687 < baseStart_7261687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261728 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7261728 : Nat := 118140960795 + 7261728 * 2 ^ 59
def prefixEnd_7261728 : Nat := 4983230072969 + 3 ^ 40 * 7261728 * 2
def baseEnd_7261728 : Nat := 3728756846212669689503927

theorem tailTrace_7261728 : CollatzResearch.WordTrace tailWord_7261728 prefixEnd_7261728 3728756846212669689503927 := by
  unfold tailWord_7261728
  simp only [CollatzResearch.WordTrace]
  refine ⟨132428489518003567624896919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176571319357338090166529225 132428489518003567624896919)
  ·
    refine ⟨198642734277005351437345379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132428489518003567624896919 198642734277005351437345379)
    ·
      refine ⟨297964101415508027156018069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198642734277005351437345379 297964101415508027156018069)
      ·
        refine ⟨13967067253851938772938347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 297964101415508027156018069 13967067253851938772938347)
        ·
          refine ⟨20950600880777908159407521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13967067253851938772938347 20950600880777908159407521)
          ·
            refine ⟨15712950660583431119555641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20950600880777908159407521 15712950660583431119555641)
            ·
              refine ⟨11784712995437573339666731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15712950660583431119555641 11784712995437573339666731)
              ·
                refine ⟨17677069493156360009500097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11784712995437573339666731 17677069493156360009500097)
                ·
                  refine ⟨13257802119867270007125073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17677069493156360009500097 13257802119867270007125073)
                  ·
                    refine ⟨9943351589900452505343805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13257802119867270007125073 9943351589900452505343805)
                    ·
                      refine ⟨3728756846212669689503927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943351589900452505343805 3728756846212669689503927)
                      ·
                        rfl

theorem cell23_7261728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7261728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261728 prefixEnd_7261728 := by exact prefixLift 7261728
  have htrace : WordTrace (prefixWord ++ tailWord_7261728) baseStart_7261728 baseEnd_7261728 := by
    simpa [prefixWord, tailWord_7261728, baseEnd_7261728] using wordTrace_append hprefix tailTrace_7261728
  have hstable : (prefixWord ++ tailWord_7261728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261728).length < 2 ^ (prefixWord ++ tailWord_7261728).sum := by decide
  have hdescent : baseEnd_7261728 < baseStart_7261728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261781 : List Nat := [1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7261781 : Nat := 118140960795 + 7261781 * 2 ^ 59
def prefixEnd_7261781 : Nat := 4983230072969 + 3 ^ 40 * 7261781 * 2
def baseEnd_7261781 : Nat := 3728784060687357982141183

theorem tailTrace_7261781 : CollatzResearch.WordTrace tailWord_7261781 prefixEnd_7261781 3728784060687357982141183 := by
  unfold tailWord_7261781
  simp only [CollatzResearch.WordTrace]
  refine ⟨264858912104815125301473197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176572608069876750200982131 264858912104815125301473197)
  ·
    refine ⟨99322092039305671988052449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264858912104815125301473197 99322092039305671988052449)
    ·
      refine ⟨74491569029479253991039337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99322092039305671988052449 74491569029479253991039337)
      ·
        refine ⟨55868676772109440493279503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74491569029479253991039337 55868676772109440493279503)
        ·
          refine ⟨83803015158164160739919255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55868676772109440493279503 83803015158164160739919255)
          ·
            refine ⟨125704522737246241109878883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83803015158164160739919255 125704522737246241109878883)
            ·
              refine ⟨188556784105869361664818325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125704522737246241109878883 188556784105869361664818325)
              ·
                refine ⟨8838599254962626328038359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188556784105869361664818325 8838599254962626328038359)
                ·
                  refine ⟨13257898882443939492057539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8838599254962626328038359 13257898882443939492057539)
                  ·
                    refine ⟨19886848323665909238086309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13257898882443939492057539 19886848323665909238086309)
                    ·
                      refine ⟨3728784060687357982141183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19886848323665909238086309 3728784060687357982141183)
                      ·
                        rfl

theorem cell23_7261781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7261781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261781 prefixEnd_7261781 := by exact prefixLift 7261781
  have htrace : WordTrace (prefixWord ++ tailWord_7261781) baseStart_7261781 baseEnd_7261781 := by
    simpa [prefixWord, tailWord_7261781, baseEnd_7261781] using wordTrace_append hprefix tailTrace_7261781
  have hstable : (prefixWord ++ tailWord_7261781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261781).length < 2 ^ (prefixWord ++ tailWord_7261781).sum := by decide
  have hdescent : baseEnd_7261781 < baseStart_7261781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261808 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 2, 4]
def baseStart_7261808 : Nat := 118140960795 + 7261808 * 2 ^ 59
def prefixEnd_7261808 : Nat := 4983230072969 + 3 ^ 40 * 7261808 * 2
def baseEnd_7261808 : Nat := 1242932641555009792167853

theorem tailTrace_7261808 : CollatzResearch.WordTrace tailWord_7261808 prefixEnd_7261808 1242932641555009792167853 := by
  unfold tailWord_7261808
  simp only [CollatzResearch.WordTrace]
  refine ⟨132429948437858654456353039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176573264583811539275137385 132429948437858654456353039)
  ·
    refine ⟨198644922656787981684529559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132429948437858654456353039 198644922656787981684529559)
    ·
      refine ⟨297967383985181972526794339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198644922656787981684529559 297967383985181972526794339)
      ·
        refine ⟨446951075977772958790191509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297967383985181972526794339 446951075977772958790191509)
        ·
          refine ⟨20950831686458107443290227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 446951075977772958790191509 20950831686458107443290227)
          ·
            refine ⟨31426247529687161164935341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20950831686458107443290227 31426247529687161164935341)
            ·
              refine ⟨11784842823632685436850753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31426247529687161164935341 11784842823632685436850753)
              ·
                refine ⟨8838632117724514077638065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11784842823632685436850753 8838632117724514077638065)
                ·
                  refine ⟨6628974088293385558228549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838632117724514077638065 6628974088293385558228549)
                  ·
                    refine ⟨1242932641555009792167853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6628974088293385558228549 1242932641555009792167853)
                    ·
                      rfl

theorem cell23_7261808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 4].length) (baseStart_7261808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261808 prefixEnd_7261808 := by exact prefixLift 7261808
  have htrace : WordTrace (prefixWord ++ tailWord_7261808) baseStart_7261808 baseEnd_7261808 := by
    simpa [prefixWord, tailWord_7261808, baseEnd_7261808] using wordTrace_append hprefix tailTrace_7261808
  have hstable : (prefixWord ++ tailWord_7261808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261808).length < 2 ^ (prefixWord ++ tailWord_7261808).sum := by decide
  have hdescent : baseEnd_7261808 < baseStart_7261808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261825 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 2, 4]
def baseStart_7261825 : Nat := 118140960795 + 7261825 * 2 ^ 59
def prefixEnd_7261825 : Nat := 4983230072969 + 3 ^ 40 * 7261825 * 2
def baseEnd_7261825 : Nat := 1242935551278718603330327

theorem tailTrace_7261825 : CollatzResearch.WordTrace tailWord_7261825 prefixEnd_7261825 1242935551278718603330327 := by
  unfold tailWord_7261825
  simp only [CollatzResearch.WordTrace]
  refine ⟨264860516916655720816074929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176573677944437147210716619 264860516916655720816074929)
  ·
    refine ⟨198645387687491790612056197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264860516916655720816074929 198645387687491790612056197)
    ·
      refine ⟨37246010191404710739760537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198645387687491790612056197 37246010191404710739760537)
      ·
        refine ⟨27934507643553533054820403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37246010191404710739760537 27934507643553533054820403)
        ·
          refine ⟨41901761465330299582230605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27934507643553533054820403 41901761465330299582230605)
          ·
            refine ⟨15713160549498862343336477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41901761465330299582230605 15713160549498862343336477)
            ·
              refine ⟨5892435206062073378751179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15713160549498862343336477 5892435206062073378751179)
              ·
                refine ⟨8838652809093110068126769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892435206062073378751179 8838652809093110068126769)
                ·
                  refine ⟨6628989606819832551095077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838652809093110068126769 6628989606819832551095077)
                  ·
                    refine ⟨1242935551278718603330327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6628989606819832551095077 1242935551278718603330327)
                    ·
                      rfl

theorem cell23_7261825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_7261825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261825 prefixEnd_7261825 := by exact prefixLift 7261825
  have htrace : WordTrace (prefixWord ++ tailWord_7261825) baseStart_7261825 baseEnd_7261825 := by
    simpa [prefixWord, tailWord_7261825, baseEnd_7261825] using wordTrace_append hprefix tailTrace_7261825
  have hstable : (prefixWord ++ tailWord_7261825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261825).length < 2 ^ (prefixWord ++ tailWord_7261825).sum := by decide
  have hdescent : baseEnd_7261825 < baseStart_7261825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261838 : List Nat := [4, 1, 1, 3, 1, 4, 2, 7]
def baseStart_7261838 : Nat := 118140960795 + 7261838 * 2 ^ 59
def prefixEnd_7261838 : Nat := 4983230072969 + 3 ^ 40 * 7261838 * 2
def baseEnd_7261838 : Nat := 138104197373506083671423

theorem tailTrace_7261838 : CollatzResearch.WordTrace tailWord_7261838 prefixEnd_7261838 138104197373506083671423 := by
  unfold tailWord_7261838
  simp only [CollatzResearch.WordTrace]
  refine ⟨33107623883201078004537271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176573994043739082690865445 33107623883201078004537271)
  ·
    refine ⟨49661435824801617006805907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33107623883201078004537271 49661435824801617006805907)
    ·
      refine ⟨74492153737202425510208861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49661435824801617006805907 74492153737202425510208861)
      ·
        refine ⟨27934557651450909566328323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74492153737202425510208861 27934557651450909566328323)
        ·
          refine ⟨41901836477176364349492485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27934557651450909566328323 41901836477176364349492485)
          ·
            refine ⟨7856594339470568315529841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41901836477176364349492485 7856594339470568315529841)
            ·
              refine ⟨5892445754602926236647381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7856594339470568315529841 5892445754602926236647381)
              ·
                refine ⟨138104197373506083671423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5892445754602926236647381 138104197373506083671423)
                ·
                  rfl

theorem cell23_7261838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_7261838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261838 prefixEnd_7261838 := by exact prefixLift 7261838
  have htrace : WordTrace (prefixWord ++ tailWord_7261838) baseStart_7261838 baseEnd_7261838 := by
    simpa [prefixWord, tailWord_7261838, baseEnd_7261838] using wordTrace_append hprefix tailTrace_7261838
  have hstable : (prefixWord ++ tailWord_7261838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261838).length < 2 ^ (prefixWord ++ tailWord_7261838).sum := by decide
  have hdescent : baseEnd_7261838 < baseStart_7261838 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261848 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3]
def baseStart_7261848 : Nat := 118140960795 + 7261848 * 2 ^ 59
def prefixEnd_7261848 : Nat := 4983230072969 + 3 ^ 40 * 7261848 * 2
def baseEnd_7261848 : Nat := 3728818463891209220003375

theorem tailTrace_7261848 : CollatzResearch.WordTrace tailWord_7261848 prefixEnd_7261848 3728818463891209220003375 := by
  unfold tailWord_7261848
  simp only [CollatzResearch.WordTrace]
  refine ⟨132430677897786197872081099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176574237197048263829441465 132430677897786197872081099)
  ·
    refine ⟨198646016846679296808121649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132430677897786197872081099 198646016846679296808121649)
    ·
      refine ⟨148984512635009472606091237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198646016846679296808121649 148984512635009472606091237)
      ·
        refine ⟨27934596119064276113642107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 148984512635009472606091237 27934596119064276113642107)
        ·
          refine ⟨41901894178596414170463161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27934596119064276113642107 41901894178596414170463161)
          ·
            refine ⟨31426420633947310627847371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41901894178596414170463161 31426420633947310627847371)
            ·
              refine ⟨47139630950920965941771057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31426420633947310627847371 47139630950920965941771057)
              ·
                refine ⟨35354723213190724456328293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47139630950920965941771057 35354723213190724456328293)
                ·
                  refine ⟨6629010602473260835561555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35354723213190724456328293 6629010602473260835561555)
                  ·
                    refine ⟨9943515903709891253342333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629010602473260835561555 9943515903709891253342333)
                    ·
                      refine ⟨3728818463891209220003375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943515903709891253342333 3728818463891209220003375)
                      ·
                        rfl

theorem cell23_7261848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_7261848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261848 prefixEnd_7261848 := by exact prefixLift 7261848
  have htrace : WordTrace (prefixWord ++ tailWord_7261848) baseStart_7261848 baseEnd_7261848 := by
    simpa [prefixWord, tailWord_7261848, baseEnd_7261848] using wordTrace_append hprefix tailTrace_7261848
  have hstable : (prefixWord ++ tailWord_7261848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261848).length < 2 ^ (prefixWord ++ tailWord_7261848).sum := by decide
  have hdescent : baseEnd_7261848 < baseStart_7261848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261882 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3]
def baseStart_7261882 : Nat := 118140960795 + 7261882 * 2 ^ 59
def prefixEnd_7261882 : Nat := 4983230072969 + 3 ^ 40 * 7261882 * 2
def baseEnd_7261882 : Nat := 3728835922233462086978219

theorem tailTrace_7261882 : CollatzResearch.WordTrace tailWord_7261882 prefixEnd_7261882 3728835922233462086978219 := by
  unfold tailWord_7261882
  simp only [CollatzResearch.WordTrace]
  refine ⟨66215648969362304887724975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176575063918299479700599933 66215648969362304887724975)
  ·
    refine ⟨99323473454043457331587463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66215648969362304887724975 99323473454043457331587463)
    ·
      refine ⟨148985210181065185997381195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99323473454043457331587463 148985210181065185997381195)
      ·
        refine ⟨223477815271597778996071793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148985210181065185997381195 223477815271597778996071793)
        ·
          refine ⟨167608361453698334247053845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223477815271597778996071793 167608361453698334247053845)
          ·
            refine ⟨7856641943142109417830649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 167608361453698334247053845 7856641943142109417830649)
            ·
              refine ⟨5892481457356582063372987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7856641943142109417830649 5892481457356582063372987)
              ·
                refine ⟨8838722186034873095059481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892481457356582063372987 8838722186034873095059481)
                ·
                  refine ⟨6629041639526154821294611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8838722186034873095059481 6629041639526154821294611)
                  ·
                    refine ⟨9943562459289232231941917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629041639526154821294611 9943562459289232231941917)
                    ·
                      refine ⟨3728835922233462086978219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943562459289232231941917 3728835922233462086978219)
                      ·
                        rfl

theorem cell23_7261882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 1, 3].length) (baseStart_7261882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261882 prefixEnd_7261882 := by exact prefixLift 7261882
  have htrace : WordTrace (prefixWord ++ tailWord_7261882) baseStart_7261882 baseEnd_7261882 := by
    simpa [prefixWord, tailWord_7261882, baseEnd_7261882] using wordTrace_append hprefix tailTrace_7261882
  have hstable : (prefixWord ++ tailWord_7261882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261882).length < 2 ^ (prefixWord ++ tailWord_7261882).sum := by decide
  have hdescent : baseEnd_7261882 < baseStart_7261882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261888 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2]
def baseStart_7261888 : Nat := 118140960795 + 7261888 * 2 ^ 59
def prefixEnd_7261888 : Nat := 4983230072969 + 3 ^ 40 * 7261888 * 2
def baseEnd_7261888 : Nat := 3728839003117389063503191

theorem tailTrace_7261888 : CollatzResearch.WordTrace tailWord_7261888 prefixEnd_7261888 3728839003117389063503191 := by
  unfold tailWord_7261888
  simp only [CollatzResearch.WordTrace]
  refine ⟨132431407357713741287809159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176575209810284988383745545 132431407357713741287809159)
  ·
    refine ⟨198647111036570611931713739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132431407357713741287809159 198647111036570611931713739)
    ·
      refine ⟨297970666554855917897570609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198647111036570611931713739 297970666554855917897570609)
      ·
        refine ⟨223477999916141938423177957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297970666554855917897570609 223477999916141938423177957)
        ·
          refine ⟨41902124984276613454345867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223477999916141938423177957 41902124984276613454345867)
          ·
            refine ⟨62853187476414920181518801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41902124984276613454345867 62853187476414920181518801)
            ·
              refine ⟨47139890607311190136139101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62853187476414920181518801 47139890607311190136139101)
              ·
                refine ⟨17677458977741696301052163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47139890607311190136139101 17677458977741696301052163)
                ·
                  refine ⟨26516188466612544451578245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17677458977741696301052163 26516188466612544451578245)
                  ·
                    refine ⟨4971785337489852084670921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26516188466612544451578245 4971785337489852084670921)
                    ·
                      refine ⟨3728839003117389063503191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971785337489852084670921 3728839003117389063503191)
                      ·
                        rfl

theorem cell23_7261888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 1, 4, 2].length) (baseStart_7261888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261888 prefixEnd_7261888 := by exact prefixLift 7261888
  have htrace : WordTrace (prefixWord ++ tailWord_7261888) baseStart_7261888 baseEnd_7261888 := by
    simpa [prefixWord, tailWord_7261888, baseEnd_7261888] using wordTrace_append hprefix tailTrace_7261888
  have hstable : (prefixWord ++ tailWord_7261888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261888).length < 2 ^ (prefixWord ++ tailWord_7261888).sum := by decide
  have hdescent : baseEnd_7261888 < baseStart_7261888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261904 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_7261904 : Nat := 118140960795 + 7261904 * 2 ^ 59
def prefixEnd_7261904 : Nat := 4983230072969 + 3 ^ 40 * 7261904 * 2
def baseEnd_7261904 : Nat := 3728847218807861000903117

theorem tailTrace_7261904 : CollatzResearch.WordTrace tailWord_7261904 prefixEnd_7261904 3728847218807861000903117 := by
  unfold tailWord_7261904
  simp only [CollatzResearch.WordTrace]
  refine ⟨132431699141684758654100383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176575598855579678205467177 132431699141684758654100383)
  ·
    refine ⟨198647548712527137981150575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132431699141684758654100383 198647548712527137981150575)
    ·
      refine ⟨297971323068790706971725863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198647548712527137981150575 297971323068790706971725863)
      ·
        refine ⟨446956984603186060457588795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297971323068790706971725863 446956984603186060457588795)
        ·
          refine ⟨670435476904779090686383193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446956984603186060457588795 670435476904779090686383193)
          ·
            refine ⟨502826607678584318014787395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670435476904779090686383193 502826607678584318014787395)
            ·
              refine ⟨754239911517876477022181093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502826607678584318014787395 754239911517876477022181093)
              ·
                refine ⟨141419983409601839441658955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 754239911517876477022181093 141419983409601839441658955)
                ·
                  refine ⟨212129975114402759162488433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141419983409601839441658955 212129975114402759162488433)
                  ·
                    refine ⟨159097481335802069371866325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 212129975114402759162488433 159097481335802069371866325)
                    ·
                      refine ⟨3728847218807861000903117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159097481335802069371866325 3728847218807861000903117)
                      ·
                        rfl

theorem cell23_7261904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_7261904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261904 prefixEnd_7261904 := by exact prefixLift 7261904
  have htrace : WordTrace (prefixWord ++ tailWord_7261904) baseStart_7261904 baseEnd_7261904 := by
    simpa [prefixWord, tailWord_7261904, baseEnd_7261904] using wordTrace_append hprefix tailTrace_7261904
  have hstable : (prefixWord ++ tailWord_7261904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261904).length < 2 ^ (prefixWord ++ tailWord_7261904).sum := by decide
  have hdescent : baseEnd_7261904 < baseStart_7261904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261908 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7261908 : Nat := 118140960795 + 7261908 * 2 ^ 59
def prefixEnd_7261908 : Nat := 4983230072969 + 3 ^ 40 * 7261908 * 2
def baseEnd_7261908 : Nat := 3728849272730478985253099

theorem tailTrace_7261908 : CollatzResearch.WordTrace tailWord_7261908 prefixEnd_7261908 3728849272730478985253099 := by
  unfold tailWord_7261908
  simp only [CollatzResearch.WordTrace]
  refine ⟨132431772087677512995673189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176575696116903350660897585 132431772087677512995673189)
  ·
    refine ⟨24830957266439533686688723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 132431772087677512995673189 24830957266439533686688723)
    ·
      refine ⟨37246435899659300530033085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24830957266439533686688723 37246435899659300530033085)
      ·
        refine ⟨13967413462372237698762407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37246435899659300530033085 13967413462372237698762407)
        ·
          refine ⟨20951120193558356548143611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13967413462372237698762407 20951120193558356548143611)
          ·
            refine ⟨31426680290337534822215417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20951120193558356548143611 31426680290337534822215417)
            ·
              refine ⟨23570010217753151116661563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31426680290337534822215417 23570010217753151116661563)
              ·
                refine ⟨35355015326629726674992345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23570010217753151116661563 35355015326629726674992345)
                ·
                  refine ⟨26516261494972295006244259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35355015326629726674992345 26516261494972295006244259)
                  ·
                    refine ⟨39774392242458442509366389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26516261494972295006244259 39774392242458442509366389)
                    ·
                      refine ⟨3728849272730478985253099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39774392242458442509366389 3728849272730478985253099)
                      ·
                        rfl

theorem cell23_7261908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7261908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261908 prefixEnd_7261908 := by exact prefixLift 7261908
  have htrace : WordTrace (prefixWord ++ tailWord_7261908) baseStart_7261908 baseEnd_7261908 := by
    simpa [prefixWord, tailWord_7261908, baseEnd_7261908] using wordTrace_append hprefix tailTrace_7261908
  have hstable : (prefixWord ++ tailWord_7261908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261908).length < 2 ^ (prefixWord ++ tailWord_7261908).sum := by decide
  have hdescent : baseEnd_7261908 < baseStart_7261908 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261938 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_7261938 : Nat := 118140960795 + 7261938 * 2 ^ 59
def prefixEnd_7261938 : Nat := 4983230072969 + 3 ^ 40 * 7261938 * 2
def baseEnd_7261938 : Nat := 3728864677150113867877961

theorem tailTrace_7261938 : CollatzResearch.WordTrace tailWord_7261938 prefixEnd_7261938 3728864677150113867877961 := by
  unfold tailWord_7261938
  simp only [CollatzResearch.WordTrace]
  refine ⟨66216159591311585278734617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176576425576830894076625645 66216159591311585278734617)
  ·
    refine ⟨49662119693483688959050963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66216159591311585278734617 49662119693483688959050963)
    ·
      refine ⟨74493179540225533438576445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49662119693483688959050963 74493179540225533438576445)
      ·
        refine ⟨27934942327584575039466167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74493179540225533438576445 27934942327584575039466167)
        ·
          refine ⟨41902413491376862559199251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27934942327584575039466167 41902413491376862559199251)
          ·
            refine ⟨62853620237065293838798877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41902413491376862559199251 62853620237065293838798877)
            ·
              refine ⟨23570107588899485189549579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62853620237065293838798877 23570107588899485189549579)
              ·
                refine ⟨35355161383349227784324369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23570107588899485189549579 35355161383349227784324369)
                ·
                  refine ⟨26516371037511920838243277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35355161383349227784324369 26516371037511920838243277)
                  ·
                    refine ⟨9943639139066970314341229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26516371037511920838243277 9943639139066970314341229)
                    ·
                      refine ⟨3728864677150113867877961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943639139066970314341229 3728864677150113867877961)
                      ·
                        rfl

theorem cell23_7261938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_7261938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261938 prefixEnd_7261938 := by exact prefixLift 7261938
  have htrace : WordTrace (prefixWord ++ tailWord_7261938) baseStart_7261938 baseEnd_7261938 := by
    simpa [prefixWord, tailWord_7261938, baseEnd_7261938] using wordTrace_append hprefix tailTrace_7261938
  have hstable : (prefixWord ++ tailWord_7261938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261938).length < 2 ^ (prefixWord ++ tailWord_7261938).sum := by decide
  have hdescent : baseEnd_7261938 < baseStart_7261938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7261948 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_7261948 : Nat := 118140960795 + 7261948 * 2 ^ 59
def prefixEnd_7261948 : Nat := 4983230072969 + 3 ^ 40 * 7261948 * 2
def baseEnd_7261948 : Nat := 3728869811956658828752915

theorem tailTrace_7261948 : CollatzResearch.WordTrace tailWord_7261948 prefixEnd_7261948 3728869811956658828752915 := by
  unfold tailWord_7261948
  simp only [CollatzResearch.WordTrace]
  refine ⟨132432501547605056411401249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176576668730140075215201665 132432501547605056411401249)
  ·
    refine ⟨99324376160703792308550937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132432501547605056411401249 99324376160703792308550937)
    ·
      refine ⟨74493282120527844231413203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99324376160703792308550937 74493282120527844231413203)
      ·
        refine ⟨111739923180791766347119805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74493282120527844231413203 111739923180791766347119805)
        ·
          refine ⟨41902471192796912380169927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111739923180791766347119805 41902471192796912380169927)
          ·
            refine ⟨62853706789195368570254891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41902471192796912380169927 62853706789195368570254891)
            ·
              refine ⟨94280560183793052855382337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62853706789195368570254891 94280560183793052855382337)
              ·
                refine ⟨70710420137844789641536753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94280560183793052855382337 70710420137844789641536753)
                ·
                  refine ⟨53032815103383592231152565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70710420137844789641536753 53032815103383592231152565)
                  ·
                    refine ⟨4971826415942211771670553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53032815103383592231152565 4971826415942211771670553)
                    ·
                      refine ⟨3728869811956658828752915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971826415942211771670553 3728869811956658828752915)
                      ·
                        rfl

theorem cell23_7261948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_7261948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7261948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7261948 prefixEnd_7261948 := by exact prefixLift 7261948
  have htrace : WordTrace (prefixWord ++ tailWord_7261948) baseStart_7261948 baseEnd_7261948 := by
    simpa [prefixWord, tailWord_7261948, baseEnd_7261948] using wordTrace_append hprefix tailTrace_7261948
  have hstable : (prefixWord ++ tailWord_7261948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7261948).length < 2 ^ (prefixWord ++ tailWord_7261948).sum := by decide
  have hdescent : baseEnd_7261948 < baseStart_7261948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7261948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262039 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 1, 4]
def baseStart_7262039 : Nat := 118140960795 + 7262039 * 2 ^ 59
def prefixEnd_7262039 : Nat := 4983230072969 + 3 ^ 40 * 7262039 * 2
def baseEnd_7262039 : Nat := 1242972179565405990904999

theorem tailTrace_7262039 : CollatzResearch.WordTrace tailWord_7262039 prefixEnd_7262039 1242972179565405990904999 := by
  unfold tailWord_7262039
  simp only [CollatzResearch.WordTrace]
  refine ⟨264868322137880435364365171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176578881425253623576243447 264868322137880435364365171)
  ·
    refine ⟨397302483206820653046547757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264868322137880435364365171 397302483206820653046547757)
    ·
      refine ⟨148988431202557744892455409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397302483206820653046547757 148988431202557744892455409)
      ·
        refine ⟨111741323401918308669341557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148988431202557744892455409 111741323401918308669341557)
        ·
          refine ⟨10475749068929841437750771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111741323401918308669341557 10475749068929841437750771)
          ·
            refine ⟨15713623603394762156626157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10475749068929841437750771 15713623603394762156626157)
            ·
              refine ⟨5892608851273035808734809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15713623603394762156626157 5892608851273035808734809)
              ·
                refine ⟨4419456638454776856551107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5892608851273035808734809 4419456638454776856551107)
                ·
                  refine ⟨6629184957682165284826661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419456638454776856551107 6629184957682165284826661)
                  ·
                    refine ⟨1242972179565405990904999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629184957682165284826661 1242972179565405990904999)
                    ·
                      rfl

theorem cell23_7262039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 4].length) (baseStart_7262039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262039 prefixEnd_7262039 := by exact prefixLift 7262039
  have htrace : WordTrace (prefixWord ++ tailWord_7262039) baseStart_7262039 baseEnd_7262039 := by
    simpa [prefixWord, tailWord_7262039, baseEnd_7262039] using wordTrace_append hprefix tailTrace_7262039
  have hstable : (prefixWord ++ tailWord_7262039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262039).length < 2 ^ (prefixWord ++ tailWord_7262039).sum := by decide
  have hdescent : baseEnd_7262039 < baseStart_7262039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262052 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 6]
def baseStart_7262052 : Nat := 118140960795 + 7262052 * 2 ^ 59
def prefixEnd_7262052 : Nat := 4983230072969 + 3 ^ 40 * 7262052 * 2
def baseEnd_7262052 : Nat := 414324801549414046872493

theorem tailTrace_7262052 : CollatzResearch.WordTrace tailWord_7262052 prefixEnd_7262052 414324801549414046872493 := by
  unfold tailWord_7262052
  simp only [CollatzResearch.WordTrace]
  refine ⟨132434398143416669292294205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176579197524555559056392273 132434398143416669292294205)
  ·
    refine ⟨49662899303781250984610327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132434398143416669292294205 49662899303781250984610327)
    ·
      refine ⟨74494348955671876476915491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49662899303781250984610327 74494348955671876476915491)
      ·
        refine ⟨111741523433507814715373237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74494348955671876476915491 111741523433507814715373237)
        ·
          refine ⟨10475767821891357629566241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 111741523433507814715373237 10475767821891357629566241)
          ·
            refine ⟨7856825866418518222174681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10475767821891357629566241 7856825866418518222174681)
            ·
              refine ⟨5892619399813888666631011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7856825866418518222174681 5892619399813888666631011)
              ·
                refine ⟨8838929099720832999946517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5892619399813888666631011 8838929099720832999946517)
                ·
                  refine ⟨414324801549414046872493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8838929099720832999946517 414324801549414046872493)
                  ·
                    rfl

theorem cell23_7262052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_7262052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262052 prefixEnd_7262052 := by exact prefixLift 7262052
  have htrace : WordTrace (prefixWord ++ tailWord_7262052) baseStart_7262052 baseEnd_7262052 := by
    simpa [prefixWord, tailWord_7262052, baseEnd_7262052] using wordTrace_append hprefix tailTrace_7262052
  have hstable : (prefixWord ++ tailWord_7262052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262052).length < 2 ^ (prefixWord ++ tailWord_7262052).sum := by decide
  have hdescent : baseEnd_7262052 < baseStart_7262052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262055 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 4, 3, 2]
def baseStart_7262055 : Nat := 118140960795 + 7262055 * 2 ^ 59
def prefixEnd_7262055 : Nat := 4983230072969 + 3 ^ 40 * 7262055 * 2
def baseEnd_7262055 : Nat := 3728924754386689910114923

theorem tailTrace_7262055 : CollatzResearch.WordTrace tailWord_7262055 prefixEnd_7262055 3728924754386689910114923 := by
  unfold tailWord_7262055
  simp only [CollatzResearch.WordTrace]
  refine ⟨264868905705822470096947619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176579270470548313397965079 264868905705822470096947619)
  ·
    refine ⟨397303358558733705145421429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264868905705822470096947619 397303358558733705145421429)
    ·
      refine ⟨37247189864881284857383259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397303358558733705145421429 37247189864881284857383259)
      ·
        refine ⟨55870784797321927286074889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37247189864881284857383259 55870784797321927286074889)
        ·
          refine ⟨41903088597991445464556167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55870784797321927286074889 41903088597991445464556167)
          ·
            refine ⟨62854632896987168196834251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41903088597991445464556167 62854632896987168196834251)
            ·
              refine ⟨94281949345480752295251377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62854632896987168196834251 94281949345480752295251377)
              ·
                refine ⟨70711462009110564221438533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94281949345480752295251377 70711462009110564221438533)
                ·
                  refine ⟨13258399126708230791519725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70711462009110564221438533 13258399126708230791519725)
                  ·
                    refine ⟨4971899672515586546819897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13258399126708230791519725 4971899672515586546819897)
                    ·
                      refine ⟨3728924754386689910114923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971899672515586546819897 3728924754386689910114923)
                      ·
                        rfl

theorem cell23_7262055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 3, 2].length) (baseStart_7262055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262055 prefixEnd_7262055 := by exact prefixLift 7262055
  have htrace : WordTrace (prefixWord ++ tailWord_7262055) baseStart_7262055 baseEnd_7262055 := by
    simpa [prefixWord, tailWord_7262055, baseEnd_7262055] using wordTrace_append hprefix tailTrace_7262055
  have hstable : (prefixWord ++ tailWord_7262055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262055).length < 2 ^ (prefixWord ++ tailWord_7262055).sum := by decide
  have hdescent : baseEnd_7262055 < baseStart_7262055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262071 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_7262071 : Nat := 118140960795 + 7262071 * 2 ^ 59
def prefixEnd_7262071 : Nat := 4983230072969 + 3 ^ 40 * 7262071 * 2
def baseEnd_7262071 : Nat := 3728932970077161847514849

theorem tailTrace_7262071 : CollatzResearch.WordTrace tailWord_7262071 prefixEnd_7262071 3728932970077161847514849 := by
  unfold tailWord_7262071
  simp only [CollatzResearch.WordTrace]
  refine ⟨264869489273764504829530067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176579659515843003219686711 264869489273764504829530067)
  ·
    refine ⟨397304233910646757244295101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264869489273764504829530067 397304233910646757244295101)
    ·
      refine ⟨148989087716492533966610663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397304233910646757244295101 148989087716492533966610663)
      ·
        refine ⟨223483631574738800949915995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148989087716492533966610663 223483631574738800949915995)
        ·
          refine ⟨335225447362108201424873993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223483631574738800949915995 335225447362108201424873993)
          ·
            refine ⟨251419085521581151068655495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335225447362108201424873993 251419085521581151068655495)
            ·
              refine ⟨377128628282371726602983243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251419085521581151068655495 377128628282371726602983243)
              ·
                refine ⟨565692942423557589904474865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377128628282371726602983243 565692942423557589904474865)
                ·
                  refine ⟨424269706817668192428356149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 565692942423557589904474865 424269706817668192428356149)
                  ·
                    refine ⟨39775285014156393040158389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 424269706817668192428356149 39775285014156393040158389)
                    ·
                      refine ⟨3728932970077161847514849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39775285014156393040158389 3728932970077161847514849)
                      ·
                        rfl

theorem cell23_7262071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_7262071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262071 prefixEnd_7262071 := by exact prefixLift 7262071
  have htrace : WordTrace (prefixWord ++ tailWord_7262071) baseStart_7262071 baseEnd_7262071 := by
    simpa [prefixWord, tailWord_7262071, baseEnd_7262071] using wordTrace_append hprefix tailTrace_7262071
  have hstable : (prefixWord ++ tailWord_7262071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262071).length < 2 ^ (prefixWord ++ tailWord_7262071).sum := by decide
  have hdescent : baseEnd_7262071 < baseStart_7262071 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262119 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 3, 2, 2]
def baseStart_7262119 : Nat := 118140960795 + 7262119 * 2 ^ 59
def prefixEnd_7262119 : Nat := 4983230072969 + 3 ^ 40 * 7262119 * 2
def baseEnd_7262119 : Nat := 3728957617148577659714629

theorem tailTrace_7262119 : CollatzResearch.WordTrace tailWord_7262119 prefixEnd_7262119 3728957617148577659714629 := by
  unfold tailWord_7262119
  simp only [CollatzResearch.WordTrace]
  refine ⟨264871239977590609027277411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176580826651727072684851607 264871239977590609027277411)
  ·
    refine ⟨397306859966385913540916117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264871239977590609027277411 397306859966385913540916117)
    ·
      refine ⟨18623759060924339697230443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 397306859966385913540916117 18623759060924339697230443)
      ·
        refine ⟨27935638591386509545845665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18623759060924339697230443 27935638591386509545845665)
        ·
          refine ⟨20951728943539882159384249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27935638591386509545845665 20951728943539882159384249)
          ·
            refine ⟨15713796707654911619538187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20951728943539882159384249 15713796707654911619538187)
            ·
              refine ⟨23570695061482367429307281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15713796707654911619538187 23570695061482367429307281)
              ·
                refine ⟨17678021296111775571980461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23570695061482367429307281 17678021296111775571980461)
                ·
                  refine ⟨6629257986041915839492673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17678021296111775571980461 6629257986041915839492673)
                  ·
                    refine ⟨4971943489531436879619505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629257986041915839492673 4971943489531436879619505)
                    ·
                      refine ⟨3728957617148577659714629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971943489531436879619505 3728957617148577659714629)
                      ·
                        rfl

theorem cell23_7262119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_7262119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262119 prefixEnd_7262119 := by exact prefixLift 7262119
  have htrace : WordTrace (prefixWord ++ tailWord_7262119) baseStart_7262119 baseEnd_7262119 := by
    simpa [prefixWord, tailWord_7262119, baseEnd_7262119] using wordTrace_append hprefix tailTrace_7262119
  have hstable : (prefixWord ++ tailWord_7262119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262119).length < 2 ^ (prefixWord ++ tailWord_7262119).sum := by decide
  have hdescent : baseEnd_7262119 < baseStart_7262119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262135 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_7262135 : Nat := 118140960795 + 7262135 * 2 ^ 59
def prefixEnd_7262135 : Nat := 4983230072969 + 3 ^ 40 * 7262135 * 2
def baseEnd_7262135 : Nat := 3728965832839049597114555

theorem tailTrace_7262135 : CollatzResearch.WordTrace tailWord_7262135 prefixEnd_7262135 3728965832839049597114555 := by
  unfold tailWord_7262135
  simp only [CollatzResearch.WordTrace]
  refine ⟨264871823545532643759859859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176581215697021762506573239 264871823545532643759859859)
  ·
    refine ⟨397307735318298965639789789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264871823545532643759859859 397307735318298965639789789)
    ·
      refine ⟨148990400744362112114921171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397307735318298965639789789 148990400744362112114921171)
      ·
        refine ⟨223485601116543168172381757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148990400744362112114921171 223485601116543168172381757)
        ·
          refine ⟨83807100418703688064643159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223485601116543168172381757 83807100418703688064643159)
          ·
            refine ⟨125710650628055532096964739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83807100418703688064643159 125710650628055532096964739)
            ·
              refine ⟨188565975942083298145447109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125710650628055532096964739 188565975942083298145447109)
              ·
                refine ⟨35356120489140618402271333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 188565975942083298145447109 35356120489140618402271333)
                ·
                  refine ⟨6629272591713865950425875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35356120489140618402271333 6629272591713865950425875)
                  ·
                    refine ⟨9943908887570798925638813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629272591713865950425875 9943908887570798925638813)
                    ·
                      refine ⟨3728965832839049597114555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943908887570798925638813 3728965832839049597114555)
                      ·
                        rfl

theorem cell23_7262135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_7262135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262135 prefixEnd_7262135 := by exact prefixLift 7262135
  have htrace : WordTrace (prefixWord ++ tailWord_7262135) baseStart_7262135 baseEnd_7262135 := by
    simpa [prefixWord, tailWord_7262135, baseEnd_7262135] using wordTrace_append hprefix tailTrace_7262135
  have hstable : (prefixWord ++ tailWord_7262135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262135).length < 2 ^ (prefixWord ++ tailWord_7262135).sum := by decide
  have hdescent : baseEnd_7262135 < baseStart_7262135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262152 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3]
def baseStart_7262152 : Nat := 118140960795 + 7262152 * 2 ^ 59
def prefixEnd_7262152 : Nat := 4983230072969 + 3 ^ 40 * 7262152 * 2
def baseEnd_7262152 : Nat := 3728974562010176030601977

theorem tailTrace_7262152 : CollatzResearch.WordTrace tailWord_7262152 prefixEnd_7262152 3728974562010176030601977 := by
  unfold tailWord_7262152
  simp only [CollatzResearch.WordTrace]
  refine ⟨132436221793235527831614355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176581629057647370442152473 132436221793235527831614355)
  ·
    refine ⟨198654332689853291747421533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132436221793235527831614355 198654332689853291747421533)
    ·
      refine ⟨74495374758694984405283075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198654332689853291747421533 74495374758694984405283075)
      ·
        refine ⟨111743062138042476607924613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74495374758694984405283075 111743062138042476607924613)
        ·
          refine ⟨20951824150882964363985865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111743062138042476607924613 20951824150882964363985865)
          ·
            refine ⟨15713868113162223272989399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20951824150882964363985865 15713868113162223272989399)
            ·
              refine ⟨23570802169743334909484099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15713868113162223272989399 23570802169743334909484099)
              ·
                refine ⟨35356203254615002364226149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23570802169743334909484099 35356203254615002364226149)
                ·
                  refine ⟨6629288110240312943292403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35356203254615002364226149 6629288110240312943292403)
                  ·
                    refine ⟨9943932165360469414938605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629288110240312943292403 9943932165360469414938605)
                    ·
                      refine ⟨3728974562010176030601977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943932165360469414938605 3728974562010176030601977)
                      ·
                        rfl

theorem cell23_7262152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_7262152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262152 prefixEnd_7262152 := by exact prefixLift 7262152
  have htrace : WordTrace (prefixWord ++ tailWord_7262152) baseStart_7262152 baseEnd_7262152 := by
    simpa [prefixWord, tailWord_7262152, baseEnd_7262152] using wordTrace_append hprefix tailTrace_7262152
  have hstable : (prefixWord ++ tailWord_7262152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262152).length < 2 ^ (prefixWord ++ tailWord_7262152).sum := by decide
  have hdescent : baseEnd_7262152 < baseStart_7262152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262166 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_7262166 : Nat := 118140960795 + 7262166 * 2 ^ 59
def prefixEnd_7262166 : Nat := 4983230072969 + 3 ^ 40 * 7262166 * 2
def baseEnd_7262166 : Nat := 3728981750739338975826913

theorem tailTrace_7262166 : CollatzResearch.WordTrace tailWord_7262166 prefixEnd_7262166 3728981750739338975826913 := by
  unfold tailWord_7262166
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554559638026271003389897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176581969472280224036158901 16554559638026271003389897)
  ·
    refine ⟨12415919728519703252542423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16554559638026271003389897 12415919728519703252542423)
    ·
      refine ⟨18623879592779554878813635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12415919728519703252542423 18623879592779554878813635)
      ·
        refine ⟨27935819389169332318220453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18623879592779554878813635 27935819389169332318220453)
        ·
          refine ⟨5237966135469249809666335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27935819389169332318220453 5237966135469249809666335)
          ·
            refine ⟨7856949203203874714499503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237966135469249809666335 7856949203203874714499503)
            ·
              refine ⟨11785423804805812071749255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856949203203874714499503 11785423804805812071749255)
              ·
                refine ⟨17678135707208718107623883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11785423804805812071749255 17678135707208718107623883)
                ·
                  refine ⟨26517203560813077161435825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17678135707208718107623883 26517203560813077161435825)
                  ·
                    refine ⟨19887902670609807871076869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26517203560813077161435825 19887902670609807871076869)
                    ·
                      refine ⟨3728981750739338975826913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19887902670609807871076869 3728981750739338975826913)
                      ·
                        rfl

theorem cell23_7262166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_7262166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262166 prefixEnd_7262166 := by exact prefixLift 7262166
  have htrace : WordTrace (prefixWord ++ tailWord_7262166) baseStart_7262166 baseEnd_7262166 := by
    simpa [prefixWord, tailWord_7262166, baseEnd_7262166] using wordTrace_append hprefix tailTrace_7262166
  have hstable : (prefixWord ++ tailWord_7262166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262166).length < 2 ^ (prefixWord ++ tailWord_7262166).sum := by decide
  have hdescent : baseEnd_7262166 < baseStart_7262166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262168 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 2, 6]
def baseStart_7262168 : Nat := 118140960795 + 7262168 * 2 ^ 59
def prefixEnd_7262168 : Nat := 4983230072969 + 3 ^ 40 * 7262168 * 2
def baseEnd_7262168 : Nat := 1242994259233549322667301

theorem tailTrace_7262168 : CollatzResearch.WordTrace tailWord_7262168 prefixEnd_7262168 1242994259233549322667301 := by
  unfold tailWord_7262168
  simp only [CollatzResearch.WordTrace]
  refine ⟨132436513577206545197905579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176582018102942060263874105 132436513577206545197905579)
  ·
    refine ⟨198654770365809817796858369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132436513577206545197905579 198654770365809817796858369)
    ·
      refine ⟨148991077774357363347643777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198654770365809817796858369 148991077774357363347643777)
      ·
        refine ⟨111743308330768022510732833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148991077774357363347643777 111743308330768022510732833)
        ·
          refine ⟨83807481248076016883049625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111743308330768022510732833 83807481248076016883049625)
          ·
            refine ⟨62855610936057012662287219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83807481248076016883049625 62855610936057012662287219)
            ·
              refine ⟨94283416404085518993430829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62855610936057012662287219 94283416404085518993430829)
              ·
                refine ⟨35356281151532069622536561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94283416404085518993430829 35356281151532069622536561)
                ·
                  refine ⟨26517210863649052216902421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35356281151532069622536561 26517210863649052216902421)
                  ·
                    refine ⟨1242994259233549322667301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26517210863649052216902421 1242994259233549322667301)
                    ·
                      rfl

theorem cell23_7262168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_7262168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262168 prefixEnd_7262168 := by exact prefixLift 7262168
  have htrace : WordTrace (prefixWord ++ tailWord_7262168) baseStart_7262168 baseEnd_7262168 := by
    simpa [prefixWord, tailWord_7262168, baseEnd_7262168] using wordTrace_append hprefix tailTrace_7262168
  have hstable : (prefixWord ++ tailWord_7262168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262168).length < 2 ^ (prefixWord ++ tailWord_7262168).sum := by decide
  have hdescent : baseEnd_7262168 < baseStart_7262168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262169 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 1, 3, 3]
def baseStart_7262169 : Nat := 118140960795 + 7262169 * 2 ^ 59
def prefixEnd_7262169 : Nat := 4983230072969 + 3 ^ 40 * 7262169 * 2
def baseEnd_7262169 : Nat := 3728983291181302464089399

theorem tailTrace_7262169 : CollatzResearch.WordTrace tailWord_7262169 prefixEnd_7262169 3728983291181302464089399 := by
  unfold tailWord_7262169
  simp only [CollatzResearch.WordTrace]
  refine ⟨264873063627409467566597561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176582042418272978377731707 264873063627409467566597561)
  ·
    refine ⟨198654797720557100674948171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264873063627409467566597561 198654797720557100674948171)
    ·
      refine ⟨297982196580835651012422257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198654797720557100674948171 297982196580835651012422257)
      ·
        refine ⟨223486647435626738259316693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 297982196580835651012422257 223486647435626738259316693)
        ·
          refine ⟨5237968299272501677952735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 223486647435626738259316693 5237968299272501677952735)
          ·
            refine ⟨7856952448908752516929103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237968299272501677952735 7856952448908752516929103)
            ·
              refine ⟨11785428673363128775393655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856952448908752516929103 11785428673363128775393655)
              ·
                refine ⟨17678143010044693163090483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11785428673363128775393655 17678143010044693163090483)
                ·
                  refine ⟨26517214515067039744635725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17678143010044693163090483 26517214515067039744635725)
                  ·
                    refine ⟨9943955443150139904238397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26517214515067039744635725 9943955443150139904238397)
                    ·
                      refine ⟨3728983291181302464089399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9943955443150139904238397 3728983291181302464089399)
                      ·
                        rfl

theorem cell23_7262169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 3, 3].length) (baseStart_7262169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262169 prefixEnd_7262169 := by exact prefixLift 7262169
  have htrace : WordTrace (prefixWord ++ tailWord_7262169) baseStart_7262169 baseEnd_7262169 := by
    simpa [prefixWord, tailWord_7262169, baseEnd_7262169] using wordTrace_append hprefix tailTrace_7262169
  have hstable : (prefixWord ++ tailWord_7262169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262169).length < 2 ^ (prefixWord ++ tailWord_7262169).sum := by decide
  have hdescent : baseEnd_7262169 < baseStart_7262169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262179 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 1, 3, 2]
def baseStart_7262179 : Nat := 118140960795 + 7262179 * 2 ^ 59
def prefixEnd_7262179 : Nat := 4983230072969 + 3 ^ 40 * 7262179 * 2
def baseEnd_7262179 : Nat := 3728988425987847424964353

theorem tailTrace_7262179 : CollatzResearch.WordTrace tailWord_7262179 prefixEnd_7262179 3728988425987847424964353 := by
  unfold tailWord_7262179
  simp only [CollatzResearch.WordTrace]
  refine ⟨264873428357373239274461591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176582285571582159516307727 264873428357373239274461591)
  ·
    refine ⟨397310142536059858911692387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264873428357373239274461591 397310142536059858911692387)
    ·
      refine ⟨595965213804089788367538581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397310142536059858911692387 595965213804089788367538581)
      ·
        refine ⟨27935869397066708829728371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 595965213804089788367538581 27935869397066708829728371)
        ·
          refine ⟨41903804095600063244592557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27935869397066708829728371 41903804095600063244592557)
          ·
            refine ⟨15713926535850023716722209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41903804095600063244592557 15713926535850023716722209)
            ·
              refine ⟨11785444901887517787541657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15713926535850023716722209 11785444901887517787541657)
              ·
                refine ⟨8839083676415638340656243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785444901887517787541657 8839083676415638340656243)
                ·
                  refine ⟨13258625514623457510984365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8839083676415638340656243 13258625514623457510984365)
                  ·
                    refine ⟨4971984567983796566619137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13258625514623457510984365 4971984567983796566619137)
                    ·
                      refine ⟨3728988425987847424964353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971984567983796566619137 3728988425987847424964353)
                      ·
                        rfl

theorem cell23_7262179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_7262179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262179 prefixEnd_7262179 := by exact prefixLift 7262179
  have htrace : WordTrace (prefixWord ++ tailWord_7262179) baseStart_7262179 baseEnd_7262179 := by
    simpa [prefixWord, tailWord_7262179, baseEnd_7262179] using wordTrace_append hprefix tailTrace_7262179
  have hstable : (prefixWord ++ tailWord_7262179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262179).length < 2 ^ (prefixWord ++ tailWord_7262179).sum := by decide
  have hdescent : baseEnd_7262179 < baseStart_7262179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262188 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_7262188 : Nat := 118140960795 + 7262188 * 2 ^ 59
def prefixEnd_7262188 : Nat := 4983230072969 + 3 ^ 40 * 7262188 * 2
def baseEnd_7262188 : Nat := 3728993047313737889751811

theorem tailTrace_7262188 : CollatzResearch.WordTrace tailWord_7262188 prefixEnd_7262188 3728993047313737889751811 := by
  unfold tailWord_7262188
  simp only [CollatzResearch.WordTrace]
  refine ⟨132436878307170316905769609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176582504409560422541026145 132436878307170316905769609)
  ·
    refine ⟨99327658730377737679327207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132436878307170316905769609 99327658730377737679327207)
    ·
      refine ⟨148991488095566606518990811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99327658730377737679327207 148991488095566606518990811)
      ·
        refine ⟨223487232143349909778486217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148991488095566606518990811 223487232143349909778486217)
        ·
          refine ⟨167615424107512432333864663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223487232143349909778486217 167615424107512432333864663)
          ·
            refine ⟨251423136161268648500796995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167615424107512432333864663 251423136161268648500796995)
            ·
              refine ⟨377134704241902972751195493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251423136161268648500796995 377134704241902972751195493)
              ·
                refine ⟨70712757045356807390849155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377134704241902972751195493 70712757045356807390849155)
                ·
                  refine ⟨106069135568035211086273733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70712757045356807390849155 106069135568035211086273733)
                  ·
                    refine ⟨19887962919006602078676325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106069135568035211086273733 19887962919006602078676325)
                    ·
                      refine ⟨3728993047313737889751811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19887962919006602078676325 3728993047313737889751811)
                      ·
                        rfl

theorem cell23_7262188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_7262188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262188 prefixEnd_7262188 := by exact prefixLift 7262188
  have htrace : WordTrace (prefixWord ++ tailWord_7262188) baseStart_7262188 baseEnd_7262188 := by
    simpa [prefixWord, tailWord_7262188, baseEnd_7262188] using wordTrace_append hprefix tailTrace_7262188
  have hstable : (prefixWord ++ tailWord_7262188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262188).length < 2 ^ (prefixWord ++ tailWord_7262188).sum := by decide
  have hdescent : baseEnd_7262188 < baseStart_7262188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262192 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2]
def baseStart_7262192 : Nat := 118140960795 + 7262192 * 2 ^ 59
def prefixEnd_7262192 : Nat := 4983230072969 + 3 ^ 40 * 7262192 * 2
def baseEnd_7262192 : Nat := 3728995101236355874101793

theorem tailTrace_7262192 : CollatzResearch.WordTrace tailWord_7262192 prefixEnd_7262192 3728995101236355874101793 := by
  unfold tailWord_7262192
  simp only [CollatzResearch.WordTrace]
  refine ⟨132436951253163071247342415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176582601670884094996456553 132436951253163071247342415)
  ·
    refine ⟨198655426879744606871013623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132436951253163071247342415 198655426879744606871013623)
    ·
      refine ⟨297983140319616910306520435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198655426879744606871013623 297983140319616910306520435)
      ·
        refine ⟨446974710479425365459780653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297983140319616910306520435 446974710479425365459780653)
        ·
          refine ⟨167615516429784512047417745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 446974710479425365459780653 167615516429784512047417745)
          ·
            refine ⟨125711637322338384035563309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167615516429784512047417745 125711637322338384035563309)
            ·
              refine ⟨47141863995876894013336241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125711637322338384035563309 47141863995876894013336241)
              ·
                refine ⟨35356397996907670510002181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47141863995876894013336241 35356397996907670510002181)
                ·
                  refine ⟨6629324624420188220625409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35356397996907670510002181 6629324624420188220625409)
                  ·
                    refine ⟨4971993468315141165469057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629324624420188220625409 4971993468315141165469057)
                    ·
                      refine ⟨3728995101236355874101793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4971993468315141165469057 3728995101236355874101793)
                      ·
                        rfl

theorem cell23_7262192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 4, 2, 2].length) (baseStart_7262192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262192 prefixEnd_7262192 := by exact prefixLift 7262192
  have htrace : WordTrace (prefixWord ++ tailWord_7262192) baseStart_7262192 baseEnd_7262192 := by
    simpa [prefixWord, tailWord_7262192, baseEnd_7262192] using wordTrace_append hprefix tailTrace_7262192
  have hstable : (prefixWord ++ tailWord_7262192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262192).length < 2 ^ (prefixWord ++ tailWord_7262192).sum := by decide
  have hdescent : baseEnd_7262192 < baseStart_7262192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262209 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_7262209 : Nat := 118140960795 + 7262209 * 2 ^ 59
def prefixEnd_7262209 : Nat := 4983230072969 + 3 ^ 40 * 7262209 * 2
def baseEnd_7262209 : Nat := 3729003830407482307589215

theorem tailTrace_7262209 : CollatzResearch.WordTrace tailWord_7262209 prefixEnd_7262209 3729003830407482307589215 := by
  unfold tailWord_7262209
  simp only [CollatzResearch.WordTrace]
  refine ⟨264874522547264554398053681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176583015031509702932035787 264874522547264554398053681)
  ·
    refine ⟨198655891910448415798540261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264874522547264554398053681 198655891910448415798540261)
    ·
      refine ⟨37247979733209077962226299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198655891910448415798540261 37247979733209077962226299)
      ·
        refine ⟨55871969599813616943339449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37247979733209077962226299 55871969599813616943339449)
        ·
          refine ⟨41903977199860212707504587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55871969599813616943339449 41903977199860212707504587)
          ·
            refine ⟨62855965799790319061256881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41903977199860212707504587 62855965799790319061256881)
            ·
              refine ⟨47141974349842739295942661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62855965799790319061256881 47141974349842739295942661)
              ·
                refine ⟨8839120190595513617989249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47141974349842739295942661 8839120190595513617989249)
                ·
                  refine ⟨6629340142946635213491937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8839120190595513617989249 6629340142946635213491937)
                  ·
                    refine ⟨4972005107209976410118953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629340142946635213491937 4972005107209976410118953)
                    ·
                      refine ⟨3729003830407482307589215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972005107209976410118953 3729003830407482307589215)
                      ·
                        rfl

theorem cell23_7262209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_7262209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262209 prefixEnd_7262209 := by exact prefixLift 7262209
  have htrace : WordTrace (prefixWord ++ tailWord_7262209) baseStart_7262209 baseEnd_7262209 := by
    simpa [prefixWord, tailWord_7262209, baseEnd_7262209] using wordTrace_append hprefix tailTrace_7262209
  have hstable : (prefixWord ++ tailWord_7262209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262209).length < 2 ^ (prefixWord ++ tailWord_7262209).sum := by decide
  have hdescent : baseEnd_7262209 < baseStart_7262209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262215 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 7]
def baseStart_7262215 : Nat := 118140960795 + 7262215 * 2 ^ 59
def prefixEnd_7262215 : Nat := 4983230072969 + 3 ^ 40 * 7262215 * 2
def baseEnd_7262215 : Nat := 414334101254601031568243

theorem tailTrace_7262215 : CollatzResearch.WordTrace tailWord_7262215 prefixEnd_7262215 414334101254601031568243 := by
  unfold tailWord_7262215
  simp only [CollatzResearch.WordTrace]
  refine ⟨264874741385242817422772099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176583160923495211615181399 264874741385242817422772099)
  ·
    refine ⟨397312112077864226134158149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264874741385242817422772099 397312112077864226134158149)
    ·
      refine ⟨74496021014599542400154653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397312112077864226134158149 74496021014599542400154653)
      ·
        refine ⟨27936007880474828400057995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74496021014599542400154653 27936007880474828400057995)
        ·
          refine ⟨41904011820712242600086993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27936007880474828400057995 41904011820712242600086993)
          ·
            refine ⟨31428008865534181950065245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41904011820712242600086993 31428008865534181950065245)
            ·
              refine ⟨11785503324575318231274467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31428008865534181950065245 11785503324575318231274467)
              ·
                refine ⟨17678254986862977346911701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11785503324575318231274467 17678254986862977346911701)
                ·
                  refine ⟨414334101254601031568243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17678254986862977346911701 414334101254601031568243)
                  ·
                    rfl

theorem cell23_7262215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 7].length) (baseStart_7262215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262215 prefixEnd_7262215 := by exact prefixLift 7262215
  have htrace : WordTrace (prefixWord ++ tailWord_7262215) baseStart_7262215 baseEnd_7262215 := by
    simpa [prefixWord, tailWord_7262215, baseEnd_7262215] using wordTrace_append hprefix tailTrace_7262215
  have hstable : (prefixWord ++ tailWord_7262215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262215).length < 2 ^ (prefixWord ++ tailWord_7262215).sum := by decide
  have hdescent : baseEnd_7262215 < baseStart_7262215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262235 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 5, 2]
def baseStart_7262235 : Nat := 118140960795 + 7262235 * 2 ^ 59
def prefixEnd_7262235 : Nat := 4983230072969 + 3 ^ 40 * 7262235 * 2
def baseEnd_7262235 : Nat := 3729017180904499205864095

theorem tailTrace_7262235 : CollatzResearch.WordTrace tailWord_7262235 prefixEnd_7262235 3729017180904499205864095 := by
  unfold tailWord_7262235
  simp only [CollatzResearch.WordTrace]
  refine ⟨264875470845170360838500159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176583647230113573892333439 264875470845170360838500159)
  ·
    refine ⟨397313206267755541257750239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264875470845170360838500159 397313206267755541257750239)
    ·
      refine ⟨595969809401633311886625359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397313206267755541257750239 595969809401633311886625359)
      ·
        refine ⟨893954714102449967829938039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595969809401633311886625359 893954714102449967829938039)
        ·
          refine ⟨1340932071153674951744907059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893954714102449967829938039 1340932071153674951744907059)
          ·
            refine ⟨2011398106730512427617360589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1340932071153674951744907059 2011398106730512427617360589)
            ·
              refine ⟨754274290023942160356510221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2011398106730512427617360589 754274290023942160356510221)
              ·
                refine ⟨282852858758978310133691333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 754274290023942160356510221 282852858758978310133691333)
                ·
                  refine ⟨53034911017308433150067125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 282852858758978310133691333 53034911017308433150067125)
                  ·
                    refine ⟨4972022907872665607818793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53034911017308433150067125 4972022907872665607818793)
                    ·
                      refine ⟨3729017180904499205864095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972022907872665607818793 3729017180904499205864095)
                      ·
                        rfl

theorem cell23_7262235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 5, 2].length) (baseStart_7262235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262235 prefixEnd_7262235 := by exact prefixLift 7262235
  have htrace : WordTrace (prefixWord ++ tailWord_7262235) baseStart_7262235 baseEnd_7262235 := by
    simpa [prefixWord, tailWord_7262235, baseEnd_7262235] using wordTrace_append hprefix tailTrace_7262235
  have hstable : (prefixWord ++ tailWord_7262235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262235).length < 2 ^ (prefixWord ++ tailWord_7262235).sum := by decide
  have hdescent : baseEnd_7262235 < baseStart_7262235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262245 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_7262245 : Nat := 118140960795 + 7262245 * 2 ^ 59
def prefixEnd_7262245 : Nat := 4983230072969 + 3 ^ 40 * 7262245 * 2
def baseEnd_7262245 : Nat := 1243007438570348055579683

theorem tailTrace_7262245 : CollatzResearch.WordTrace tailWord_7262245 prefixEnd_7262245 1243007438570348055579683 := by
  unfold tailWord_7262245
  simp only [CollatzResearch.WordTrace]
  refine ⟨264875835575134132546364189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176583890383422755030909459 264875835575134132546364189)
  ·
    refine ⟨99328438340675299704886571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264875835575134132546364189 99328438340675299704886571)
    ·
      refine ⟨148992657511012949557329857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99328438340675299704886571 148992657511012949557329857)
      ·
        refine ⟨111744493133259712167997393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148992657511012949557329857 111744493133259712167997393)
        ·
          refine ⟨83808369849944784125998045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111744493133259712167997393 83808369849944784125998045)
          ·
            refine ⟨31428138693729294047249267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83808369849944784125998045 31428138693729294047249267)
            ·
              refine ⟨47142208040593941070873901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31428138693729294047249267 47142208040593941070873901)
              ·
                refine ⟨17678328015222727901577713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47142208040593941070873901 17678328015222727901577713)
                ·
                  refine ⟨13258746011417045926183285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17678328015222727901577713 13258746011417045926183285)
                  ·
                    refine ⟨1243007438570348055579683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13258746011417045926183285 1243007438570348055579683)
                    ·
                      rfl

theorem cell23_7262245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_7262245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262245 prefixEnd_7262245 := by exact prefixLift 7262245
  have htrace : WordTrace (prefixWord ++ tailWord_7262245) baseStart_7262245 baseEnd_7262245 := by
    simpa [prefixWord, tailWord_7262245, baseEnd_7262245] using wordTrace_append hprefix tailTrace_7262245
  have hstable : (prefixWord ++ tailWord_7262245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262245).length < 2 ^ (prefixWord ++ tailWord_7262245).sum := by decide
  have hdescent : baseEnd_7262245 < baseStart_7262245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262262 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7262262 : Nat := 118140960795 + 7262262 * 2 ^ 59
def prefixEnd_7262262 : Nat := 4983230072969 + 3 ^ 40 * 7262262 * 2
def baseEnd_7262262 : Nat := 1243010348294056866742157

theorem tailTrace_7262262 : CollatzResearch.WordTrace tailWord_7262262 prefixEnd_7262262 1243010348294056866742157 := by
  unfold tailWord_7262262
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554778476004534028108315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176584303744048362966488693 16554778476004534028108315)
  ·
    refine ⟨24832167714006801042162473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16554778476004534028108315 24832167714006801042162473)
    ·
      refine ⟨18624125785505100781621855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24832167714006801042162473 18624125785505100781621855)
      ·
        refine ⟨27936188678257651172432783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18624125785505100781621855 27936188678257651172432783)
        ·
          refine ⟨41904283017386476758649175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27936188678257651172432783 41904283017386476758649175)
          ·
            refine ⟨62856424526079715137973763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41904283017386476758649175 62856424526079715137973763)
            ·
              refine ⟨94284636789119572706960645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62856424526079715137973763 94284636789119572706960645)
              ·
                refine ⟨17678369397959919882555121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94284636789119572706960645 17678369397959919882555121)
                ·
                  refine ⟨13258777048469939911916341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17678369397959919882555121 13258777048469939911916341)
                  ·
                    refine ⟨1243010348294056866742157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13258777048469939911916341 1243010348294056866742157)
                    ·
                      rfl

theorem cell23_7262262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7262262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262262 prefixEnd_7262262 := by exact prefixLift 7262262
  have htrace : WordTrace (prefixWord ++ tailWord_7262262) baseStart_7262262 baseEnd_7262262 := by
    simpa [prefixWord, tailWord_7262262, baseEnd_7262262] using wordTrace_append hprefix tailTrace_7262262
  have hstable : (prefixWord ++ tailWord_7262262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262262).length < 2 ^ (prefixWord ++ tailWord_7262262).sum := by decide
  have hdescent : baseEnd_7262262 < baseStart_7262262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262288 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 12]
def baseStart_7262288 : Nat := 118140960795 + 7262288 * 2 ^ 59
def prefixEnd_7262288 : Nat := 4983230072969 + 3 ^ 40 * 7262288 * 2
def baseEnd_7262288 : Nat := 414338266153243055389039

theorem tailTrace_7262288 : CollatzResearch.WordTrace tailWord_7262288 prefixEnd_7262288 414338266153243055389039 := by
  unfold tailWord_7262288
  simp only [CollatzResearch.WordTrace]
  refine ⟨132438701956989175445089759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176584935942652233926786345 132438701956989175445089759)
  ·
    refine ⟨198658052935483763167634639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132438701956989175445089759 198658052935483763167634639)
    ·
      refine ⟨297987079403225644751451959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198658052935483763167634639 297987079403225644751451959)
      ·
        refine ⟨446980619104838467127177939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297987079403225644751451959 446980619104838467127177939)
        ·
          refine ⟨670470928657257700690766909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446980619104838467127177939 670470928657257700690766909)
          ·
            refine ⟨251426598246471637759037591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670470928657257700690766909 251426598246471637759037591)
            ·
              refine ⟨377139897369707456638556387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251426598246471637759037591 377139897369707456638556387)
              ·
                refine ⟨565709846054561184957834581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 377139897369707456638556387 565709846054561184957834581)
                ·
                  refine ⟨414338266153243055389039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 565709846054561184957834581 414338266153243055389039)
                  ·
                    rfl

theorem cell23_7262288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 12].length) (baseStart_7262288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262288 prefixEnd_7262288 := by exact prefixLift 7262288
  have htrace : WordTrace (prefixWord ++ tailWord_7262288) baseStart_7262288 baseEnd_7262288 := by
    simpa [prefixWord, tailWord_7262288, baseEnd_7262288] using wordTrace_append hprefix tailTrace_7262288
  have hstable : (prefixWord ++ tailWord_7262288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262288).length < 2 ^ (prefixWord ++ tailWord_7262288).sum := by decide
  have hdescent : baseEnd_7262288 < baseStart_7262288 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262309 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_7262309 : Nat := 118140960795 + 7262309 * 2 ^ 59
def prefixEnd_7262309 : Nat := 4983230072969 + 3 ^ 40 * 7262309 * 2
def baseEnd_7262309 : Nat := 1243018392824310638779585

theorem tailTrace_7262309 : CollatzResearch.WordTrace tailWord_7262309 prefixEnd_7262309 1243018392824310638779585 := by
  unfold tailWord_7262309
  simp only [CollatzResearch.WordTrace]
  refine ⟨264878169846902271476693981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176585446564601514317795987 264878169846902271476693981)
  ·
    refine ⟨99329313692588351803760243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264878169846902271476693981 99329313692588351803760243)
    ·
      refine ⟨148993970538882527705640365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99329313692588351803760243 148993970538882527705640365)
      ·
        refine ⟨55872738952080947889615137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148993970538882527705640365 55872738952080947889615137)
        ·
          refine ⟨41904554214060710917211353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55872738952080947889615137 41904554214060710917211353)
          ·
            refine ⟨31428415660545533187908515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41904554214060710917211353 31428415660545533187908515)
            ·
              refine ⟨47142623490818299781862773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31428415660545533187908515 47142623490818299781862773)
              ·
                refine ⟨4419620952264215604549635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47142623490818299781862773 4419620952264215604549635)
                ·
                  refine ⟨6629431428396323406824453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419620952264215604549635 6629431428396323406824453)
                  ·
                    refine ⟨1243018392824310638779585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629431428396323406824453 1243018392824310638779585)
                    ·
                      rfl

theorem cell23_7262309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_7262309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262309 prefixEnd_7262309 := by exact prefixLift 7262309
  have htrace : WordTrace (prefixWord ++ tailWord_7262309) baseStart_7262309 baseEnd_7262309 := by
    simpa [prefixWord, tailWord_7262309, baseEnd_7262309] using wordTrace_append hprefix tailTrace_7262309
  have hstable : (prefixWord ++ tailWord_7262309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262309).length < 2 ^ (prefixWord ++ tailWord_7262309).sum := by decide
  have hdescent : baseEnd_7262309 < baseStart_7262309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262322 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_7262322 : Nat := 118140960795 + 7262322 * 2 ^ 59
def prefixEnd_7262322 : Nat := 4983230072969 + 3 ^ 40 * 7262322 * 2
def baseEnd_7262322 : Nat := 414340205969048929497355

theorem tailTrace_7262322 : CollatzResearch.WordTrace tailWord_7262322 prefixEnd_7262322 414340205969048929497355 := by
  unfold tailWord_7262322
  simp only [CollatzResearch.WordTrace]
  refine ⟨66219660998963793674229305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176585762663903449797944813 66219660998963793674229305)
  ·
    refine ⟨49664745749222845255671979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66219660998963793674229305 49664745749222845255671979)
    ·
      refine ⟨74497118623834267883507969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49664745749222845255671979 74497118623834267883507969)
      ·
        refine ⟨55872838967875700912630977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74497118623834267883507969 55872838967875700912630977)
        ·
          refine ⟨41904629225906775684473233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55872838967875700912630977 41904629225906775684473233)
          ·
            refine ⟨31428471919430081763354925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41904629225906775684473233 31428471919430081763354925)
            ·
              refine ⟨11785676969786280661258097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31428471919430081763354925 11785676969786280661258097)
              ·
                refine ⟨8839257727339710495943573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785676969786280661258097 8839257727339710495943573)
                ·
                  refine ⟨414340205969048929497355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8839257727339710495943573 414340205969048929497355)
                  ·
                    rfl

theorem cell23_7262322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_7262322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262322 prefixEnd_7262322 := by exact prefixLift 7262322
  have htrace : WordTrace (prefixWord ++ tailWord_7262322) baseStart_7262322 baseEnd_7262322 := by
    simpa [prefixWord, tailWord_7262322, baseEnd_7262322] using wordTrace_append hprefix tailTrace_7262322
  have hstable : (prefixWord ++ tailWord_7262322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262322).length < 2 ^ (prefixWord ++ tailWord_7262322).sum := by decide
  have hdescent : baseEnd_7262322 < baseStart_7262322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262326 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 1, 4]
def baseStart_7262326 : Nat := 118140960795 + 7262326 * 2 ^ 59
def prefixEnd_7262326 : Nat := 4983230072969 + 3 ^ 40 * 7262326 * 2
def baseEnd_7262326 : Nat := 1243021302548019449942059

theorem tailTrace_7262326 : CollatzResearch.WordTrace tailWord_7262326 prefixEnd_7262326 1243021302548019449942059 := by
  unfold tailWord_7262326
  simp only [CollatzResearch.WordTrace]
  refine ⟨16554924367990042711253927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176585859925227122253375221 16554924367990042711253927)
  ·
    refine ⟨24832386551985064066880891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16554924367990042711253927 24832386551985064066880891)
    ·
      refine ⟨37248579827977596100321337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24832386551985064066880891 37248579827977596100321337)
      ·
        refine ⟨27936434870983197075241003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37248579827977596100321337 27936434870983197075241003)
        ·
          refine ⟨41904652306474795612861505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27936434870983197075241003 41904652306474795612861505)
          ·
            refine ⟨31428489229856096709646129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41904652306474795612861505 31428489229856096709646129)
            ·
              refine ⟨23571366922392072532234597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31428489229856096709646129 23571366922392072532234597)
              ·
                refine ⟨4419631297948513599793987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23571366922392072532234597 4419631297948513599793987)
                ·
                  refine ⟨6629446946922770399690981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419631297948513599793987 6629446946922770399690981)
                  ·
                    refine ⟨1243021302548019449942059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6629446946922770399690981 1243021302548019449942059)
                    ·
                      rfl

theorem cell23_7262326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_7262326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262326 prefixEnd_7262326 := by exact prefixLift 7262326
  have htrace : WordTrace (prefixWord ++ tailWord_7262326) baseStart_7262326 baseEnd_7262326 := by
    simpa [prefixWord, tailWord_7262326, baseEnd_7262326] using wordTrace_append hprefix tailTrace_7262326
  have hstable : (prefixWord ++ tailWord_7262326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262326).length < 2 ^ (prefixWord ++ tailWord_7262326).sum := by decide
  have hdescent : baseEnd_7262326 < baseStart_7262326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262352 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 1, 5]
def baseStart_7262352 : Nat := 118140960795 + 7262352 * 2 ^ 59
def prefixEnd_7262352 : Nat := 4983230072969 + 3 ^ 40 * 7262352 * 2
def baseEnd_7262352 : Nat := 1243025752713691749367019

theorem tailTrace_7262352 : CollatzResearch.WordTrace tailWord_7262352 prefixEnd_7262352 1243025752713691749367019 := by
  unfold tailWord_7262352
  simp only [CollatzResearch.WordTrace]
  refine ⟨132439869092873244910254655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176586492123830993213672873 132439869092873244910254655)
  ·
    refine ⟨198659803639309867365381983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132439869092873244910254655 198659803639309867365381983)
    ·
      refine ⟨297989705458964801048072975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198659803639309867365381983 297989705458964801048072975)
      ·
        refine ⟨446984558188447201572109463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297989705458964801048072975 446984558188447201572109463)
        ·
          refine ⟨670476837282670802358164195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446984558188447201572109463 670476837282670802358164195)
          ·
            refine ⟨1005715255924006203537246293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 670476837282670802358164195 1005715255924006203537246293)
            ·
              refine ⟨11785725655359447697702105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1005715255924006203537246293 11785725655359447697702105)
              ·
                refine ⟨8839294241519585773276579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785725655359447697702105 8839294241519585773276579)
                ·
                  refine ⟨13258941362279378659914869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8839294241519585773276579 13258941362279378659914869)
                  ·
                    refine ⟨1243025752713691749367019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13258941362279378659914869 1243025752713691749367019)
                    ·
                      rfl

theorem cell23_7262352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 5].length) (baseStart_7262352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262352 prefixEnd_7262352 := by exact prefixLift 7262352
  have htrace : WordTrace (prefixWord ++ tailWord_7262352) baseStart_7262352 baseEnd_7262352 := by
    simpa [prefixWord, tailWord_7262352, baseEnd_7262352] using wordTrace_append hprefix tailTrace_7262352
  have hstable : (prefixWord ++ tailWord_7262352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262352).length < 2 ^ (prefixWord ++ tailWord_7262352).sum := by decide
  have hdescent : baseEnd_7262352 < baseStart_7262352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262392 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3]
def baseStart_7262392 : Nat := 118140960795 + 7262392 * 2 ^ 59
def prefixEnd_7262392 : Nat := 4983230072969 + 3 ^ 40 * 7262392 * 2
def baseEnd_7262392 : Nat := 3729097797367255091600873

theorem tailTrace_7262392 : CollatzResearch.WordTrace tailWord_7262392 prefixEnd_7262392 3729097797367255091600873 := by
  unfold tailWord_7262392
  simp only [CollatzResearch.WordTrace]
  refine ⟨132440598552800788325982715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176587464737067717767976953 132440598552800788325982715)
  ·
    refine ⟨198660897829201182488974073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132440598552800788325982715 198660897829201182488974073)
    ·
      refine ⟨148995673371900886866730555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198660897829201182488974073 148995673371900886866730555)
      ·
        refine ⟨223493510057851330300095833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 148995673371900886866730555 223493510057851330300095833)
        ·
          refine ⟨167620132543388497725071875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223493510057851330300095833 167620132543388497725071875)
          ·
            refine ⟨251430198815082746587607813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167620132543388497725071875 251430198815082746587607813)
            ·
              refine ⟨47143162277828014985176465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251430198815082746587607813 47143162277828014985176465)
              ·
                refine ⟨35357371708371011238882349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47143162277828014985176465 35357371708371011238882349)
                ·
                  refine ⟨13259014390639129214580881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35357371708371011238882349 13259014390639129214580881)
                  ·
                    refine ⟨9944260792979346910935661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13259014390639129214580881 9944260792979346910935661)
                    ·
                      refine ⟨3729097797367255091600873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9944260792979346910935661 3729097797367255091600873)
                      ·
                        rfl

theorem cell23_7262392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_7262392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262392 prefixEnd_7262392 := by exact prefixLift 7262392
  have htrace : WordTrace (prefixWord ++ tailWord_7262392) baseStart_7262392 baseEnd_7262392 := by
    simpa [prefixWord, tailWord_7262392, baseEnd_7262392] using wordTrace_append hprefix tailTrace_7262392
  have hstable : (prefixWord ++ tailWord_7262392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262392).length < 2 ^ (prefixWord ++ tailWord_7262392).sum := by decide
  have hdescent : baseEnd_7262392 < baseStart_7262392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262395 : List Nat := [1, 1, 1, 1, 1, 2, 8, 8]
def baseStart_7262395 : Nat := 118140960795 + 7262395 * 2 ^ 59
def prefixEnd_7262395 : Nat := 4983230072969 + 3 ^ 40 * 7262395 * 2
def baseEnd_7262395 : Nat := 138114790289230317772717

theorem tailTrace_7262395 : CollatzResearch.WordTrace tailWord_7262395 prefixEnd_7262395 138114790289230317772717 := by
  unfold tailWord_7262395
  simp only [CollatzResearch.WordTrace]
  refine ⟨264881306524590708164324639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176587537683060472109549759 264881306524590708164324639)
  ·
    refine ⟨397321959786886062246486959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264881306524590708164324639 397321959786886062246486959)
    ·
      refine ⟨595982939680329093369730439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397321959786886062246486959 595982939680329093369730439)
      ·
        refine ⟨893974409520493640054595659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 595982939680329093369730439 893974409520493640054595659)
        ·
          refine ⟨1340961614280740460081893489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 893974409520493640054595659 1340961614280740460081893489)
          ·
            refine ⟨1005721210710555345061420117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1340961614280740460081893489 1005721210710555345061420117)
            ·
              refine ⟨11785795438014320449938517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1005721210710555345061420117 11785795438014320449938517)
              ·
                refine ⟨138114790289230317772717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11785795438014320449938517 138114790289230317772717)
                ·
                  rfl

theorem cell23_7262395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 8].length) (baseStart_7262395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262395 prefixEnd_7262395 := by exact prefixLift 7262395
  have htrace : WordTrace (prefixWord ++ tailWord_7262395) baseStart_7262395 baseEnd_7262395 := by
    simpa [prefixWord, tailWord_7262395, baseEnd_7262395] using wordTrace_append hprefix tailTrace_7262395
  have hstable : (prefixWord ++ tailWord_7262395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262395).length < 2 ^ (prefixWord ++ tailWord_7262395).sum := by decide
  have hdescent : baseEnd_7262395 < baseStart_7262395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262440 : List Nat := [2, 1, 4, 1, 2, 2, 4, 2, 1, 2, 2]
def baseStart_7262440 : Nat := 118140960795 + 7262440 * 2 ^ 59
def prefixEnd_7262440 : Nat := 4983230072969 + 3 ^ 40 * 7262440 * 2
def baseEnd_7262440 : Nat := 3729122444438670903800653

theorem tailTrace_7262440 : CollatzResearch.WordTrace tailWord_7262440 prefixEnd_7262440 3729122444438670903800653 := by
  unfold tailWord_7262440
  simp only [CollatzResearch.WordTrace]
  refine ⟨132441473904713840424856387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176588631872951787233141849 132441473904713840424856387)
  ·
    refine ⟨198662210857070760637284581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132441473904713840424856387 198662210857070760637284581)
    ·
      refine ⟨37249164535700767619490859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198662210857070760637284581 37249164535700767619490859)
      ·
        refine ⟨55873746803551151429236289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37249164535700767619490859 55873746803551151429236289)
        ·
          refine ⟨41905310102663363571927217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55873746803551151429236289 41905310102663363571927217)
          ·
            refine ⟨31428982576997522678945413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41905310102663363571927217 31428982576997522678945413)
            ·
              refine ⟨5892934233187035502302265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31428982576997522678945413 5892934233187035502302265)
              ·
                refine ⟨4419700674890276626726699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5892934233187035502302265 4419700674890276626726699)
                ·
                  refine ⟨6629551012335414940090049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4419700674890276626726699 6629551012335414940090049)
                  ·
                    refine ⟨4972163259251561205067537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629551012335414940090049 4972163259251561205067537)
                    ·
                      refine ⟨3729122444438670903800653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972163259251561205067537 3729122444438670903800653)
                      ·
                        rfl

theorem cell23_7262440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_7262440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262440 prefixEnd_7262440 := by exact prefixLift 7262440
  have htrace : WordTrace (prefixWord ++ tailWord_7262440) baseStart_7262440 baseEnd_7262440 := by
    simpa [prefixWord, tailWord_7262440, baseEnd_7262440] using wordTrace_append hprefix tailTrace_7262440
  have hstable : (prefixWord ++ tailWord_7262440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262440).length < 2 ^ (prefixWord ++ tailWord_7262440).sum := by decide
  have hdescent : baseEnd_7262440 < baseStart_7262440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262449 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_7262449 : Nat := 118140960795 + 7262449 * 2 ^ 59
def prefixEnd_7262449 : Nat := 4983230072969 + 3 ^ 40 * 7262449 * 2
def baseEnd_7262449 : Nat := 3729127065764561368588111

theorem tailTrace_7262449 : CollatzResearch.WordTrace tailWord_7262449 prefixEnd_7262449 3729127065764561368588111 := by
  unfold tailWord_7262449
  simp only [CollatzResearch.WordTrace]
  refine ⟨264883276066395075386790401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176588850710930050257860267 264883276066395075386790401)
  ·
    refine ⟨198662457049796306540092801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264883276066395075386790401 198662457049796306540092801)
    ·
      refine ⟨148996842787347229905069601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198662457049796306540092801 148996842787347229905069601)
      ·
        refine ⟨111747632090510422428802201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148996842787347229905069601 111747632090510422428802201)
        ·
          refine ⟨83810724067882816821601651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111747632090510422428802201 83810724067882816821601651)
          ·
            refine ⟨125716086101824225232402477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83810724067882816821601651 125716086101824225232402477)
            ·
              refine ⟨47143532288184084462150929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 125716086101824225232402477 47143532288184084462150929)
              ·
                refine ⟨35357649216138063346613197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47143532288184084462150929 35357649216138063346613197)
                ·
                  refine ⟨13259118456051773754979949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35357649216138063346613197 13259118456051773754979949)
                  ·
                    refine ⟨4972169421019415158117481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13259118456051773754979949 4972169421019415158117481)
                    ·
                      refine ⟨3729127065764561368588111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972169421019415158117481 3729127065764561368588111)
                      ·
                        rfl

theorem cell23_7262449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_7262449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262449 prefixEnd_7262449 := by exact prefixLift 7262449
  have htrace : WordTrace (prefixWord ++ tailWord_7262449) baseStart_7262449 baseEnd_7262449 := by
    simpa [prefixWord, tailWord_7262449, baseEnd_7262449] using wordTrace_append hprefix tailTrace_7262449
  have hstable : (prefixWord ++ tailWord_7262449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262449).length < 2 ^ (prefixWord ++ tailWord_7262449).sum := by decide
  have hdescent : baseEnd_7262449 < baseStart_7262449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262490 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3]
def baseStart_7262490 : Nat := 118140960795 + 7262490 * 2 ^ 59
def prefixEnd_7262490 : Nat := 4983230072969 + 3 ^ 40 * 7262490 * 2
def baseEnd_7262490 : Nat := 3729148118471395708175423

theorem tailTrace_7262490 : CollatzResearch.WordTrace tailWord_7262490 prefixEnd_7262490 3729148118471395708175423 := by
  unfold tailWord_7262490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66221192864811634847258231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176589847639497692926021949 66221192864811634847258231)
  ·
    refine ⟨99331789297217452270887347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66221192864811634847258231 99331789297217452270887347)
    ·
      refine ⟨148997683945826178406331021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99331789297217452270887347 148997683945826178406331021)
      ·
        refine ⟨55874131479684816902374133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148997683945826178406331021 55874131479684816902374133)
        ·
          refine ⟨5238199826220451584597575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55874131479684816902374133 5238199826220451584597575)
          ·
            refine ⟨7857299739330677376896363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238199826220451584597575 7857299739330677376896363)
            ·
              refine ⟨11785949608996016065344545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857299739330677376896363 11785949608996016065344545)
              ·
                refine ⟨8839462206747012049008409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11785949608996016065344545 8839462206747012049008409)
                ·
                  refine ⟨6629596655060259036756307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8839462206747012049008409 6629596655060259036756307)
                  ·
                    refine ⟨9944394982590388555134461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629596655060259036756307 9944394982590388555134461)
                    ·
                      refine ⟨3729148118471395708175423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9944394982590388555134461 3729148118471395708175423)
                      ·
                        rfl

theorem cell23_7262490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_7262490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262490 prefixEnd_7262490 := by exact prefixLift 7262490
  have htrace : WordTrace (prefixWord ++ tailWord_7262490) baseStart_7262490 baseEnd_7262490 := by
    simpa [prefixWord, tailWord_7262490, baseEnd_7262490] using wordTrace_append hprefix tailTrace_7262490
  have hstable : (prefixWord ++ tailWord_7262490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262490).length < 2 ^ (prefixWord ++ tailWord_7262490).sum := by decide
  have hdescent : baseEnd_7262490 < baseStart_7262490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262512 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3]
def baseStart_7262512 : Nat := 118140960795 + 7262512 * 2 ^ 59
def prefixEnd_7262512 : Nat := 4983230072969 + 3 ^ 40 * 7262512 * 2
def baseEnd_7262512 : Nat := 3729159415045794622100321

theorem tailTrace_7262512 : CollatzResearch.WordTrace tailWord_7262512 prefixEnd_7262512 3729159415045794622100321 := by
  unfold tailWord_7262512
  simp only [CollatzResearch.WordTrace]
  refine ⟨132442786932583418573166895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176590382576777891430889193 132442786932583418573166895)
  ·
    refine ⟨198664180398875127859750343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132442786932583418573166895 198664180398875127859750343)
    ·
      refine ⟨297996270598312691789625515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198664180398875127859750343 297996270598312691789625515)
      ·
        refine ⟨446994405897469037684438273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297996270598312691789625515 446994405897469037684438273)
        ·
          refine ⟨335245804423101778263328705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 446994405897469037684438273 335245804423101778263328705)
          ·
            refine ⟨251434353317326333697496529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 335245804423101778263328705 251434353317326333697496529)
            ·
              refine ⟨188575764987994750273122397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251434353317326333697496529 188575764987994750273122397)
              ·
                refine ⟨70715911870498031352420899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188575764987994750273122397 70715911870498031352420899)
                ·
                  refine ⟨106073867805747047028631349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70715911870498031352420899 106073867805747047028631349)
                  ·
                    refine ⟨9944425106788785658934189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 106073867805747047028631349 9944425106788785658934189)
                    ·
                      refine ⟨3729159415045794622100321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9944425106788785658934189 3729159415045794622100321)
                      ·
                        rfl

theorem cell23_7262512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 3].length) (baseStart_7262512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262512 prefixEnd_7262512 := by exact prefixLift 7262512
  have htrace : WordTrace (prefixWord ++ tailWord_7262512) baseStart_7262512 baseEnd_7262512 := by
    simpa [prefixWord, tailWord_7262512, baseEnd_7262512] using wordTrace_append hprefix tailTrace_7262512
  have hstable : (prefixWord ++ tailWord_7262512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262512).length < 2 ^ (prefixWord ++ tailWord_7262512).sum := by decide
  have hdescent : baseEnd_7262512 < baseStart_7262512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262513 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_7262513 : Nat := 118140960795 + 7262513 * 2 ^ 59
def prefixEnd_7262513 : Nat := 4983230072969 + 3 ^ 40 * 7262513 * 2
def baseEnd_7262513 : Nat := 3729159928526449118187817

theorem tailTrace_7262513 : CollatzResearch.WordTrace tailWord_7262513 prefixEnd_7262513 3729159928526449118187817 := by
  unfold tailWord_7262513
  simp only [CollatzResearch.WordTrace]
  refine ⟨264885610338163214317120193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176590406892108809544746795 264885610338163214317120193)
  ·
    refine ⟨198664207753622410737840145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264885610338163214317120193 198664207753622410737840145)
    ·
      refine ⟨148998155815216808053380109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198664207753622410737840145 148998155815216808053380109)
      ·
        refine ⟨55874308430706303020017541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 148998155815216808053380109 55874308430706303020017541)
        ·
          refine ⟨10476432830757431816253289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55874308430706303020017541 10476432830757431816253289)
          ·
            refine ⟨7857324623068073862189967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476432830757431816253289 7857324623068073862189967)
            ·
              refine ⟨11785986934602110793284951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857324623068073862189967 11785986934602110793284951)
              ·
                refine ⟨17678980401903166189927427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11785986934602110793284951 17678980401903166189927427)
                ·
                  refine ⟨26518470602854749284891141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17678980401903166189927427 26518470602854749284891141)
                  ·
                    refine ⟨4972213238035265490917089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26518470602854749284891141 4972213238035265490917089)
                    ·
                      refine ⟨3729159928526449118187817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972213238035265490917089 3729159928526449118187817)
                      ·
                        rfl

theorem cell23_7262513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_7262513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262513 prefixEnd_7262513 := by exact prefixLift 7262513
  have htrace : WordTrace (prefixWord ++ tailWord_7262513) baseStart_7262513 baseEnd_7262513 := by
    simpa [prefixWord, tailWord_7262513, baseEnd_7262513] using wordTrace_append hprefix tailTrace_7262513
  have hstable : (prefixWord ++ tailWord_7262513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262513).length < 2 ^ (prefixWord ++ tailWord_7262513).sum := by decide
  have hdescent : baseEnd_7262513 < baseStart_7262513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262552 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_7262552 : Nat := 118140960795 + 7262552 * 2 ^ 59
def prefixEnd_7262552 : Nat := 4983230072969 + 3 ^ 40 * 7262552 * 2
def baseEnd_7262552 : Nat := 3729179954271974465600137

theorem tailTrace_7262552 : CollatzResearch.WordTrace tailWord_7262552 prefixEnd_7262552 3729179954271974465600137 := by
  unfold tailWord_7262552
  simp only [CollatzResearch.WordTrace]
  refine ⟨132443516392510961988894955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176591355190014615985193273 132443516392510961988894955)
  ·
    refine ⟨198665274588766442983342433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132443516392510961988894955 198665274588766442983342433)
    ·
      refine ⟨148998955941574832237506825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198665274588766442983342433 148998955941574832237506825)
      ·
        refine ⟨111749216956181124178130119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 148998955941574832237506825 111749216956181124178130119)
        ·
          refine ⟨167623825434271686267195179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111749216956181124178130119 167623825434271686267195179)
          ·
            refine ⟨251435738151407529400792769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167623825434271686267195179 251435738151407529400792769)
            ·
              refine ⟨188576803613555647050594577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251435738151407529400792769 188576803613555647050594577)
              ·
                refine ⟨141432602710166735287945933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188576803613555647050594577 141432602710166735287945933)
                ·
                  refine ⟨53037226016312525732979725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 141432602710166735287945933 53037226016312525732979725)
                  ·
                    refine ⟨19888959756117197149867397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53037226016312525732979725 19888959756117197149867397)
                    ·
                      refine ⟨3729179954271974465600137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19888959756117197149867397 3729179954271974465600137)
                      ·
                        rfl

theorem cell23_7262552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_7262552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262552 prefixEnd_7262552 := by exact prefixLift 7262552
  have htrace : WordTrace (prefixWord ++ tailWord_7262552) baseStart_7262552 baseEnd_7262552 := by
    simpa [prefixWord, tailWord_7262552, baseEnd_7262552] using wordTrace_append hprefix tailTrace_7262552
  have hstable : (prefixWord ++ tailWord_7262552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262552).length < 2 ^ (prefixWord ++ tailWord_7262552).sum := by decide
  have hdescent : baseEnd_7262552 < baseStart_7262552 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262558 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7262558 : Nat := 118140960795 + 7262558 * 2 ^ 59
def prefixEnd_7262558 : Nat := 4983230072969 + 3 ^ 40 * 7262558 * 2
def baseEnd_7262558 : Nat := 3729183035155901442125111

theorem tailTrace_7262558 : CollatzResearch.WordTrace tailWord_7262558 prefixEnd_7262558 3729183035155901442125111 := by
  unfold tailWord_7262558
  simp only [CollatzResearch.WordTrace]
  refine ⟨33110906452875023375313541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176591501082000124668338885 33110906452875023375313541)
  ·
    refine ⟨6208294959914066882871289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33110906452875023375313541 6208294959914066882871289)
    ·
      refine ⟨4656221219935550162153467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208294959914066882871289 4656221219935550162153467)
      ·
        refine ⟨6984331829903325243230201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4656221219935550162153467 6984331829903325243230201)
        ·
          refine ⟨5238248872427493932422651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6984331829903325243230201 5238248872427493932422651)
          ·
            refine ⟨7857373308641240898633977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238248872427493932422651 7857373308641240898633977)
            ·
              refine ⟨5893029981480930673975483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7857373308641240898633977 5893029981480930673975483)
              ·
                refine ⟨8839544972221396010963225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893029981480930673975483 8839544972221396010963225)
                ·
                  refine ⟨6629658729166047008222419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8839544972221396010963225 6629658729166047008222419)
                  ·
                    refine ⟨9944488093749070512333629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6629658729166047008222419 9944488093749070512333629)
                    ·
                      refine ⟨3729183035155901442125111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9944488093749070512333629 3729183035155901442125111)
                      ·
                        rfl

theorem cell23_7262558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7262558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262558 prefixEnd_7262558 := by exact prefixLift 7262558
  have htrace : WordTrace (prefixWord ++ tailWord_7262558) baseStart_7262558 baseEnd_7262558 := by
    simpa [prefixWord, tailWord_7262558, baseEnd_7262558] using wordTrace_append hprefix tailTrace_7262558
  have hstable : (prefixWord ++ tailWord_7262558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262558).length < 2 ^ (prefixWord ++ tailWord_7262558).sum := by decide
  have hdescent : baseEnd_7262558 < baseStart_7262558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262569 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 6, 2]
def baseStart_7262569 : Nat := 118140960795 + 7262569 * 2 ^ 59
def prefixEnd_7262569 : Nat := 4983230072969 + 3 ^ 40 * 7262569 * 2
def baseEnd_7262569 : Nat := 3729188683443100899087559

theorem tailTrace_7262569 : CollatzResearch.WordTrace tailWord_7262569 prefixEnd_7262569 3729188683443100899087559 := by
  unfold tailWord_7262569
  simp only [CollatzResearch.WordTrace]
  refine ⟨264887652825960335881158761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176591768550640223920772507 264887652825960335881158761)
  ·
    refine ⟨198665739619470251910869071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264887652825960335881158761 198665739619470251910869071)
    ·
      refine ⟨297998609429205377866303607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198665739619470251910869071 297998609429205377866303607)
      ·
        refine ⟨446997914143808066799455411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 297998609429205377866303607 446997914143808066799455411)
        ·
          refine ⟨670496871215712100199183117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 446997914143808066799455411 670496871215712100199183117)
          ·
            refine ⟨251436326705892037574693669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670496871215712100199183117 251436326705892037574693669)
            ·
              refine ⟨47144311257354757045255063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 251436326705892037574693669 47144311257354757045255063)
              ·
                refine ⟨70716466886032135567882595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47144311257354757045255063 70716466886032135567882595)
                ·
                  refine ⟨106074700329048203351823893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70716466886032135567882595 106074700329048203351823893)
                  ·
                    refine ⟨4972251577924134532116745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106074700329048203351823893 4972251577924134532116745)
                    ·
                      refine ⟨3729188683443100899087559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972251577924134532116745 3729188683443100899087559)
                      ·
                        rfl

theorem cell23_7262569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6, 2].length) (baseStart_7262569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262569 prefixEnd_7262569 := by exact prefixLift 7262569
  have htrace : WordTrace (prefixWord ++ tailWord_7262569) baseStart_7262569 baseEnd_7262569 := by
    simpa [prefixWord, tailWord_7262569, baseEnd_7262569] using wordTrace_append hprefix tailTrace_7262569
  have hstable : (prefixWord ++ tailWord_7262569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262569).length < 2 ^ (prefixWord ++ tailWord_7262569).sum := by decide
  have hdescent : baseEnd_7262569 < baseStart_7262569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262660 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 6]
def baseStart_7262660 : Nat := 118140960795 + 7262660 * 2 ^ 59
def prefixEnd_7262660 : Nat := 4983230072969 + 3 ^ 40 * 7262660 * 2
def baseEnd_7262660 : Nat := 414359490020295560338849

theorem tailTrace_7262660 : CollatzResearch.WordTrace tailWord_7262660 prefixEnd_7262660 414359490020295560338849 := by
  unfold tailWord_7262660
  simp only [CollatzResearch.WordTrace]
  refine ⟨132445485934315329211360717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176593981245753772281814289 132445485934315329211360717)
  ·
    refine ⟨49667057225368248454260269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132445485934315329211360717 49667057225368248454260269)
    ·
      refine ⟨18625146459513093170347601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49667057225368248454260269 18625146459513093170347601)
      ·
        refine ⟨13968859844634819877760701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18625146459513093170347601 13968859844634819877760701)
        ·
          refine ⟨5238322441738057454160263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13968859844634819877760701 5238322441738057454160263)
          ·
            refine ⟨7857483662607086181240395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238322441738057454160263 7857483662607086181240395)
            ·
              refine ⟨11786225493910629271860593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857483662607086181240395 11786225493910629271860593)
              ·
                refine ⟨8839669120432971953895445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11786225493910629271860593 8839669120432971953895445)
                ·
                  refine ⟨414359490020295560338849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8839669120432971953895445 414359490020295560338849)
                  ·
                    rfl

theorem cell23_7262660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 6].length) (baseStart_7262660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262660 prefixEnd_7262660 := by exact prefixLift 7262660
  have htrace : WordTrace (prefixWord ++ tailWord_7262660) baseStart_7262660 baseEnd_7262660 := by
    simpa [prefixWord, tailWord_7262660, baseEnd_7262660] using wordTrace_append hprefix tailTrace_7262660
  have hstable : (prefixWord ++ tailWord_7262660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262660).length < 2 ^ (prefixWord ++ tailWord_7262660).sum := by decide
  have hdescent : baseEnd_7262660 < baseStart_7262660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262689 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_7262689 : Nat := 118140960795 + 7262689 * 2 ^ 59
def prefixEnd_7262689 : Nat := 4983230072969 + 3 ^ 40 * 7262689 * 2
def baseEnd_7262689 : Nat := 3729250301121640429587007

theorem tailTrace_7262689 : CollatzResearch.WordTrace tailWord_7262689 prefixEnd_7262689 3729250301121640429587007 := by
  unfold tailWord_7262689
  simp only [CollatzResearch.WordTrace]
  refine ⟨264892029585525596375527121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176594686390350397583684747 264892029585525596375527121)
  ·
    refine ⟨198669022189144197281645341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264892029585525596375527121 198669022189144197281645341)
    ·
      refine ⟨74500883320929073980617003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198669022189144197281645341 74500883320929073980617003)
      ·
        refine ⟨111751324981393610970925505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74500883320929073980617003 111751324981393610970925505)
        ·
          refine ⟨83813493736045208228194129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 111751324981393610970925505 83813493736045208228194129)
          ·
            refine ⟨62860120302033906171145597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83813493736045208228194129 62860120302033906171145597)
            ·
              refine ⟨23572545113262714814179599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62860120302033906171145597 23572545113262714814179599)
              ·
                refine ⟨35358817669894072221269399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23572545113262714814179599 35358817669894072221269399)
                ·
                  refine ⟨53038226504841108331904099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35358817669894072221269399 53038226504841108331904099)
                  ·
                    refine ⟨79557339757261662497856149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53038226504841108331904099 79557339757261662497856149)
                    ·
                      refine ⟨3729250301121640429587007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79557339757261662497856149 3729250301121640429587007)
                      ·
                        rfl

theorem cell23_7262689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_7262689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262689 prefixEnd_7262689 := by exact prefixLift 7262689
  have htrace : WordTrace (prefixWord ++ tailWord_7262689) baseStart_7262689 baseEnd_7262689 := by
    simpa [prefixWord, tailWord_7262689, baseEnd_7262689] using wordTrace_append hprefix tailTrace_7262689
  have hstable : (prefixWord ++ tailWord_7262689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262689).length < 2 ^ (prefixWord ++ tailWord_7262689).sum := by decide
  have hdescent : baseEnd_7262689 < baseStart_7262689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262727 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 3, 2, 2]
def baseStart_7262727 : Nat := 118140960795 + 7262727 * 2 ^ 59
def prefixEnd_7262727 : Nat := 4983230072969 + 3 ^ 40 * 7262727 * 2
def baseEnd_7262727 : Nat := 3729269813386511280911833

theorem tailTrace_7262727 : CollatzResearch.WordTrace tailWord_7262727 prefixEnd_7262727 3729269813386511280911833 := by
  unfold tailWord_7262727
  simp only [CollatzResearch.WordTrace]
  refine ⟨264893415559387928865410435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176595610372925285910273623 264893415559387928865410435)
  ·
    refine ⟨397340123339081893298115653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264893415559387928865410435 397340123339081893298115653)
    ·
      refine ⟨74501273126077854993396685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 397340123339081893298115653 74501273126077854993396685)
      ·
        refine ⟨27937977422279195622523757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74501273126077854993396685 27937977422279195622523757)
        ·
          refine ⟨10476741533354698358446409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27937977422279195622523757 10476741533354698358446409)
          ·
            refine ⟨7857556150016023768834807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476741533354698358446409 7857556150016023768834807)
            ·
              refine ⟨11786334225024035653252211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857556150016023768834807 11786334225024035653252211)
              ·
                refine ⟨17679501337536053479878317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786334225024035653252211 17679501337536053479878317)
                ·
                  refine ⟨6629813001576020054954369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17679501337536053479878317 6629813001576020054954369)
                  ·
                    refine ⟨4972359751182015041215777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629813001576020054954369 4972359751182015041215777)
                    ·
                      refine ⟨3729269813386511280911833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972359751182015041215777 3729269813386511280911833)
                      ·
                        rfl

theorem cell23_7262727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_7262727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262727 prefixEnd_7262727 := by exact prefixLift 7262727
  have htrace : WordTrace (prefixWord ++ tailWord_7262727) baseStart_7262727 baseEnd_7262727 := by
    simpa [prefixWord, tailWord_7262727, baseEnd_7262727] using wordTrace_append hprefix tailTrace_7262727
  have hstable : (prefixWord ++ tailWord_7262727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262727).length < 2 ^ (prefixWord ++ tailWord_7262727).sum := by decide
  have hdescent : baseEnd_7262727 < baseStart_7262727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262733 : List Nat := [1, 7, 1, 1, 1, 1, 1, 10]
def baseStart_7262733 : Nat := 118140960795 + 7262733 * 2 ^ 59
def prefixEnd_7262733 : Nat := 4983230072969 + 3 ^ 40 * 7262733 * 2
def baseEnd_7262733 : Nat := 138121218306312528053215

theorem tailTrace_7262733 : CollatzResearch.WordTrace tailWord_7262733 prefixEnd_7262733 138121218306312528053215 := by
  unfold tailWord_7262733
  simp only [CollatzResearch.WordTrace]
  refine ⟨264893634397366191890128853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176595756264910794593419235 264893634397366191890128853)
  ·
    refine ⟨6208444556188270122424895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 264893634397366191890128853 6208444556188270122424895)
    ·
      refine ⟨9312666834282405183637343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6208444556188270122424895 9312666834282405183637343)
      ·
        refine ⟨13969000251423607775456015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9312666834282405183637343 13969000251423607775456015)
        ·
          refine ⟨20953500377135411663184023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13969000251423607775456015 20953500377135411663184023)
          ·
            refine ⟨31430250565703117494776035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20953500377135411663184023 31430250565703117494776035)
            ·
              refine ⟨47145375848554676242164053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31430250565703117494776035 47145375848554676242164053)
              ·
                refine ⟨138121218306312528053215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47145375848554676242164053 138121218306312528053215)
                ·
                  rfl

theorem cell23_7262733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 10].length) (baseStart_7262733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262733 prefixEnd_7262733 := by exact prefixLift 7262733
  have htrace : WordTrace (prefixWord ++ tailWord_7262733) baseStart_7262733 baseEnd_7262733 := by
    simpa [prefixWord, tailWord_7262733, baseEnd_7262733] using wordTrace_append hprefix tailTrace_7262733
  have hstable : (prefixWord ++ tailWord_7262733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262733).length < 2 ^ (prefixWord ++ tailWord_7262733).sum := by decide
  have hdescent : baseEnd_7262733 < baseStart_7262733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262753 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_7262753 : Nat := 118140960795 + 7262753 * 2 ^ 59
def prefixEnd_7262753 : Nat := 4983230072969 + 3 ^ 40 * 7262753 * 2
def baseEnd_7262753 : Nat := 3729283163883528179186713

theorem tailTrace_7262753 : CollatzResearch.WordTrace tailWord_7262753 prefixEnd_7262753 3729283163883528179186713 := by
  unfold tailWord_7262753
  simp only [CollatzResearch.WordTrace]
  refine ⟨264894363857293735305856913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176596242571529156870571275 264894363857293735305856913)
  ·
    refine ⟨198670772892970301479392685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264894363857293735305856913 198670772892970301479392685)
    ·
      refine ⟨74501539834863863054772257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198670772892970301479392685 74501539834863863054772257)
      ·
        refine ⟨55876154876147897291079193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74501539834863863054772257 55876154876147897291079193)
        ·
          refine ⟨41907116157110922968309395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55876154876147897291079193 41907116157110922968309395)
          ·
            refine ⟨62860674235666384452464093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41907116157110922968309395 62860674235666384452464093)
            ·
              refine ⟨23572752838374894169674035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62860674235666384452464093 23572752838374894169674035)
              ·
                refine ⟨35359129257562341254511053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23572752838374894169674035 35359129257562341254511053)
                ·
                  refine ⟨13259673471585877970441645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35359129257562341254511053 13259673471585877970441645)
                  ·
                    refine ⟨4972377551844704238915617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13259673471585877970441645 4972377551844704238915617)
                    ·
                      refine ⟨3729283163883528179186713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972377551844704238915617 3729283163883528179186713)
                      ·
                        rfl

theorem cell23_7262753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_7262753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262753 prefixEnd_7262753 := by exact prefixLift 7262753
  have htrace : WordTrace (prefixWord ++ tailWord_7262753) baseStart_7262753 baseEnd_7262753 := by
    simpa [prefixWord, tailWord_7262753, baseEnd_7262753] using wordTrace_append hprefix tailTrace_7262753
  have hstable : (prefixWord ++ tailWord_7262753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262753).length < 2 ^ (prefixWord ++ tailWord_7262753).sum := by decide
  have hdescent : baseEnd_7262753 < baseStart_7262753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262796 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 2, 2, 4]
def baseStart_7262796 : Nat := 118140960795 + 7262796 * 2 ^ 59
def prefixEnd_7262796 : Nat := 4983230072969 + 3 ^ 40 * 7262796 * 2
def baseEnd_7262796 : Nat := 3729305243551671510949015

theorem tailTrace_7262796 : CollatzResearch.WordTrace tailWord_7262796 prefixEnd_7262796 3729305243551671510949015 := by
  unfold tailWord_7262796
  simp only [CollatzResearch.WordTrace]
  refine ⟨132447966098068976824836121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176597288130758635766448161 132447966098068976824836121)
  ·
    refine ⟨99335974573551732618627091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132447966098068976824836121 99335974573551732618627091)
    ·
      refine ⟨149003961860327598927940637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99335974573551732618627091 149003961860327598927940637)
      ·
        refine ⟨55876485697622849597977739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149003961860327598927940637 55876485697622849597977739)
        ·
          refine ⟨83814728546434274396966609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55876485697622849597977739 83814728546434274396966609)
          ·
            refine ⟨62861046409825705797724957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83814728546434274396966609 62861046409825705797724957)
            ·
              refine ⟨23572892403684639674146859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62861046409825705797724957 23572892403684639674146859)
              ·
                refine ⟨35359338605526959511220289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23572892403684639674146859 35359338605526959511220289)
                ·
                  refine ⟨26519503954145219633415217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35359338605526959511220289 26519503954145219633415217)
                  ·
                    refine ⟨19889627965608914725061413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26519503954145219633415217 19889627965608914725061413)
                    ·
                      refine ⟨3729305243551671510949015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19889627965608914725061413 3729305243551671510949015)
                      ·
                        rfl

theorem cell23_7262796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_7262796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262796 prefixEnd_7262796 := by exact prefixLift 7262796
  have htrace : WordTrace (prefixWord ++ tailWord_7262796) baseStart_7262796 baseEnd_7262796 := by
    simpa [prefixWord, tailWord_7262796, baseEnd_7262796] using wordTrace_append hprefix tailTrace_7262796
  have hstable : (prefixWord ++ tailWord_7262796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262796).length < 2 ^ (prefixWord ++ tailWord_7262796).sum := by decide
  have hdescent : baseEnd_7262796 < baseStart_7262796 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262834 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 2, 2, 2]
def baseStart_7262834 : Nat := 118140960795 + 7262834 * 2 ^ 59
def prefixEnd_7262834 : Nat := 4983230072969 + 3 ^ 40 * 7262834 * 2
def baseEnd_7262834 : Nat := 3729324755816542362273841

theorem tailTrace_7262834 : CollatzResearch.WordTrace tailWord_7262834 prefixEnd_7262834 3729324755816542362273841 := by
  unfold tailWord_7262834
  simp only [CollatzResearch.WordTrace]
  refine ⟨66224329542500071534888889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176598212113333524093037037 66224329542500071534888889)
  ·
    refine ⟨49668247156875053651166667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66224329542500071534888889 49668247156875053651166667)
    ·
      refine ⟨74502370735312580476750001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49668247156875053651166667 74502370735312580476750001)
      ·
        refine ⟨55876778051484435357562501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74502370735312580476750001 55876778051484435357562501)
        ·
          refine ⟨10476895884653331629542969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55876778051484435357562501 10476895884653331629542969)
          ·
            refine ⟨7857671913489998722157227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10476895884653331629542969 7857671913489998722157227)
            ·
              refine ⟨11786507870234998083235841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857671913489998722157227 11786507870234998083235841)
              ·
                refine ⟨8839880902676248562426881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11786507870234998083235841 8839880902676248562426881)
                ·
                  refine ⟨6629910677007186421820161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8839880902676248562426881 6629910677007186421820161)
                  ·
                    refine ⟨4972433007755389816365121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6629910677007186421820161 4972433007755389816365121)
                    ·
                      refine ⟨3729324755816542362273841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972433007755389816365121 3729324755816542362273841)
                      ·
                        rfl

theorem cell23_7262834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_7262834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262834 prefixEnd_7262834 := by exact prefixLift 7262834
  have htrace : WordTrace (prefixWord ++ tailWord_7262834) baseStart_7262834 baseEnd_7262834 := by
    simpa [prefixWord, tailWord_7262834, baseEnd_7262834] using wordTrace_append hprefix tailTrace_7262834
  have hstable : (prefixWord ++ tailWord_7262834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262834).length < 2 ^ (prefixWord ++ tailWord_7262834).sum := by decide
  have hdescent : baseEnd_7262834 < baseStart_7262834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262874 : List Nat := [3, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_7262874 : Nat := 118140960795 + 7262874 * 2 ^ 59
def prefixEnd_7262874 : Nat := 4983230072969 + 3 ^ 40 * 7262874 * 2
def baseEnd_7262874 : Nat := 414371699449191356197073

theorem tailTrace_7262874 : CollatzResearch.WordTrace tailWord_7262874 prefixEnd_7262874 414371699449191356197073 := by
  unfold tailWord_7262874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66224694272463843242752919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176599184726570248647341117 66224694272463843242752919)
  ·
    refine ⟨99337041408695764864129379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66224694272463843242752919 99337041408695764864129379)
    ·
      refine ⟨149005562113043647296194069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99337041408695764864129379 149005562113043647296194069)
      ·
        refine ⟨6984635724048920967009097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149005562113043647296194069 6984635724048920967009097)
        ·
          refine ⟨5238476793036690725256823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6984635724048920967009097 5238476793036690725256823)
          ·
            refine ⟨7857715189555036087885235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238476793036690725256823 7857715189555036087885235)
            ·
              refine ⟨11786572784332554131827853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857715189555036087885235 11786572784332554131827853)
              ·
                refine ⟨4419964794124707799435445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11786572784332554131827853 4419964794124707799435445)
                ·
                  refine ⟨414371699449191356197073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4419964794124707799435445 414371699449191356197073)
                  ·
                    rfl

theorem cell23_7262874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_7262874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262874 prefixEnd_7262874 := by exact prefixLift 7262874
  have htrace : WordTrace (prefixWord ++ tailWord_7262874) baseStart_7262874 baseEnd_7262874 := by
    simpa [prefixWord, tailWord_7262874, baseEnd_7262874] using wordTrace_append hprefix tailTrace_7262874
  have hstable : (prefixWord ++ tailWord_7262874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262874).length < 2 ^ (prefixWord ++ tailWord_7262874).sum := by decide
  have hdescent : baseEnd_7262874 < baseStart_7262874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262896 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 6]
def baseStart_7262896 : Nat := 118140960795 + 7262896 * 2 ^ 59
def prefixEnd_7262896 : Nat := 4983230072969 + 3 ^ 40 * 7262896 * 2
def baseEnd_7262896 : Nat := 414372954624124568855395

theorem tailTrace_7262896 : CollatzResearch.WordTrace tailWord_7262896 prefixEnd_7262896 414372954624124568855395 := by
  unfold tailWord_7262896
  simp only [CollatzResearch.WordTrace]
  refine ⟨132449789747887835364156271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176599719663850447152208361 132449789747887835364156271)
  ·
    refine ⟨198674684621831753046234407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132449789747887835364156271 198674684621831753046234407)
    ·
      refine ⟨298012026932747629569351611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198674684621831753046234407 298012026932747629569351611)
      ·
        refine ⟨447018040399121444354027417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298012026932747629569351611 447018040399121444354027417)
        ·
          refine ⟨335263530299341083265520563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447018040399121444354027417 335263530299341083265520563)
          ·
            refine ⟨502895295449011624898280845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335263530299341083265520563 502895295449011624898280845)
            ·
              refine ⟨188585735793379359336855317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 502895295449011624898280845 188585735793379359336855317)
              ·
                refine ⟨8839956365314657468915093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 188585735793379359336855317 8839956365314657468915093)
                ·
                  refine ⟨414372954624124568855395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8839956365314657468915093 414372954624124568855395)
                  ·
                    rfl

theorem cell23_7262896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 6].length) (baseStart_7262896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262896 prefixEnd_7262896 := by exact prefixLift 7262896
  have htrace : WordTrace (prefixWord ++ tailWord_7262896) baseStart_7262896 baseEnd_7262896 := by
    simpa [prefixWord, tailWord_7262896, baseEnd_7262896] using wordTrace_append hprefix tailTrace_7262896
  have hstable : (prefixWord ++ tailWord_7262896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262896).length < 2 ^ (prefixWord ++ tailWord_7262896).sum := by decide
  have hdescent : baseEnd_7262896 < baseStart_7262896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262956 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 5, 6]
def baseStart_7262956 : Nat := 118140960795 + 7262956 * 2 ^ 59
def prefixEnd_7262956 : Nat := 4983230072969 + 3 ^ 40 * 7262956 * 2
def baseEnd_7262956 : Nat := 1243129133485463628316093

theorem tailTrace_7262956 : CollatzResearch.WordTrace tailWord_7262956 prefixEnd_7262956 1243129133485463628316093 := by
  unfold tailWord_7262956
  simp only [CollatzResearch.WordTrace]
  refine ⟨132450883937779150487748361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176601178583705533983664481 132450883937779150487748361)
  ·
    refine ⟨99338162953334362865811271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132450883937779150487748361 99338162953334362865811271)
    ·
      refine ⟨149007244430001544298716907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99338162953334362865811271 149007244430001544298716907)
      ·
        refine ⟨223510866645002316448075361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149007244430001544298716907 223510866645002316448075361)
        ·
          refine ⟨167633149983751737336056521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223510866645002316448075361 167633149983751737336056521)
          ·
            refine ⟨125724862487813803002042391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167633149983751737336056521 125724862487813803002042391)
            ·
              refine ⟨188587293731720704503063587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125724862487813803002042391 188587293731720704503063587)
              ·
                refine ⟨282880940597581056754595381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188587293731720704503063587 282880940597581056754595381)
                ·
                  refine ⟨26520088181023224070743317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 282880940597581056754595381 26520088181023224070743317)
                  ·
                    refine ⟨1243129133485463628316093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26520088181023224070743317 1243129133485463628316093)
                    ·
                      rfl

theorem cell23_7262956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 6].length) (baseStart_7262956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262956 prefixEnd_7262956 := by exact prefixLift 7262956
  have htrace : WordTrace (prefixWord ++ tailWord_7262956) baseStart_7262956 baseEnd_7262956 := by
    simpa [prefixWord, tailWord_7262956, baseEnd_7262956] using wordTrace_append hprefix tailTrace_7262956
  have hstable : (prefixWord ++ tailWord_7262956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262956).length < 2 ^ (prefixWord ++ tailWord_7262956).sum := by decide
  have hdescent : baseEnd_7262956 < baseStart_7262956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262963 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 6, 2]
def baseStart_7262963 : Nat := 118140960795 + 7262963 * 2 ^ 59
def prefixEnd_7262963 : Nat := 4983230072969 + 3 ^ 40 * 7262963 * 2
def baseEnd_7262963 : Nat := 3729390994820972357560747

theorem tailTrace_7262963 : CollatzResearch.WordTrace tailWord_7262963 prefixEnd_7262963 3729390994820972357560747 := by
  unfold tailWord_7262963
  simp only [CollatzResearch.WordTrace]
  refine ⟨264902023186532941171001543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176601348791021960780667695 264902023186532941171001543)
  ·
    refine ⟨397353034779799411756502315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264902023186532941171001543 397353034779799411756502315)
    ·
      refine ⟨596029552169699117634753473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397353034779799411756502315 596029552169699117634753473)
      ·
        refine ⟨447022164127274338226065105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596029552169699117634753473 447022164127274338226065105)
        ·
          refine ⟨335266623095455753669548829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447022164127274338226065105 335266623095455753669548829)
          ·
            refine ⟨125724983660795907626080811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335266623095455753669548829 125724983660795907626080811)
            ·
              refine ⟨188587475491193861439121217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125724983660795907626080811 188587475491193861439121217)
              ·
                refine ⟨141440606618395396079340913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 188587475491193861439121217 141440606618395396079340913)
                ·
                  refine ⟨106080454963796547059505685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141440606618395396079340913 106080454963796547059505685)
                  ·
                    refine ⟨4972521326427963143414329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106080454963796547059505685 4972521326427963143414329)
                    ·
                      refine ⟨3729390994820972357560747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972521326427963143414329 3729390994820972357560747)
                      ·
                        rfl

theorem cell23_7262963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 6, 2].length) (baseStart_7262963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262963 prefixEnd_7262963 := by exact prefixLift 7262963
  have htrace : WordTrace (prefixWord ++ tailWord_7262963) baseStart_7262963 baseEnd_7262963 := by
    simpa [prefixWord, tailWord_7262963, baseEnd_7262963] using wordTrace_append hprefix tailTrace_7262963
  have hstable : (prefixWord ++ tailWord_7262963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262963).length < 2 ^ (prefixWord ++ tailWord_7262963).sum := by decide
  have hdescent : baseEnd_7262963 < baseStart_7262963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262973 : List Nat := [1, 4, 1, 1, 1, 1, 6, 1, 1, 6]
def baseStart_7262973 : Nat := 118140960795 + 7262973 * 2 ^ 59
def prefixEnd_7262973 : Nat := 4983230072969 + 3 ^ 40 * 7262973 * 2
def baseEnd_7262973 : Nat := 1243132043209172439478567

theorem tailTrace_7262973 : CollatzResearch.WordTrace tailWord_7262973 prefixEnd_7262973 1243132043209172439478567 := by
  unfold tailWord_7262973
  simp only [CollatzResearch.WordTrace]
  refine ⟨264902387916496712878865573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176601591944331141919243715 264902387916496712878865573)
  ·
    refine ⟨49669197734343133664787295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264902387916496712878865573 49669197734343133664787295)
    ·
      refine ⟨74503796601514700497180943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49669197734343133664787295 74503796601514700497180943)
      ·
        refine ⟨111755694902272050745771415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74503796601514700497180943 111755694902272050745771415)
        ·
          refine ⟨167633542353408076118657123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111755694902272050745771415 167633542353408076118657123)
          ·
            refine ⟨251450313530112114177985685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167633542353408076118657123 251450313530112114177985685)
            ·
              refine ⟨11786733446724005352093079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 251450313530112114177985685 11786733446724005352093079)
              ·
                refine ⟨17680100170086008028139619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11786733446724005352093079 17680100170086008028139619)
                ·
                  refine ⟨26520150255129012042209429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17680100170086008028139619 26520150255129012042209429)
                  ·
                    refine ⟨1243132043209172439478567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26520150255129012042209429 1243132043209172439478567)
                    ·
                      rfl

theorem cell23_7262973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_7262973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262973 prefixEnd_7262973 := by exact prefixLift 7262973
  have htrace : WordTrace (prefixWord ++ tailWord_7262973) baseStart_7262973 baseEnd_7262973 := by
    simpa [prefixWord, tailWord_7262973, baseEnd_7262973] using wordTrace_append hprefix tailTrace_7262973
  have hstable : (prefixWord ++ tailWord_7262973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262973).length < 2 ^ (prefixWord ++ tailWord_7262973).sum := by decide
  have hdescent : baseEnd_7262973 < baseStart_7262973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262980 : List Nat := [2, 3, 2, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_7262980 : Nat := 118140960795 + 7262980 * 2 ^ 59
def prefixEnd_7262980 : Nat := 4983230072969 + 3 ^ 40 * 7262980 * 2
def baseEnd_7262980 : Nat := 3729399723992098791048169

theorem tailTrace_7262980 : CollatzResearch.WordTrace tailWord_7262980 prefixEnd_7262980 3729399723992098791048169 := by
  unfold tailWord_7262980
  simp only [CollatzResearch.WordTrace]
  refine ⟨132451321613735676537185197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176601762151647568716246929 132451321613735676537185197)
  ·
    refine ⟨49669245605150878701444449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132451321613735676537185197 49669245605150878701444449)
    ·
      refine ⟨37251934203863159026083337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49669245605150878701444449 37251934203863159026083337)
      ·
        refine ⟨27938950652897369269562503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37251934203863159026083337 27938950652897369269562503)
        ·
          refine ⟨41908425979346053904343755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27938950652897369269562503 41908425979346053904343755)
          ·
            refine ⟨62862638969019080856515633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41908425979346053904343755 62862638969019080856515633)
            ·
              refine ⟨47146979226764310642386725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62862638969019080856515633 47146979226764310642386725)
              ·
                refine ⟨8840058605018308245447511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47146979226764310642386725 8840058605018308245447511)
                ·
                  refine ⟨13260087907527462368171267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840058605018308245447511 13260087907527462368171267)
                  ·
                    refine ⟨19890131861291193552256901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13260087907527462368171267 19890131861291193552256901)
                    ·
                      refine ⟨3729399723992098791048169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19890131861291193552256901 3729399723992098791048169)
                      ·
                        rfl

theorem cell23_7262980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_7262980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262980 prefixEnd_7262980 := by exact prefixLift 7262980
  have htrace : WordTrace (prefixWord ++ tailWord_7262980) baseStart_7262980 baseEnd_7262980 := by
    simpa [prefixWord, tailWord_7262980, baseEnd_7262980] using wordTrace_append hprefix tailTrace_7262980
  have hstable : (prefixWord ++ tailWord_7262980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262980).length < 2 ^ (prefixWord ++ tailWord_7262980).sum := by decide
  have hdescent : baseEnd_7262980 < baseStart_7262980 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7262993 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_7262993 : Nat := 118140960795 + 7262993 * 2 ^ 59
def prefixEnd_7262993 : Nat := 4983230072969 + 3 ^ 40 * 7262993 * 2
def baseEnd_7262993 : Nat := 3729406399240607240185609

theorem tailTrace_7262993 : CollatzResearch.WordTrace tailWord_7262993 prefixEnd_7262993 3729406399240607240185609 := by
  unfold tailWord_7262993
  simp only [CollatzResearch.WordTrace]
  refine ⟨264903117376424256294593633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176602078250949504196395755 264903117376424256294593633)
  ·
    refine ⟨198677338032318192220945225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264903117376424256294593633 198677338032318192220945225)
    ·
      refine ⟨149008003524238644165708919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198677338032318192220945225 149008003524238644165708919)
      ·
        refine ⟨223512005286357966248563379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149008003524238644165708919 223512005286357966248563379)
        ·
          refine ⟨335268007929536949372845069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223512005286357966248563379 335268007929536949372845069)
          ·
            refine ⟨125725502973576356014816901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335268007929536949372845069 125725502973576356014816901)
            ·
              refine ⟨23573531807545566752778169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125725502973576356014816901 23573531807545566752778169)
              ·
                refine ⟨17680148855659175064583627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23573531807545566752778169 17680148855659175064583627)
                ·
                  refine ⟨26520223283488762596875441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17680148855659175064583627 26520223283488762596875441)
                  ·
                    refine ⟨19890167462616571947656581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26520223283488762596875441 19890167462616571947656581)
                    ·
                      refine ⟨3729406399240607240185609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19890167462616571947656581 3729406399240607240185609)
                      ·
                        rfl

theorem cell23_7262993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_7262993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7262993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7262993 prefixEnd_7262993 := by exact prefixLift 7262993
  have htrace : WordTrace (prefixWord ++ tailWord_7262993) baseStart_7262993 baseEnd_7262993 := by
    simpa [prefixWord, tailWord_7262993, baseEnd_7262993] using wordTrace_append hprefix tailTrace_7262993
  have hstable : (prefixWord ++ tailWord_7262993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7262993).length < 2 ^ (prefixWord ++ tailWord_7262993).sum := by decide
  have hdescent : baseEnd_7262993 < baseStart_7262993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7262993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263007 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 2, 4]
def baseStart_7263007 : Nat := 118140960795 + 7263007 * 2 ^ 59
def prefixEnd_7263007 : Nat := 4983230072969 + 3 ^ 40 * 7263007 * 2
def baseEnd_7263007 : Nat := 1243137862656590061803515

theorem tailTrace_7263007 : CollatzResearch.WordTrace tailWord_7263007 prefixEnd_7263007 1243137862656590061803515 := by
  unfold tailWord_7263007
  simp only [CollatzResearch.WordTrace]
  refine ⟨264903627998373536685603275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176602418665582357790402183 264903627998373536685603275)
  ·
    refine ⟨397355441997560305028404913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264903627998373536685603275 397355441997560305028404913)
    ·
      refine ⟨298016581498170228771303685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397355441997560305028404913 298016581498170228771303685)
      ·
        refine ⟨55878109030906917894619441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 298016581498170228771303685 55878109030906917894619441)
        ·
          refine ⟨41908581773180188420964581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55878109030906917894619441 41908581773180188420964581)
          ·
            refine ⟨7857859082471285328930859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41908581773180188420964581 7857859082471285328930859)
            ·
              refine ⟨11786788623706927993396289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7857859082471285328930859 11786788623706927993396289)
              ·
                refine ⟨8840091467780195995047217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11786788623706927993396289 8840091467780195995047217)
                ·
                  refine ⟨6630068600835146996285413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8840091467780195995047217 6630068600835146996285413)
                  ·
                    refine ⟨1243137862656590061803515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6630068600835146996285413 1243137862656590061803515)
                    ·
                      rfl

theorem cell23_7263007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 2, 4].length) (baseStart_7263007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263007 prefixEnd_7263007 := by exact prefixLift 7263007
  have htrace : WordTrace (prefixWord ++ tailWord_7263007) baseStart_7263007 baseEnd_7263007 := by
    simpa [prefixWord, tailWord_7263007, baseEnd_7263007] using wordTrace_append hprefix tailTrace_7263007
  have hstable : (prefixWord ++ tailWord_7263007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263007).length < 2 ^ (prefixWord ++ tailWord_7263007).sum := by decide
  have hdescent : baseEnd_7263007 < baseStart_7263007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263037 : List Nat := [1, 4, 1, 4, 2, 2, 2, 7]
def baseStart_7263037 : Nat := 118140960795 + 7263037 * 2 ^ 59
def prefixEnd_7263037 : Nat := 4983230072969 + 3 ^ 40 * 7263037 * 2
def baseEnd_7263037 : Nat := 138126999718126113630941

theorem tailTrace_7263037 : CollatzResearch.WordTrace tailWord_7263037 prefixEnd_7263037 138126999718126113630941 := by
  unfold tailWord_7263037
  simp only [CollatzResearch.WordTrace]
  refine ⟨264904722188264851809195365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176603148125509901206130243 264904722188264851809195365)
  ·
    refine ⟨49669635410299659714224131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264904722188264851809195365 49669635410299659714224131)
    ·
      refine ⟨74504453115449489571336197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49669635410299659714224131 74504453115449489571336197)
      ·
        refine ⟨13969584959146779294625537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74504453115449489571336197 13969584959146779294625537)
        ·
          refine ⟨10477188719360084470969153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13969584959146779294625537 10477188719360084470969153)
          ·
            refine ⟨7857891539520063353226865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10477188719360084470969153 7857891539520063353226865)
            ·
              refine ⟨5893418654640047514920149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7857891539520063353226865 5893418654640047514920149)
              ·
                refine ⟨138126999718126113630941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5893418654640047514920149 138126999718126113630941)
                ·
                  rfl

theorem cell23_7263037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 7].length) (baseStart_7263037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263037 prefixEnd_7263037 := by exact prefixLift 7263037
  have htrace : WordTrace (prefixWord ++ tailWord_7263037) baseStart_7263037 baseEnd_7263037 := by
    simpa [prefixWord, tailWord_7263037, baseEnd_7263037] using wordTrace_append hprefix tailTrace_7263037
  have hstable : (prefixWord ++ tailWord_7263037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263037).length < 2 ^ (prefixWord ++ tailWord_7263037).sum := by decide
  have hdescent : baseEnd_7263037 < baseStart_7263037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263040 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2]
def baseStart_7263040 : Nat := 118140960795 + 7263040 * 2 ^ 59
def prefixEnd_7263040 : Nat := 4983230072969 + 3 ^ 40 * 7263040 * 2
def baseEnd_7263040 : Nat := 3729430532831368556297893

theorem tailTrace_7263040 : CollatzResearch.WordTrace tailWord_7263040 prefixEnd_7263040 3729430532831368556297893 := by
  unfold tailWord_7263040
  simp only [CollatzResearch.WordTrace]
  refine ⟨132452415803626991660777287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176603221071502655547703049 132452415803626991660777287)
  ·
    refine ⟨198678623705440487491165931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132452415803626991660777287 198678623705440487491165931)
    ·
      refine ⟨298017935558160731236748897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198678623705440487491165931 298017935558160731236748897)
      ·
        refine ⟨223513451668620548427561673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298017935558160731236748897 223513451668620548427561673)
        ·
          refine ⟨167635088751465411320671255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223513451668620548427561673 167635088751465411320671255)
          ·
            refine ⟨251452633127198116981006883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167635088751465411320671255 251452633127198116981006883)
            ·
              refine ⟨377178949690797175471510325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251452633127198116981006883 377178949690797175471510325)
              ·
                refine ⟨35360526533512235200454093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377178949690797175471510325 35360526533512235200454093)
                ·
                  refine ⟨13260197450067088200170285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35360526533512235200454093 13260197450067088200170285)
                  ·
                    refine ⟨4972574043775158075063857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13260197450067088200170285 4972574043775158075063857)
                    ·
                      refine ⟨3729430532831368556297893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972574043775158075063857 3729430532831368556297893)
                      ·
                        rfl

theorem cell23_7263040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 3, 2].length) (baseStart_7263040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263040 prefixEnd_7263040 := by exact prefixLift 7263040
  have htrace : WordTrace (prefixWord ++ tailWord_7263040) baseStart_7263040 baseEnd_7263040 := by
    simpa [prefixWord, tailWord_7263040, baseEnd_7263040] using wordTrace_append hprefix tailTrace_7263040
  have hstable : (prefixWord ++ tailWord_7263040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263040).length < 2 ^ (prefixWord ++ tailWord_7263040).sum := by decide
  have hdescent : baseEnd_7263040 < baseStart_7263040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263083 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_7263083 : Nat := 118140960795 + 7263083 * 2 ^ 59
def prefixEnd_7263083 : Nat := 4983230072969 + 3 ^ 40 * 7263083 * 2
def baseEnd_7263083 : Nat := 3729452612499511888060195

theorem tailTrace_7263083 : CollatzResearch.WordTrace tailWord_7263083 prefixEnd_7263083 3729452612499511888060195 := by
  unfold tailWord_7263083
  simp only [CollatzResearch.WordTrace]
  refine ⟨264906399946098201665369903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176604266630732134443579935 264906399946098201665369903)
  ·
    refine ⟨397359599919147302498054855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264906399946098201665369903 397359599919147302498054855)
    ·
      refine ⟨596039399878720953747082283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397359599919147302498054855 596039399878720953747082283)
      ·
        refine ⟨894059099818081430620623425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596039399878720953747082283 894059099818081430620623425)
        ·
          refine ⟨670544324863561072965467569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894059099818081430620623425 670544324863561072965467569)
          ·
            refine ⟨502908243647670804724100677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670544324863561072965467569 502908243647670804724100677)
            ·
              refine ⟨94295295683938275885768877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502908243647670804724100677 94295295683938275885768877)
              ·
                refine ⟨35360735881476853457163329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94295295683938275885768877 35360735881476853457163329)
                ·
                  refine ⟨26520551911107640092872497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35360735881476853457163329 26520551911107640092872497)
                  ·
                    refine ⟨19890413933330730069654373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26520551911107640092872497 19890413933330730069654373)
                    ·
                      refine ⟨3729452612499511888060195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19890413933330730069654373 3729452612499511888060195)
                      ·
                        rfl

theorem cell23_7263083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_7263083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263083 prefixEnd_7263083 := by exact prefixLift 7263083
  have htrace : WordTrace (prefixWord ++ tailWord_7263083) baseStart_7263083 baseEnd_7263083 := by
    simpa [prefixWord, tailWord_7263083, baseEnd_7263083] using wordTrace_append hprefix tailTrace_7263083
  have hstable : (prefixWord ++ tailWord_7263083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263083).length < 2 ^ (prefixWord ++ tailWord_7263083).sum := by decide
  have hdescent : baseEnd_7263083 < baseStart_7263083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263123 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 4, 5]
def baseStart_7263123 : Nat := 118140960795 + 7263123 * 2 ^ 59
def prefixEnd_7263123 : Nat := 4983230072969 + 3 ^ 40 * 7263123 * 2
def baseEnd_7263123 : Nat := 1243157717241897243853337

theorem tailTrace_7263123 : CollatzResearch.WordTrace tailWord_7263123 prefixEnd_7263123 1243157717241897243853337 := by
  unfold tailWord_7263123
  simp only [CollatzResearch.WordTrace]
  refine ⟨264907858865953288496826023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176605239243968858997884015 264907858865953288496826023)
  ·
    refine ⟨397361788298929932745239035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264907858865953288496826023 397361788298929932745239035)
    ·
      refine ⟨596042682448394899117858553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397361788298929932745239035 596042682448394899117858553)
      ·
        refine ⟨447032011836296174338393915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596042682448394899117858553 447032011836296174338393915)
        ·
          refine ⟨670548017754444261507590873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447032011836296174338393915 670548017754444261507590873)
          ·
            refine ⟨502911013315833196130693155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670548017754444261507590873 502911013315833196130693155)
            ·
              refine ⟨754366519973749794196039733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502911013315833196130693155 754366519973749794196039733)
              ·
                refine ⟨70721861247539043205878725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 754366519973749794196039733 70721861247539043205878725)
                ·
                  refine ⟨13260348983913570601102261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 70721861247539043205878725 13260348983913570601102261)
                  ·
                    refine ⟨1243157717241897243853337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13260348983913570601102261 1243157717241897243853337)
                    ·
                      rfl

theorem cell23_7263123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 5].length) (baseStart_7263123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263123 prefixEnd_7263123 := by exact prefixLift 7263123
  have htrace : WordTrace (prefixWord ++ tailWord_7263123) baseStart_7263123 baseEnd_7263123 := by
    simpa [prefixWord, tailWord_7263123, baseEnd_7263123] using wordTrace_append hprefix tailTrace_7263123
  have hstable : (prefixWord ++ tailWord_7263123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263123).length < 2 ^ (prefixWord ++ tailWord_7263123).sum := by decide
  have hdescent : baseEnd_7263123 < baseStart_7263123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263137 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_7263137 : Nat := 118140960795 + 7263137 * 2 ^ 59
def prefixEnd_7263137 : Nat := 4983230072969 + 3 ^ 40 * 7263137 * 2
def baseEnd_7263137 : Nat := 3729480340454854676784947

theorem tailTrace_7263137 : CollatzResearch.WordTrace tailWord_7263137 prefixEnd_7263137 3729480340454854676784947 := by
  unfold tailWord_7263137
  simp only [CollatzResearch.WordTrace]
  refine ⟨264908369487902568887835665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176605579658601712591890443 264908369487902568887835665)
  ·
    refine ⟨198681277115926926665876749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264908369487902568887835665 198681277115926926665876749)
    ·
      refine ⟨74505478918472597499703781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198681277115926926665876749 74505478918472597499703781)
      ·
        refine ⟨13969777297213612031194459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74505478918472597499703781 13969777297213612031194459)
        ·
          refine ⟨20954665945820418046791689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13969777297213612031194459 20954665945820418046791689)
          ·
            refine ⟨15715999459365313535093767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20954665945820418046791689 15715999459365313535093767)
            ·
              refine ⟨23573999189047970302640651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15715999459365313535093767 23573999189047970302640651)
              ·
                refine ⟨35360998783571955453960977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23573999189047970302640651 35360998783571955453960977)
                ·
                  refine ⟨26520749087678966590470733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35360998783571955453960977 26520749087678966590470733)
                  ·
                    refine ⟨9945280907879612471426525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26520749087678966590470733 9945280907879612471426525)
                    ·
                      refine ⟨3729480340454854676784947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945280907879612471426525 3729480340454854676784947)
                      ·
                        rfl

theorem cell23_7263137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_7263137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263137 prefixEnd_7263137 := by exact prefixLift 7263137
  have htrace : WordTrace (prefixWord ++ tailWord_7263137) baseStart_7263137 baseEnd_7263137 := by
    simpa [prefixWord, tailWord_7263137, baseEnd_7263137] using wordTrace_append hprefix tailTrace_7263137
  have hstable : (prefixWord ++ tailWord_7263137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263137).length < 2 ^ (prefixWord ++ tailWord_7263137).sum := by decide
  have hdescent : baseEnd_7263137 < baseStart_7263137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263160 : List Nat := [2, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4]
def baseStart_7263160 : Nat := 118140960795 + 7263160 * 2 ^ 59
def prefixEnd_7263160 : Nat := 4983230072969 + 3 ^ 40 * 7263160 * 2
def baseEnd_7263160 : Nat := 3729492150509908086797341

theorem tailTrace_7263160 : CollatzResearch.WordTrace tailWord_7263160 prefixEnd_7263160 3729492150509908086797341 := by
  unfold tailWord_7263160
  simp only [CollatzResearch.WordTrace]
  refine ⟨132454604183409621907961467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176606138911212829210615289 132454604183409621907961467)
  ·
    refine ⟨198681906275114432861942201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132454604183409621907961467 198681906275114432861942201)
    ·
      refine ⟨149011429706335824646456651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198681906275114432861942201 149011429706335824646456651)
      ·
        refine ⟨223517144559503736969684977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149011429706335824646456651 223517144559503736969684977)
        ·
          refine ⟨167637858419627802727263733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223517144559503736969684977 167637858419627802727263733)
          ·
            refine ⟨15716049226840106505680975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167637858419627802727263733 15716049226840106505680975)
            ·
              refine ⟨23574073840260159758521463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15716049226840106505680975 23574073840260159758521463)
              ·
                refine ⟨35361110760390239637782195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23574073840260159758521463 35361110760390239637782195)
                ·
                  refine ⟨53041666140585359456673293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35361110760390239637782195 53041666140585359456673293)
                  ·
                    refine ⟨19890624802719509796252485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53041666140585359456673293 19890624802719509796252485)
                    ·
                      refine ⟨3729492150509908086797341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19890624802719509796252485 3729492150509908086797341)
                      ·
                        rfl

theorem cell23_7263160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_7263160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263160 prefixEnd_7263160 := by exact prefixLift 7263160
  have htrace : WordTrace (prefixWord ++ tailWord_7263160) baseStart_7263160 baseEnd_7263160 := by
    simpa [prefixWord, tailWord_7263160, baseEnd_7263160] using wordTrace_append hprefix tailTrace_7263160
  have hstable : (prefixWord ++ tailWord_7263160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263160).length < 2 ^ (prefixWord ++ tailWord_7263160).sum := by decide
  have hdescent : baseEnd_7263160 < baseStart_7263160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263197 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_7263197 : Nat := 118140960795 + 7263197 * 2 ^ 59
def prefixEnd_7263197 : Nat := 4983230072969 + 3 ^ 40 * 7263197 * 2
def baseEnd_7263197 : Nat := 3729511149294124442034671

theorem tailTrace_7263197 : CollatzResearch.WordTrace tailWord_7263197 prefixEnd_7263197 3729511149294124442034671 := by
  unfold tailWord_7263197
  simp only [CollatzResearch.WordTrace]
  refine ⟨264910557867685199135019845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176607038578456799423346563 264910557867685199135019845)
  ·
    refine ⟨49670729600190974837816221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264910557867685199135019845 49670729600190974837816221)
    ·
      refine ⟨18626523600071615564181083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49670729600190974837816221 18626523600071615564181083)
      ·
        refine ⟨27939785400107423346271625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18626523600071615564181083 27939785400107423346271625)
        ·
          refine ⟨20954839050080567509703719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27939785400107423346271625 20954839050080567509703719)
          ·
            refine ⟨31432258575120851264555579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20954839050080567509703719 31432258575120851264555579)
            ·
              refine ⟨47148387862681276896833369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31432258575120851264555579 47148387862681276896833369)
              ·
                refine ⟨35361290897010957672625027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47148387862681276896833369 35361290897010957672625027)
                ·
                  refine ⟨53041936345516436508937541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35361290897010957672625027 53041936345516436508937541)
                  ·
                    refine ⟨9945363064784331845425789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53041936345516436508937541 9945363064784331845425789)
                    ·
                      refine ⟨3729511149294124442034671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945363064784331845425789 3729511149294124442034671)
                      ·
                        rfl

theorem cell23_7263197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_7263197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263197 prefixEnd_7263197 := by exact prefixLift 7263197
  have htrace : WordTrace (prefixWord ++ tailWord_7263197) baseStart_7263197 baseEnd_7263197 := by
    simpa [prefixWord, tailWord_7263197, baseEnd_7263197] using wordTrace_append hprefix tailTrace_7263197
  have hstable : (prefixWord ++ tailWord_7263197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263197).length < 2 ^ (prefixWord ++ tailWord_7263197).sum := by decide
  have hdescent : baseEnd_7263197 < baseStart_7263197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263244 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 3, 1, 3]
def baseStart_7263244 : Nat := 118140960795 + 7263244 * 2 ^ 59
def prefixEnd_7263244 : Nat := 4983230072969 + 3 ^ 40 * 7263244 * 2
def baseEnd_7263244 : Nat := 3729535282884885758146955

theorem tailTrace_7263244 : CollatzResearch.WordTrace tailWord_7263244 prefixEnd_7263244 3729535282884885758146955 := by
  unfold tailWord_7263244
  simp only [CollatzResearch.WordTrace]
  refine ⟨132456136049257463080990393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176608181399009950774653857 132456136049257463080990393)
  ·
    refine ⟨99342102036943097310742795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132456136049257463080990393 99342102036943097310742795)
    ·
      refine ⟨149013153055414645966114193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99342102036943097310742795 149013153055414645966114193)
      ·
        refine ⟨111759864791560984474585645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149013153055414645966114193 111759864791560984474585645)
        ·
          refine ⟨41909949296835369177969617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111759864791560984474585645 41909949296835369177969617)
          ·
            refine ⟨31432461972626526883477213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41909949296835369177969617 31432461972626526883477213)
            ·
              refine ⟨11787173239734947581303955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31432461972626526883477213 11787173239734947581303955)
              ·
                refine ⟨17680759859602421371955933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787173239734947581303955 17680759859602421371955933)
                ·
                  refine ⟨6630284947350908014483475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17680759859602421371955933 6630284947350908014483475)
                  ·
                    refine ⟨9945427421026362021725213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630284947350908014483475 9945427421026362021725213)
                    ·
                      refine ⟨3729535282884885758146955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945427421026362021725213 3729535282884885758146955)
                      ·
                        rfl

theorem cell23_7263244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 1, 3].length) (baseStart_7263244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263244 prefixEnd_7263244 := by exact prefixLift 7263244
  have htrace : WordTrace (prefixWord ++ tailWord_7263244) baseStart_7263244 baseEnd_7263244 := by
    simpa [prefixWord, tailWord_7263244, baseEnd_7263244] using wordTrace_append hprefix tailTrace_7263244
  have hstable : (prefixWord ++ tailWord_7263244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263244).length < 2 ^ (prefixWord ++ tailWord_7263244).sum := by decide
  have hdescent : baseEnd_7263244 < baseStart_7263244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263264 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 3, 5]
def baseStart_7263264 : Nat := 118140960795 + 7263264 * 2 ^ 59
def prefixEnd_7263264 : Nat := 4983230072969 + 3 ^ 40 * 7263264 * 2
def baseEnd_7263264 : Nat := 1243181850832658559965621

theorem tailTrace_7263264 : CollatzResearch.WordTrace tailWord_7263264 prefixEnd_7263264 1243181850832658559965621 := by
  unfold tailWord_7263264
  simp only [CollatzResearch.WordTrace]
  refine ⟨132456500779221234788854423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176608667705628313051805897 132456500779221234788854423)
  ·
    refine ⟨198684751168831852183281635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132456500779221234788854423 198684751168831852183281635)
    ·
      refine ⟨298027126753247778274922453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198684751168831852183281635 298027126753247778274922453)
      ·
        refine ⟨6985010783279244803318495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 298027126753247778274922453 6985010783279244803318495)
        ·
          refine ⟨10477516174918867204977743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6985010783279244803318495 10477516174918867204977743)
          ·
            refine ⟨15716274262378300807466615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10477516174918867204977743 15716274262378300807466615)
            ·
              refine ⟨23574411393567451211199923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15716274262378300807466615 23574411393567451211199923)
              ·
                refine ⟨35361617090351176816799885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23574411393567451211199923 35361617090351176816799885)
                ·
                  refine ⟨13260606408881691306299957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35361617090351176816799885 13260606408881691306299957)
                  ·
                    refine ⟨1243181850832658559965621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13260606408881691306299957 1243181850832658559965621)
                    ·
                      rfl

theorem cell23_7263264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 3, 5].length) (baseStart_7263264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263264 prefixEnd_7263264 := by exact prefixLift 7263264
  have htrace : WordTrace (prefixWord ++ tailWord_7263264) baseStart_7263264 baseEnd_7263264 := by
    simpa [prefixWord, tailWord_7263264, baseEnd_7263264] using wordTrace_append hprefix tailTrace_7263264
  have hstable : (prefixWord ++ tailWord_7263264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263264).length < 2 ^ (prefixWord ++ tailWord_7263264).sum := by decide
  have hdescent : baseEnd_7263264 < baseStart_7263264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263267 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4]
def baseStart_7263267 : Nat := 118140960795 + 7263267 * 2 ^ 59
def prefixEnd_7263267 : Nat := 4983230072969 + 3 ^ 40 * 7263267 * 2
def baseEnd_7263267 : Nat := 3729547092939939168159349

theorem tailTrace_7263267 : CollatzResearch.WordTrace tailWord_7263267 prefixEnd_7263267 3729547092939939168159349 := by
  unfold tailWord_7263267
  simp only [CollatzResearch.WordTrace]
  refine ⟨264913110977431601090068055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176608740651621067393378703 264913110977431601090068055)
  ·
    refine ⟨397369666466147401635102083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264913110977431601090068055 397369666466147401635102083)
    ·
      refine ⟨596054499699221102452653125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397369666466147401635102083 596054499699221102452653125)
      ·
        refine ⟨111760218693603956709872461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 596054499699221102452653125 111760218693603956709872461)
        ·
          refine ⟨41910082010101483766202173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111760218693603956709872461 41910082010101483766202173)
          ·
            refine ⟨15716280753788056412325815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41910082010101483766202173 15716280753788056412325815)
            ·
              refine ⟨23574421130682084618488723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15716280753788056412325815 23574421130682084618488723)
              ·
                refine ⟨35361631696023126927733085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23574421130682084618488723 35361631696023126927733085)
                ·
                  refine ⟨13260611886008672597899907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35361631696023126927733085 13260611886008672597899907)
                  ·
                    refine ⟨19890917829013008896849861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13260611886008672597899907 19890917829013008896849861)
                    ·
                      refine ⟨3729547092939939168159349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19890917829013008896849861 3729547092939939168159349)
                      ·
                        rfl

theorem cell23_7263267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_7263267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263267 prefixEnd_7263267 := by exact prefixLift 7263267
  have htrace : WordTrace (prefixWord ++ tailWord_7263267) baseStart_7263267 baseEnd_7263267 := by
    simpa [prefixWord, tailWord_7263267, baseEnd_7263267] using wordTrace_append hprefix tailTrace_7263267
  have hstable : (prefixWord ++ tailWord_7263267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263267).length < 2 ^ (prefixWord ++ tailWord_7263267).sum := by decide
  have hdescent : baseEnd_7263267 < baseStart_7263267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263271 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7263271 : Nat := 118140960795 + 7263271 * 2 ^ 59
def prefixEnd_7263271 : Nat := 4983230072969 + 3 ^ 40 * 7263271 * 2
def baseEnd_7263271 : Nat := 3729549146862557152509331

theorem tailTrace_7263271 : CollatzResearch.WordTrace tailWord_7263271 prefixEnd_7263271 3729549146862557152509331 := by
  unfold tailWord_7263271
  simp only [CollatzResearch.WordTrace]
  refine ⟨264913256869417109773213667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176608837912944739848809111 264913256869417109773213667)
  ·
    refine ⟨397369885304125664659820501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264913256869417109773213667 397369885304125664659820501)
    ·
      refine ⟨9313356686815445265464543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 397369885304125664659820501 9313356686815445265464543)
      ·
        refine ⟨13970035030223167898196815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313356686815445265464543 13970035030223167898196815)
        ·
          refine ⟨20955052545334751847295223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970035030223167898196815 20955052545334751847295223)
          ·
            refine ⟨31432578818002127770942835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955052545334751847295223 31432578818002127770942835)
            ·
              refine ⟨47148868227003191656414253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31432578818002127770942835 47148868227003191656414253)
              ·
                refine ⟨17680825585126196871155345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47148868227003191656414253 17680825585126196871155345)
                ·
                  refine ⟨13260619188844647653366509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17680825585126196871155345 13260619188844647653366509)
                  ·
                    refine ⟨4972732195816742870012441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13260619188844647653366509 4972732195816742870012441)
                    ·
                      refine ⟨3729549146862557152509331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972732195816742870012441 3729549146862557152509331)
                      ·
                        rfl

theorem cell23_7263271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7263271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263271 prefixEnd_7263271 := by exact prefixLift 7263271
  have htrace : WordTrace (prefixWord ++ tailWord_7263271) baseStart_7263271 baseEnd_7263271 := by
    simpa [prefixWord, tailWord_7263271, baseEnd_7263271] using wordTrace_append hprefix tailTrace_7263271
  have hstable : (prefixWord ++ tailWord_7263271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263271).length < 2 ^ (prefixWord ++ tailWord_7263271).sum := by decide
  have hdescent : baseEnd_7263271 < baseStart_7263271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263314 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_7263314 : Nat := 118140960795 + 7263314 * 2 ^ 59
def prefixEnd_7263314 : Nat := 4983230072969 + 3 ^ 40 * 7263314 * 2
def baseEnd_7263314 : Nat := 3729571226530700484271633

theorem tailTrace_7263314 : CollatzResearch.WordTrace tailWord_7263314 prefixEnd_7263314 3729571226530700484271633 := by
  unfold tailWord_7263314
  simp only [CollatzResearch.WordTrace]
  refine ⟨66228706302065332029257249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176609883472174218744685997 66228706302065332029257249)
  ·
    refine ⟨49671529726548999021942937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66228706302065332029257249 49671529726548999021942937)
    ·
      refine ⟨37253647294911749266457203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49671529726548999021942937 37253647294911749266457203)
      ·
        refine ⟨55880470942367623899685805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37253647294911749266457203 55880470942367623899685805)
        ·
          refine ⟨20955176603387858962382177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55880470942367623899685805 20955176603387858962382177)
          ·
            refine ⟨15716382452540894221786633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20955176603387858962382177 15716382452540894221786633)
            ·
              refine ⟨11787286839405670666339975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15716382452540894221786633 11787286839405670666339975)
              ·
                refine ⟨17680930259108505999509963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787286839405670666339975 17680930259108505999509963)
                ·
                  refine ⟨26521395388662758999264945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17680930259108505999509963 26521395388662758999264945)
                  ·
                    refine ⟨19891046541497069249448709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26521395388662758999264945 19891046541497069249448709)
                    ·
                      refine ⟨3729571226530700484271633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19891046541497069249448709 3729571226530700484271633)
                      ·
                        rfl

theorem cell23_7263314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_7263314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263314 prefixEnd_7263314 := by exact prefixLift 7263314
  have htrace : WordTrace (prefixWord ++ tailWord_7263314) baseStart_7263314 baseEnd_7263314 := by
    simpa [prefixWord, tailWord_7263314, baseEnd_7263314] using wordTrace_append hprefix tailTrace_7263314
  have hstable : (prefixWord ++ tailWord_7263314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263314).length < 2 ^ (prefixWord ++ tailWord_7263314).sum := by decide
  have hdescent : baseEnd_7263314 < baseStart_7263314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263320 : List Nat := [2, 1, 2, 2, 1, 3, 1, 2, 2, 7]
def baseStart_7263320 : Nat := 118140960795 + 7263320 * 2 ^ 59
def prefixEnd_7263320 : Nat := 4983230072969 + 3 ^ 40 * 7263320 * 2
def baseEnd_7263320 : Nat := 1243191435804875820265535

theorem tailTrace_7263320 : CollatzResearch.WordTrace tailWord_7263320 prefixEnd_7263320 1243191435804875820265535 := by
  unfold tailWord_7263320
  simp only [CollatzResearch.WordTrace]
  refine ⟨132457522023119795570873707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176610029364159727427831609 132457522023119795570873707)
  ·
    refine ⟨198686283034679693356310561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132457522023119795570873707 198686283034679693356310561)
    ·
      refine ⟨149014712276009770017232921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198686283034679693356310561 149014712276009770017232921)
      ·
        refine ⟨111761034207007327512924691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149014712276009770017232921 111761034207007327512924691)
        ·
          refine ⟨167641551310510991269387037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111761034207007327512924691 167641551310510991269387037)
          ·
            refine ⟨62865581741441621726020139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167641551310510991269387037 62865581741441621726020139)
            ·
              refine ⟨94298372612162432589030209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62865581741441621726020139 94298372612162432589030209)
              ·
                refine ⟨70723779459121824441772657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94298372612162432589030209 70723779459121824441772657)
                ·
                  refine ⟨53042834594341368331329493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70723779459121824441772657 53042834594341368331329493)
                  ·
                    refine ⟨1243191435804875820265535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53042834594341368331329493 1243191435804875820265535)
                    ·
                      rfl

theorem cell23_7263320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_7263320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263320 prefixEnd_7263320 := by exact prefixLift 7263320
  have htrace : WordTrace (prefixWord ++ tailWord_7263320) baseStart_7263320 baseEnd_7263320 := by
    simpa [prefixWord, tailWord_7263320, baseEnd_7263320] using wordTrace_append hprefix tailTrace_7263320
  have hstable : (prefixWord ++ tailWord_7263320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263320).length < 2 ^ (prefixWord ++ tailWord_7263320).sum := by decide
  have hdescent : baseEnd_7263320 < baseStart_7263320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263338 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_7263338 : Nat := 118140960795 + 7263338 * 2 ^ 59
def prefixEnd_7263338 : Nat := 4983230072969 + 3 ^ 40 * 7263338 * 2
def baseEnd_7263338 : Nat := 3729583550066408390371523

theorem tailTrace_7263338 : CollatzResearch.WordTrace tailWord_7263338 prefixEnd_7263338 3729583550066408390371523 := by
  unfold tailWord_7263338
  simp only [CollatzResearch.WordTrace]
  refine ⟨66228925140043595053975667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176610467040116253477268445 66228925140043595053975667)
  ·
    refine ⟨99343387710065392580963501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66228925140043595053975667 99343387710065392580963501)
    ·
      refine ⟨37253770391274522217861313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99343387710065392580963501 37253770391274522217861313)
      ·
        refine ⟨27940327793455891663395985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37253770391274522217861313 27940327793455891663395985)
        ·
          refine ⟨20955245845091918747546989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27940327793455891663395985 20955245845091918747546989)
          ·
            refine ⟨7858217191909469530330121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20955245845091918747546989 7858217191909469530330121)
            ·
              refine ⟨5893662893932102147747591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7858217191909469530330121 5893662893932102147747591)
              ·
                refine ⟨8840494340898153221621387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893662893932102147747591 8840494340898153221621387)
                ·
                  refine ⟨13260741511347229832432081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840494340898153221621387 13260741511347229832432081)
                  ·
                    refine ⟨9945556133510422374324061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13260741511347229832432081 9945556133510422374324061)
                    ·
                      refine ⟨3729583550066408390371523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945556133510422374324061 3729583550066408390371523)
                      ·
                        rfl

theorem cell23_7263338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_7263338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263338 prefixEnd_7263338 := by exact prefixLift 7263338
  have htrace : WordTrace (prefixWord ++ tailWord_7263338) baseStart_7263338 baseEnd_7263338 := by
    simpa [prefixWord, tailWord_7263338, baseEnd_7263338] using wordTrace_append hprefix tailTrace_7263338
  have hstable : (prefixWord ++ tailWord_7263338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263338).length < 2 ^ (prefixWord ++ tailWord_7263338).sum := by decide
  have hdescent : baseEnd_7263338 < baseStart_7263338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263368 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3]
def baseStart_7263368 : Nat := 118140960795 + 7263368 * 2 ^ 59
def prefixEnd_7263368 : Nat := 4983230072969 + 3 ^ 40 * 7263368 * 2
def baseEnd_7263368 : Nat := 3729598954486043272996385

theorem tailTrace_7263368 : CollatzResearch.WordTrace tailWord_7263368 prefixEnd_7263368 3729598954486043272996385 := by
  unfold tailWord_7263368
  simp only [CollatzResearch.WordTrace]
  refine ⟨132458397375032847669747379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176611196500043796892996505 132458397375032847669747379)
  ·
    refine ⟨198687596062549271504621069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132458397375032847669747379 198687596062549271504621069)
    ·
      refine ⟨74507848523455976814232901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 198687596062549271504621069 74507848523455976814232901)
      ·
        refine ⟨13970221598147995652668669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74507848523455976814232901 13970221598147995652668669)
        ·
          refine ⟨5238833099305498369750751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13970221598147995652668669 5238833099305498369750751)
          ·
            refine ⟨7858249648958247554626127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238833099305498369750751 7858249648958247554626127)
            ·
              refine ⟨11787374473437371331939191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858249648958247554626127 11787374473437371331939191)
              ·
                refine ⟨17681061710156056997908787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787374473437371331939191 17681061710156056997908787)
                ·
                  refine ⟨26521592565234085496863181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17681061710156056997908787 26521592565234085496863181)
                  ·
                    refine ⟨9945597211962782061323693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26521592565234085496863181 9945597211962782061323693)
                    ·
                      refine ⟨3729598954486043272996385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945597211962782061323693 3729598954486043272996385)
                      ·
                        rfl

theorem cell23_7263368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_7263368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263368 prefixEnd_7263368 := by exact prefixLift 7263368
  have htrace : WordTrace (prefixWord ++ tailWord_7263368) baseStart_7263368 baseEnd_7263368 := by
    simpa [prefixWord, tailWord_7263368, baseEnd_7263368] using wordTrace_append hprefix tailTrace_7263368
  have hstable : (prefixWord ++ tailWord_7263368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263368).length < 2 ^ (prefixWord ++ tailWord_7263368).sum := by decide
  have hdescent : baseEnd_7263368 < baseStart_7263368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263378 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_7263378 : Nat := 118140960795 + 7263378 * 2 ^ 59
def prefixEnd_7263378 : Nat := 4983230072969 + 3 ^ 40 * 7263378 * 2
def baseEnd_7263378 : Nat := 3729604089292588233871339

theorem tailTrace_7263378 : CollatzResearch.WordTrace tailWord_7263378 prefixEnd_7263378 3729604089292588233871339 := by
  unfold tailWord_7263378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66229289870007366761839697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176611439653352978031572525 66229289870007366761839697)
  ·
    refine ⟨49671967402505525071379773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66229289870007366761839697 49671967402505525071379773)
    ·
      refine ⟨18626987775939571901767415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49671967402505525071379773 18626987775939571901767415)
      ·
        refine ⟨27940481663909357852651123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18626987775939571901767415 27940481663909357852651123)
        ·
          refine ⟨41910722495864036778976685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27940481663909357852651123 41910722495864036778976685)
          ·
            refine ⟨15716520935949013792116257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41910722495864036778976685 15716520935949013792116257)
            ·
              refine ⟨11787390701961760344087193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15716520935949013792116257 11787390701961760344087193)
              ·
                refine ⟨8840543026471320258065395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11787390701961760344087193 8840543026471320258065395)
                ·
                  refine ⟨13260814539706980387098093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840543026471320258065395 13260814539706980387098093)
                  ·
                    refine ⟨4972805452390117645161785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13260814539706980387098093 4972805452390117645161785)
                    ·
                      refine ⟨3729604089292588233871339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972805452390117645161785 3729604089292588233871339)
                      ·
                        rfl

theorem cell23_7263378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_7263378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263378 prefixEnd_7263378 := by exact prefixLift 7263378
  have htrace : WordTrace (prefixWord ++ tailWord_7263378) baseStart_7263378 baseEnd_7263378 := by
    simpa [prefixWord, tailWord_7263378, baseEnd_7263378] using wordTrace_append hprefix tailTrace_7263378
  have hstable : (prefixWord ++ tailWord_7263378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263378).length < 2 ^ (prefixWord ++ tailWord_7263378).sum := by decide
  have hdescent : baseEnd_7263378 < baseStart_7263378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263407 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3]
def baseStart_7263407 : Nat := 118140960795 + 7263407 * 2 ^ 59
def prefixEnd_7263407 : Nat := 4983230072969 + 3 ^ 40 * 7263407 * 2
def baseEnd_7263407 : Nat := 3729618980231568620408705

theorem tailTrace_7263407 : CollatzResearch.WordTrace tailWord_7263407 prefixEnd_7263407 3729618980231568620408705 := by
  unfold tailWord_7263407
  simp only [CollatzResearch.WordTrace]
  refine ⟨264918217196924405000164475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176612144797949603333442983 264918217196924405000164475)
  ·
    refine ⟨397377325795386607500246713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264918217196924405000164475 397377325795386607500246713)
    ·
      refine ⟨298032994346539955625185035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397377325795386607500246713 298032994346539955625185035)
      ·
        refine ⟨447049491519809933437777553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298032994346539955625185035 447049491519809933437777553)
        ·
          refine ⟨335287118639857450078333165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447049491519809933437777553 335287118639857450078333165)
          ·
            refine ⟨125732669489946543779374937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335287118639857450078333165 125732669489946543779374937)
            ·
              refine ⟨94299502117459907834531203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125732669489946543779374937 94299502117459907834531203)
              ·
                refine ⟨141449253176189861751796805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94299502117459907834531203 141449253176189861751796805)
                ·
                  refine ⟨26521734970535599078461901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 141449253176189861751796805 26521734970535599078461901)
                  ·
                    refine ⟨9945650613950849654423213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26521734970535599078461901 9945650613950849654423213)
                    ·
                      refine ⟨3729618980231568620408705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945650613950849654423213 3729618980231568620408705)
                      ·
                        rfl

theorem cell23_7263407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 3].length) (baseStart_7263407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263407 prefixEnd_7263407 := by exact prefixLift 7263407
  have htrace : WordTrace (prefixWord ++ tailWord_7263407) baseStart_7263407 baseEnd_7263407 := by
    simpa [prefixWord, tailWord_7263407, baseEnd_7263407] using wordTrace_append hprefix tailTrace_7263407
  have hstable : (prefixWord ++ tailWord_7263407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263407).length < 2 ^ (prefixWord ++ tailWord_7263407).sum := by decide
  have hdescent : baseEnd_7263407 < baseStart_7263407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263425 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_7263425 : Nat := 118140960795 + 7263425 * 2 ^ 59
def prefixEnd_7263425 : Nat := 4983230072969 + 3 ^ 40 * 7263425 * 2
def baseEnd_7263425 : Nat := 3729628222883349549983623

theorem tailTrace_7263425 : CollatzResearch.WordTrace tailWord_7263425 prefixEnd_7263425 3729628222883349549983623 := by
  unfold tailWord_7263425
  simp only [CollatzResearch.WordTrace]
  refine ⟨264918873710859194074319729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176612582473906129382879819 264918873710859194074319729)
  ·
    refine ⟨198689155283144395555739797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264918873710859194074319729 198689155283144395555739797)
    ·
      refine ⟨9313554153897393541675303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198689155283144395555739797 9313554153897393541675303)
      ·
        refine ⟨13970331230846090312512955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313554153897393541675303 13970331230846090312512955)
        ·
          refine ⟨20955496846269135468769433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970331230846090312512955 20955496846269135468769433)
          ·
            refine ⟨15716622634701851601577075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20955496846269135468769433 15716622634701851601577075)
            ·
              refine ⟨23574933952052777402365613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15716622634701851601577075 23574933952052777402365613)
              ·
                refine ⟨8840600232019791525887105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23574933952052777402365613 8840600232019791525887105)
                ·
                  refine ⟨6630450174014843644415329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8840600232019791525887105 6630450174014843644415329)
                  ·
                    refine ⟨4972837630511132733311497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6630450174014843644415329 4972837630511132733311497)
                    ·
                      refine ⟨3729628222883349549983623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972837630511132733311497 3729628222883349549983623)
                      ·
                        rfl

theorem cell23_7263425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_7263425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263425 prefixEnd_7263425 := by exact prefixLift 7263425
  have htrace : WordTrace (prefixWord ++ tailWord_7263425) baseStart_7263425 baseEnd_7263425 := by
    simpa [prefixWord, tailWord_7263425, baseEnd_7263425] using wordTrace_append hprefix tailTrace_7263425
  have hstable : (prefixWord ++ tailWord_7263425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263425).length < 2 ^ (prefixWord ++ tailWord_7263425).sum := by decide
  have hdescent : baseEnd_7263425 < baseStart_7263425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263447 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_7263447 : Nat := 118140960795 + 7263447 * 2 ^ 59
def prefixEnd_7263447 : Nat := 4983230072969 + 3 ^ 40 * 7263447 * 2
def baseEnd_7263447 : Nat := 3729639519457748463908521

theorem tailTrace_7263447 : CollatzResearch.WordTrace tailWord_7263447 prefixEnd_7263447 3729639519457748463908521 := by
  unfold tailWord_7263447
  simp only [CollatzResearch.WordTrace]
  refine ⟨264919676116779491831620595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176613117411186327887747063 264919676116779491831620595)
  ·
    refine ⟨397379514175169237747430893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264919676116779491831620595 397379514175169237747430893)
    ·
      refine ⟨149017317815688464155286585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397379514175169237747430893 149017317815688464155286585)
      ·
        refine ⟨111762988361766348116464939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149017317815688464155286585 111762988361766348116464939)
        ·
          refine ⟨167644482542649522174697409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111762988361766348116464939 167644482542649522174697409)
          ·
            refine ⟨125733361906987141631023057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167644482542649522174697409 125733361906987141631023057)
            ·
              refine ⟨94300021430240356223267293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125733361906987141631023057 94300021430240356223267293)
              ·
                refine ⟨35362508036340133583725235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94300021430240356223267293 35362508036340133583725235)
                ·
                  refine ⟨53043762054510200375587853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35362508036340133583725235 53043762054510200375587853)
                  ·
                    refine ⟨19891410770441325140845445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53043762054510200375587853 19891410770441325140845445)
                    ·
                      refine ⟨3729639519457748463908521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19891410770441325140845445 3729639519457748463908521)
                      ·
                        rfl

theorem cell23_7263447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_7263447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263447 prefixEnd_7263447 := by exact prefixLift 7263447
  have htrace : WordTrace (prefixWord ++ tailWord_7263447) baseStart_7263447 baseEnd_7263447 := by
    simpa [prefixWord, tailWord_7263447, baseEnd_7263447] using wordTrace_append hprefix tailTrace_7263447
  have hstable : (prefixWord ++ tailWord_7263447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263447).length < 2 ^ (prefixWord ++ tailWord_7263447).sum := by decide
  have hdescent : baseEnd_7263447 < baseStart_7263447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263464 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_7263464 : Nat := 118140960795 + 7263464 * 2 ^ 59
def prefixEnd_7263464 : Nat := 4983230072969 + 3 ^ 40 * 7263464 * 2
def baseEnd_7263464 : Nat := 3729648248628874897395943

theorem tailTrace_7263464 : CollatzResearch.WordTrace tailWord_7263464 prefixEnd_7263464 3729648248628874897395943 := by
  unfold tailWord_7263464
  simp only [CollatzResearch.WordTrace]
  refine ⟨132460148078858951867494723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176613530771811935823326297 132460148078858951867494723)
  ·
    refine ⟨198690222118288427801242085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132460148078858951867494723 198690222118288427801242085)
    ·
      refine ⟨37254416647179080212732891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 198690222118288427801242085 37254416647179080212732891)
      ·
        refine ⟨55881624970768620319099337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37254416647179080212732891 55881624970768620319099337)
        ·
          refine ⟨41911218728076465239324503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55881624970768620319099337 41911218728076465239324503)
          ·
            refine ⟨62866828092114697858986755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41911218728076465239324503 62866828092114697858986755)
            ·
              refine ⟨94300242138172046788480133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62866828092114697858986755 94300242138172046788480133)
              ·
                refine ⟨17681295400907258772840025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94300242138172046788480133 17681295400907258772840025)
                ·
                  refine ⟨13260971550680444079630019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17681295400907258772840025 13260971550680444079630019)
                  ·
                    refine ⟨19891457326020666119445029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13260971550680444079630019 19891457326020666119445029)
                    ·
                      refine ⟨3729648248628874897395943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19891457326020666119445029 3729648248628874897395943)
                      ·
                        rfl

theorem cell23_7263464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_7263464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263464 prefixEnd_7263464 := by exact prefixLift 7263464
  have htrace : WordTrace (prefixWord ++ tailWord_7263464) baseStart_7263464 baseEnd_7263464 := by
    simpa [prefixWord, tailWord_7263464, baseEnd_7263464] using wordTrace_append hprefix tailTrace_7263464
  have hstable : (prefixWord ++ tailWord_7263464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263464).length < 2 ^ (prefixWord ++ tailWord_7263464).sum := by decide
  have hdescent : baseEnd_7263464 < baseStart_7263464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263541 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_7263541 : Nat := 118140960795 + 7263541 * 2 ^ 59
def prefixEnd_7263541 : Nat := 4983230072969 + 3 ^ 40 * 7263541 * 2
def baseEnd_7263541 : Nat := 3729687786639271096133089

theorem tailTrace_7263541 : CollatzResearch.WordTrace tailWord_7263541 prefixEnd_7263541 3729687786639271096133089 := by
  unfold tailWord_7263541
  simp only [CollatzResearch.WordTrace]
  refine ⟨264923104578438945885542477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176615403052292630590361651 264923104578438945885542477)
  ·
    refine ⟨99346164216914604707078429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264923104578438945885542477 99346164216914604707078429)
    ·
      refine ⟨37254811581342976765154411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99346164216914604707078429 37254811581342976765154411)
      ·
        refine ⟨55882217372014465147731617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37254811581342976765154411 55882217372014465147731617)
        ·
          refine ⟨41911663029010848860798713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55882217372014465147731617 41911663029010848860798713)
          ·
            refine ⟨31433747271758136645599035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41911663029010848860798713 31433747271758136645599035)
            ·
              refine ⟨47150620907637204968398553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31433747271758136645599035 47150620907637204968398553)
              ·
                refine ⟨35362965680727903726298915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47150620907637204968398553 35362965680727903726298915)
                ·
                  refine ⟨53044448521091855589448373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35362965680727903726298915 53044448521091855589448373)
                  ·
                    refine ⟨4972917048852361461510785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53044448521091855589448373 4972917048852361461510785)
                    ·
                      refine ⟨3729687786639271096133089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4972917048852361461510785 3729687786639271096133089)
                      ·
                        rfl

theorem cell23_7263541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_7263541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263541 prefixEnd_7263541 := by exact prefixLift 7263541
  have htrace : WordTrace (prefixWord ++ tailWord_7263541) baseStart_7263541 baseEnd_7263541 := by
    simpa [prefixWord, tailWord_7263541, baseEnd_7263541] using wordTrace_append hprefix tailTrace_7263541
  have hstable : (prefixWord ++ tailWord_7263541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263541).length < 2 ^ (prefixWord ++ tailWord_7263541).sum := by decide
  have hdescent : baseEnd_7263541 < baseStart_7263541 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263551 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 1, 5]
def baseStart_7263551 : Nat := 118140960795 + 7263551 * 2 ^ 59
def prefixEnd_7263551 : Nat := 4983230072969 + 3 ^ 40 * 7263551 * 2
def baseEnd_7263551 : Nat := 1243230973815272019002681

theorem tailTrace_7263551 : CollatzResearch.WordTrace tailWord_7263551 prefixEnd_7263551 1243230973815272019002681 := by
  unfold tailWord_7263551
  simp only [CollatzResearch.WordTrace]
  refine ⟨264923469308402717593406507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176615646205601811728937671 264923469308402717593406507)
  ·
    refine ⟨397385203962604076390109761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264923469308402717593406507 397385203962604076390109761)
    ·
      refine ⟨298038902971953057292582321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397385203962604076390109761 298038902971953057292582321)
      ·
        refine ⟨223529177228964792969436741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298038902971953057292582321 223529177228964792969436741)
        ·
          refine ⟨41911720730430898681769389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 223529177228964792969436741 41911720730430898681769389)
          ·
            refine ⟨15716895273911587005663521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41911720730430898681769389 15716895273911587005663521)
            ·
              refine ⟨11787671455433690254247641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15716895273911587005663521 11787671455433690254247641)
              ·
                refine ⟨8840753591575267690685731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11787671455433690254247641 8840753591575267690685731)
                ·
                  refine ⟨13261130387362901536028597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840753591575267690685731 13261130387362901536028597)
                  ·
                    refine ⟨1243230973815272019002681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13261130387362901536028597 1243230973815272019002681)
                    ·
                      rfl

theorem cell23_7263551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 5].length) (baseStart_7263551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263551 prefixEnd_7263551 := by exact prefixLift 7263551
  have htrace : WordTrace (prefixWord ++ tailWord_7263551) baseStart_7263551 baseEnd_7263551 := by
    simpa [prefixWord, tailWord_7263551, baseEnd_7263551] using wordTrace_append hprefix tailTrace_7263551
  have hstable : (prefixWord ++ tailWord_7263551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263551).length < 2 ^ (prefixWord ++ tailWord_7263551).sum := by decide
  have hdescent : baseEnd_7263551 < baseStart_7263551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263577 : List Nat := [1, 2, 1, 2, 2, 2, 13]
def baseStart_7263577 : Nat := 118140960795 + 7263577 * 2 ^ 59
def prefixEnd_7263577 : Nat := 4983230072969 + 3 ^ 40 * 7263577 * 2
def baseEnd_7263577 : Nat := 46045756443738678460283

theorem tailTrace_7263577 : CollatzResearch.WordTrace tailWord_7263577 prefixEnd_7263577 46045756443738678460283 := by
  unfold tailWord_7263577
  simp only [CollatzResearch.WordTrace]
  refine ⟨264924417606308524033852985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176616278404205682689235323 264924417606308524033852985)
  ·
    refine ⟨198693313204731393025389739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264924417606308524033852985 198693313204731393025389739)
    ·
      refine ⟨298039969807097089538084609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198693313204731393025389739 298039969807097089538084609)
      ·
        refine ⟨223529977355322817153563457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298039969807097089538084609 223529977355322817153563457)
        ·
          refine ⟨167647483016492112865172593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223529977355322817153563457 167647483016492112865172593)
          ·
            refine ⟨125735612262369084648879445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167647483016492112865172593 125735612262369084648879445)
            ·
              refine ⟨46045756443738678460283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 125735612262369084648879445 46045756443738678460283)
              ·
                rfl

theorem cell23_7263577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 13].length) (baseStart_7263577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263577 prefixEnd_7263577 := by exact prefixLift 7263577
  have htrace : WordTrace (prefixWord ++ tailWord_7263577) baseStart_7263577 baseEnd_7263577 := by
    simpa [prefixWord, tailWord_7263577, baseEnd_7263577] using wordTrace_append hprefix tailTrace_7263577
  have hstable : (prefixWord ++ tailWord_7263577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263577).length < 2 ^ (prefixWord ++ tailWord_7263577).sum := by decide
  have hdescent : baseEnd_7263577 < baseStart_7263577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263584 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6]
def baseStart_7263584 : Nat := 118140960795 + 7263584 * 2 ^ 59
def prefixEnd_7263584 : Nat := 4983230072969 + 3 ^ 40 * 7263584 * 2
def baseEnd_7263584 : Nat := 3729709866307414427895391

theorem tailTrace_7263584 : CollatzResearch.WordTrace tailWord_7263584 prefixEnd_7263584 3729709866307414427895391 := by
  unfold tailWord_7263584
  simp only [CollatzResearch.WordTrace]
  refine ⟨132462336458641582114678903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176616448611522109486238537 132462336458641582114678903)
  ·
    refine ⟨198693504687962373172018355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132462336458641582114678903 198693504687962373172018355)
    ·
      refine ⟨298040257031943559758027533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198693504687962373172018355 298040257031943559758027533)
      ·
        refine ⟨111765096386978834909260325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298040257031943559758027533 111765096386978834909260325)
        ·
          refine ⟨20955955572558531545486311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111765096386978834909260325 20955955572558531545486311)
          ·
            refine ⟨31433933358837797318229467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20955955572558531545486311 31433933358837797318229467)
            ·
              refine ⟨47150900038256695977344201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31433933358837797318229467 47150900038256695977344201)
              ·
                refine ⟨35363175028692521983008151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47150900038256695977344201 35363175028692521983008151)
                ·
                  refine ⟨53044762543038782974512227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35363175028692521983008151 53044762543038782974512227)
                  ·
                    refine ⟨79567143814558174461768341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53044762543038782974512227 79567143814558174461768341)
                    ·
                      refine ⟨3729709866307414427895391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 79567143814558174461768341 3729709866307414427895391)
                      ·
                        rfl

theorem cell23_7263584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_7263584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263584 prefixEnd_7263584 := by exact prefixLift 7263584
  have htrace : WordTrace (prefixWord ++ tailWord_7263584) baseStart_7263584 baseEnd_7263584 := by
    simpa [prefixWord, tailWord_7263584, baseEnd_7263584] using wordTrace_append hprefix tailTrace_7263584
  have hstable : (prefixWord ++ tailWord_7263584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263584).length < 2 ^ (prefixWord ++ tailWord_7263584).sum := by decide
  have hdescent : baseEnd_7263584 < baseStart_7263584 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263605 : List Nat := [1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7263605 : Nat := 118140960795 + 7263605 * 2 ^ 59
def prefixEnd_7263605 : Nat := 4983230072969 + 3 ^ 40 * 7263605 * 2
def baseEnd_7263605 : Nat := 3729720649401158845732795

theorem tailTrace_7263605 : CollatzResearch.WordTrace tailWord_7263605 prefixEnd_7263605 3729720649401158845732795 := by
  unfold tailWord_7263605
  simp only [CollatzResearch.WordTrace]
  refine ⟨264925438850207084815872269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176616959233471389877248179 264925438850207084815872269)
  ·
    refine ⟨99347039568827656805952101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264925438850207084815872269 99347039568827656805952101)
    ·
      refine ⟨18627569919155185651116019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99347039568827656805952101 18627569919155185651116019)
      ·
        refine ⟨27941354878732778476674029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18627569919155185651116019 27941354878732778476674029)
        ·
          refine ⟨10478008079524791928752761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27941354878732778476674029 10478008079524791928752761)
          ·
            refine ⟨7858506059643593946564571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10478008079524791928752761 7858506059643593946564571)
            ·
              refine ⟨11787759089465390919846857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858506059643593946564571 11787759089465390919846857)
              ·
                refine ⟨8840819317099043189885143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11787759089465390919846857 8840819317099043189885143)
                ·
                  refine ⟨13261228975648564784827715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840819317099043189885143 13261228975648564784827715)
                  ·
                    refine ⟨19891843463472847177241573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13261228975648564784827715 19891843463472847177241573)
                    ·
                      refine ⟨3729720649401158845732795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19891843463472847177241573 3729720649401158845732795)
                      ·
                        rfl

theorem cell23_7263605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7263605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263605 prefixEnd_7263605 := by exact prefixLift 7263605
  have htrace : WordTrace (prefixWord ++ tailWord_7263605) baseStart_7263605 baseEnd_7263605 := by
    simpa [prefixWord, tailWord_7263605, baseEnd_7263605] using wordTrace_append hprefix tailTrace_7263605
  have hstable : (prefixWord ++ tailWord_7263605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263605).length < 2 ^ (prefixWord ++ tailWord_7263605).sum := by decide
  have hdescent : baseEnd_7263605 < baseStart_7263605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263618 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_7263618 : Nat := 118140960795 + 7263618 * 2 ^ 59
def prefixEnd_7263618 : Nat := 4983230072969 + 3 ^ 40 * 7263618 * 2
def baseEnd_7263618 : Nat := 3729727324649667294870235

theorem tailTrace_7263618 : CollatzResearch.WordTrace tailWord_7263618 prefixEnd_7263618 3729727324649667294870235 := by
  unfold tailWord_7263618
  simp only [CollatzResearch.WordTrace]
  refine ⟨66231478249789997009023877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176617275332773325357397005 66231478249789997009023877)
  ·
    refine ⟨12418402171835624439191977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66231478249789997009023877 12418402171835624439191977)
    ·
      refine ⟨9313801628876718329393983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12418402171835624439191977 9313801628876718329393983)
      ·
        refine ⟨13970702443315077494090975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9313801628876718329393983 13970702443315077494090975)
        ·
          refine ⟨20956053664972616241136463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13970702443315077494090975 20956053664972616241136463)
          ·
            refine ⟨31434080497458924361704695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20956053664972616241136463 31434080497458924361704695)
            ·
              refine ⟨47151120746188386542557043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31434080497458924361704695 47151120746188386542557043)
              ·
                refine ⟨70726681119282579813835565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47151120746188386542557043 70726681119282579813835565)
                ·
                  refine ⟨26522505419730967430188337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70726681119282579813835565 26522505419730967430188337)
                  ·
                    refine ⟨19891879064798225572641253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26522505419730967430188337 19891879064798225572641253)
                    ·
                      refine ⟨3729727324649667294870235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19891879064798225572641253 3729727324649667294870235)
                      ·
                        rfl

theorem cell23_7263618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_7263618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263618 prefixEnd_7263618 := by exact prefixLift 7263618
  have htrace : WordTrace (prefixWord ++ tailWord_7263618) baseStart_7263618 baseEnd_7263618 := by
    simpa [prefixWord, tailWord_7263618, baseEnd_7263618] using wordTrace_append hprefix tailTrace_7263618
  have hstable : (prefixWord ++ tailWord_7263618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263618).length < 2 ^ (prefixWord ++ tailWord_7263618).sum := by decide
  have hdescent : baseEnd_7263618 < baseStart_7263618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263621 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 3]
def baseStart_7263621 : Nat := 118140960795 + 7263621 * 2 ^ 59
def prefixEnd_7263621 : Nat := 4983230072969 + 3 ^ 40 * 7263621 * 2
def baseEnd_7263621 : Nat := 3729728865091630783132721

theorem tailTrace_7263621 : CollatzResearch.WordTrace tailWord_7263621 prefixEnd_7263621 3729728865091630783132721 := by
  unfold tailWord_7263621
  simp only [CollatzResearch.WordTrace]
  refine ⟨264926022418149119548454717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176617348278766079698969811 264926022418149119548454717)
  ·
    refine ⟨99347258406805919830670519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264926022418149119548454717 99347258406805919830670519)
    ·
      refine ⟨149020887610208879746005779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99347258406805919830670519 149020887610208879746005779)
      ·
        refine ⟨223531331415313319619008669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149020887610208879746005779 223531331415313319619008669)
        ·
          refine ⟨83824249280742494857128251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 223531331415313319619008669 83824249280742494857128251)
          ·
            refine ⟨125736373921113742285692377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83824249280742494857128251 125736373921113742285692377)
            ·
              refine ⟨94302280440835306714269283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125736373921113742285692377 94302280440835306714269283)
              ·
                refine ⟨141453420661252960071403925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94302280440835306714269283 141453420661252960071403925)
                ·
                  refine ⟨6630629093496232503347059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 141453420661252960071403925 6630629093496232503347059)
                  ·
                    refine ⟨9945943640244348755020589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630629093496232503347059 9945943640244348755020589)
                    ·
                      refine ⟨3729728865091630783132721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945943640244348755020589 3729728865091630783132721)
                      ·
                        rfl

theorem cell23_7263621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 3].length) (baseStart_7263621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263621 prefixEnd_7263621 := by exact prefixLift 7263621
  have htrace : WordTrace (prefixWord ++ tailWord_7263621) baseStart_7263621 baseEnd_7263621 := by
    simpa [prefixWord, tailWord_7263621, baseEnd_7263621] using wordTrace_append hprefix tailTrace_7263621
  have hstable : (prefixWord ++ tailWord_7263621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263621).length < 2 ^ (prefixWord ++ tailWord_7263621).sum := by decide
  have hdescent : baseEnd_7263621 < baseStart_7263621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263625 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 1, 2, 3]
def baseStart_7263625 : Nat := 118140960795 + 7263625 * 2 ^ 59
def prefixEnd_7263625 : Nat := 4983230072969 + 3 ^ 40 * 7263625 * 2
def baseEnd_7263625 : Nat := 3729730919014248767482703

theorem tailTrace_7263625 : CollatzResearch.WordTrace tailWord_7263625 prefixEnd_7263625 3729730919014248767482703 := by
  unfold tailWord_7263625
  simp only [CollatzResearch.WordTrace]
  refine ⟨264926168310134628231600329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176617445540089752154400219 264926168310134628231600329)
  ·
    refine ⟨198694626232600971173700247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264926168310134628231600329 198694626232600971173700247)
    ·
      refine ⟨298041939348901456760550371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198694626232600971173700247 298041939348901456760550371)
      ·
        refine ⟨447062909023352185140825557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298041939348901456760550371 447062909023352185140825557)
        ·
          refine ⟨10478036930234816839238099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 447062909023352185140825557 10478036930234816839238099)
          ·
            refine ⟨15717055395352225258857149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478036930234816839238099 15717055395352225258857149)
            ·
              refine ⟨5893895773257084472071431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15717055395352225258857149 5893895773257084472071431)
              ·
                refine ⟨8840843659885626708107147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5893895773257084472071431 8840843659885626708107147)
                ·
                  refine ⟨13261265489828440062160721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8840843659885626708107147 13261265489828440062160721)
                  ·
                    refine ⟨9945949117371330046620541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13261265489828440062160721 9945949117371330046620541)
                    ·
                      refine ⟨3729730919014248767482703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9945949117371330046620541 3729730919014248767482703)
                      ·
                        rfl

theorem cell23_7263625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 2, 3].length) (baseStart_7263625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263625 prefixEnd_7263625 := by exact prefixLift 7263625
  have htrace : WordTrace (prefixWord ++ tailWord_7263625) baseStart_7263625 baseEnd_7263625 := by
    simpa [prefixWord, tailWord_7263625, baseEnd_7263625] using wordTrace_append hprefix tailTrace_7263625
  have hstable : (prefixWord ++ tailWord_7263625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263625).length < 2 ^ (prefixWord ++ tailWord_7263625).sum := by decide
  have hdescent : baseEnd_7263625 < baseStart_7263625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263664 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5]
def baseStart_7263664 : Nat := 118140960795 + 7263664 * 2 ^ 59
def prefixEnd_7263664 : Nat := 4983230072969 + 3 ^ 40 * 7263664 * 2
def baseEnd_7263664 : Nat := 3729750944759774114895023

theorem tailTrace_7263664 : CollatzResearch.WordTrace tailWord_7263664 prefixEnd_7263664 3729750944759774114895023 := by
  unfold tailWord_7263664
  simp only [CollatzResearch.WordTrace]
  refine ⟨132463795378496668946135023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176618393837995558594846697 132463795378496668946135023)
  ·
    refine ⟨198695693067745003419202535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132463795378496668946135023 198695693067745003419202535)
    ·
      refine ⟨298043539601617505128803803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198695693067745003419202535 298043539601617505128803803)
      ·
        refine ⟨447065309402426257693205705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298043539601617505128803803 447065309402426257693205705)
        ·
          refine ⟨335298982051819693269904279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447065309402426257693205705 335298982051819693269904279)
          ·
            refine ⟨502948473077729539904856419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335298982051819693269904279 502948473077729539904856419)
            ·
              refine ⟨754422709616594309857284629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502948473077729539904856419 754422709616594309857284629)
              ·
                refine ⟨35363564513277858274560217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 754422709616594309857284629 35363564513277858274560217)
                ·
                  refine ⟨26522673384958393705920163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35363564513277858274560217 26522673384958393705920163)
                  ·
                    refine ⟨39784010077437590558880245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26522673384958393705920163 39784010077437590558880245)
                    ·
                      refine ⟨3729750944759774114895023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39784010077437590558880245 3729750944759774114895023)
                      ·
                        rfl

theorem cell23_7263664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_7263664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263664 prefixEnd_7263664 := by exact prefixLift 7263664
  have htrace : WordTrace (prefixWord ++ tailWord_7263664) baseStart_7263664 baseEnd_7263664 := by
    simpa [prefixWord, tailWord_7263664, baseEnd_7263664] using wordTrace_append hprefix tailTrace_7263664
  have hstable : (prefixWord ++ tailWord_7263664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263664).length < 2 ^ (prefixWord ++ tailWord_7263664).sum := by decide
  have hdescent : baseEnd_7263664 < baseStart_7263664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263695 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 2, 2, 2]
def baseStart_7263695 : Nat := 118140960795 + 7263695 * 2 ^ 59
def prefixEnd_7263695 : Nat := 4983230072969 + 3 ^ 40 * 7263695 * 2
def baseEnd_7263695 : Nat := 3729766862660063493607381

theorem tailTrace_7263695 : CollatzResearch.WordTrace tailWord_7263695 prefixEnd_7263695 3729766862660063493607381 := by
  unfold tailWord_7263695
  simp only [CollatzResearch.WordTrace]
  refine ⟨264928721419881030186648539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176619147613254020124432359 264928721419881030186648539)
  ·
    refine ⟨397393082129821545279972809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264928721419881030186648539 397393082129821545279972809)
    ·
      refine ⟨298044811597366158959979607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397393082129821545279972809 298044811597366158959979607)
      ·
        refine ⟨447067217396049238439969411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298044811597366158959979607 447067217396049238439969411)
        ·
          refine ⟨670600826094073857659954117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447067217396049238439969411 670600826094073857659954117)
          ·
            refine ⟨125737654892638848311241397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 670600826094073857659954117 125737654892638848311241397)
            ·
              refine ⟨11787905146184892029178881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125737654892638848311241397 11787905146184892029178881)
              ·
                refine ⟨8840928859638669021884161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11787905146184892029178881 8840928859638669021884161)
                ·
                  refine ⟨6630696644729001766413121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8840928859638669021884161 6630696644729001766413121)
                  ·
                    refine ⟨4973022483546751324809841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6630696644729001766413121 4973022483546751324809841)
                    ·
                      refine ⟨3729766862660063493607381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973022483546751324809841 3729766862660063493607381)
                      ·
                        rfl

theorem cell23_7263695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 2, 2, 2].length) (baseStart_7263695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263695 prefixEnd_7263695 := by exact prefixLift 7263695
  have htrace : WordTrace (prefixWord ++ tailWord_7263695) baseStart_7263695 baseEnd_7263695 := by
    simpa [prefixWord, tailWord_7263695, baseEnd_7263695] using wordTrace_append hprefix tailTrace_7263695
  have hstable : (prefixWord ++ tailWord_7263695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263695).length < 2 ^ (prefixWord ++ tailWord_7263695).sum := by decide
  have hdescent : baseEnd_7263695 < baseStart_7263695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263701 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 7]
def baseStart_7263701 : Nat := 118140960795 + 7263701 * 2 ^ 59
def prefixEnd_7263701 : Nat := 4983230072969 + 3 ^ 40 * 7263701 * 2
def baseEnd_7263701 : Nat := 414418882615998941125817

theorem tailTrace_7263701 : CollatzResearch.WordTrace tailWord_7263701 prefixEnd_7263701 414418882615998941125817 := by
  unfold tailWord_7263701
  simp only [CollatzResearch.WordTrace]
  refine ⟨264928940257859293211366957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176619293505239528807577971 264928940257859293211366957)
  ·
    refine ⟨99348352596697234954262609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264928940257859293211366957 99348352596697234954262609)
    ·
      refine ⟨74511264447522926215696957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99348352596697234954262609 74511264447522926215696957)
      ·
        refine ⟨27941724167821097330886359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74511264447522926215696957 27941724167821097330886359)
        ·
          refine ⟨41912586251731645996329539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27941724167821097330886359 41912586251731645996329539)
          ·
            refine ⟨62868879377597468994494309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41912586251731645996329539 62868879377597468994494309)
            ·
              refine ⟨11787914883299525436467683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62868879377597468994494309 11787914883299525436467683)
              ·
                refine ⟨17681872324949288154701525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11787914883299525436467683 17681872324949288154701525)
                ·
                  refine ⟨414418882615998941125817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17681872324949288154701525 414418882615998941125817)
                  ·
                    rfl

theorem cell23_7263701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_7263701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263701 prefixEnd_7263701 := by exact prefixLift 7263701
  have htrace : WordTrace (prefixWord ++ tailWord_7263701) baseStart_7263701 baseEnd_7263701 := by
    simpa [prefixWord, tailWord_7263701, baseEnd_7263701] using wordTrace_append hprefix tailTrace_7263701
  have hstable : (prefixWord ++ tailWord_7263701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263701).length < 2 ^ (prefixWord ++ tailWord_7263701).sum := by decide
  have hdescent : baseEnd_7263701 < baseStart_7263701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263711 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3]
def baseStart_7263711 : Nat := 118140960795 + 7263711 * 2 ^ 59
def prefixEnd_7263711 : Nat := 4983230072969 + 3 ^ 40 * 7263711 * 2
def baseEnd_7263711 : Nat := 3729775078350535431007307

theorem tailTrace_7263711 : CollatzResearch.WordTrace tailWord_7263711 prefixEnd_7263711 3729775078350535431007307 := by
  unfold tailWord_7263711
  simp only [CollatzResearch.WordTrace]
  refine ⟨264929304987823064919230987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176619536658548709946153991 264929304987823064919230987)
  ·
    refine ⟨397393957481734597378846481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264929304987823064919230987 397393957481734597378846481)
    ·
      refine ⟨298045468111300948034134861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397393957481734597378846481 298045468111300948034134861)
      ·
        refine ⟨111767050541737855512800573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298045468111300948034134861 111767050541737855512800573)
        ·
          refine ⟨41912643953151695817300215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111767050541737855512800573 41912643953151695817300215)
          ·
            refine ⟨62868965929727543725950323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41912643953151695817300215 62868965929727543725950323)
            ·
              refine ⟨94303448894591315588925485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62868965929727543725950323 94303448894591315588925485)
              ·
                refine ⟨35363793335471743345847057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94303448894591315588925485 35363793335471743345847057)
                ·
                  refine ⟨26522845001603807509385293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35363793335471743345847057 26522845001603807509385293)
                  ·
                    refine ⟨9946066875601427816019485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26522845001603807509385293 9946066875601427816019485)
                    ·
                      refine ⟨3729775078350535431007307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9946066875601427816019485 3729775078350535431007307)
                      ·
                        rfl

theorem cell23_7263711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_7263711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263711 prefixEnd_7263711 := by exact prefixLift 7263711
  have htrace : WordTrace (prefixWord ++ tailWord_7263711) baseStart_7263711 baseEnd_7263711 := by
    simpa [prefixWord, tailWord_7263711, baseEnd_7263711] using wordTrace_append hprefix tailTrace_7263711
  have hstable : (prefixWord ++ tailWord_7263711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263711).length < 2 ^ (prefixWord ++ tailWord_7263711).sum := by decide
  have hdescent : baseEnd_7263711 < baseStart_7263711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263721 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 7, 2]
def baseStart_7263721 : Nat := 118140960795 + 7263721 * 2 ^ 59
def prefixEnd_7263721 : Nat := 4983230072969 + 3 ^ 40 * 7263721 * 2
def baseEnd_7263721 : Nat := 3729780213157080391882261

theorem tailTrace_7263721 : CollatzResearch.WordTrace tailWord_7263721 prefixEnd_7263721 3729780213157080391882261 := by
  unfold tailWord_7263721
  simp only [CollatzResearch.WordTrace]
  refine ⟨264929669717786836627095017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176619779811857891084730011 264929669717786836627095017)
  ·
    refine ⟨198697252288340127470321263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264929669717786836627095017 198697252288340127470321263)
    ·
      refine ⟨298045878432510191205481895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198697252288340127470321263 298045878432510191205481895)
      ·
        refine ⟨447068817648765286808222843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298045878432510191205481895 447068817648765286808222843)
        ·
          refine ⟨670603226473147930212334265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 447068817648765286808222843 670603226473147930212334265)
          ·
            refine ⟨502952419854860947659250699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670603226473147930212334265 502952419854860947659250699)
            ·
              refine ⟨754428629782291421488876049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 502952419854860947659250699 754428629782291421488876049)
              ·
                refine ⟨565821472336718566116657037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 754428629782291421488876049 565821472336718566116657037)
                ·
                  refine ⟨212183052126269462293746389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 565821472336718566116657037 212183052126269462293746389)
                  ·
                    refine ⟨4973040284209440522509681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 212183052126269462293746389 4973040284209440522509681)
                    ·
                      refine ⟨3729780213157080391882261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973040284209440522509681 3729780213157080391882261)
                      ·
                        rfl

theorem cell23_7263721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 7, 2].length) (baseStart_7263721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263721 prefixEnd_7263721 := by exact prefixLift 7263721
  have htrace : WordTrace (prefixWord ++ tailWord_7263721) baseStart_7263721 baseEnd_7263721 := by
    simpa [prefixWord, tailWord_7263721, baseEnd_7263721] using wordTrace_append hprefix tailTrace_7263721
  have hstable : (prefixWord ++ tailWord_7263721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263721).length < 2 ^ (prefixWord ++ tailWord_7263721).sum := by decide
  have hdescent : baseEnd_7263721 < baseStart_7263721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263724 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 7]
def baseStart_7263724 : Nat := 118140960795 + 7263724 * 2 ^ 59
def prefixEnd_7263724 : Nat := 4983230072969 + 3 ^ 40 * 7263724 * 2
def baseEnd_7263724 : Nat := 3729781753599043880144747

theorem tailTrace_7263724 : CollatzResearch.WordTrace tailWord_7263724 prefixEnd_7263724 3729781753599043880144747 := by
  unfold tailWord_7263724
  simp only [CollatzResearch.WordTrace]
  refine ⟨132464889568387984069727113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176619852757850645426302817 132464889568387984069727113)
  ·
    refine ⟨99348667176290988052295335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132464889568387984069727113 99348667176290988052295335)
    ·
      refine ⟨149023000764436482078443003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99348667176290988052295335 149023000764436482078443003)
      ·
        refine ⟨223534501146654723117664505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149023000764436482078443003 223534501146654723117664505)
        ·
          refine ⟨167650875859991042338248379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223534501146654723117664505 167650875859991042338248379)
          ·
            refine ⟨251476313789986563507372569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167650875859991042338248379 251476313789986563507372569)
            ·
              refine ⟨188607235342489922630529427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251476313789986563507372569 188607235342489922630529427)
              ·
                refine ⟨282910853013734883945794141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 188607235342489922630529427 282910853013734883945794141)
                ·
                  refine ⟨106091569880150581479672803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282910853013734883945794141 106091569880150581479672803)
                  ·
                    refine ⟨159137354820225872219509205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106091569880150581479672803 159137354820225872219509205)
                    ·
                      refine ⟨3729781753599043880144747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159137354820225872219509205 3729781753599043880144747)
                      ·
                        rfl

theorem cell23_7263724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_7263724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263724 prefixEnd_7263724 := by exact prefixLift 7263724
  have htrace : WordTrace (prefixWord ++ tailWord_7263724) baseStart_7263724 baseEnd_7263724 := by
    simpa [prefixWord, tailWord_7263724, baseEnd_7263724] using wordTrace_append hprefix tailTrace_7263724
  have hstable : (prefixWord ++ tailWord_7263724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263724).length < 2 ^ (prefixWord ++ tailWord_7263724).sum := by decide
  have hdescent : baseEnd_7263724 < baseStart_7263724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263758 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_7263758 : Nat := 118140960795 + 7263758 * 2 ^ 59
def prefixEnd_7263758 : Nat := 4983230072969 + 3 ^ 40 * 7263758 * 2
def baseEnd_7263758 : Nat := 3729799211941296747119591

theorem tailTrace_7263758 : CollatzResearch.WordTrace tailWord_7263758 prefixEnd_7263758 3729799211941296747119591 := by
  unfold tailWord_7263758
  simp only [CollatzResearch.WordTrace]
  refine ⟨33116377402331598993273991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176620679479101861297461285 33116377402331598993273991)
  ·
    refine ⟨49674566103497398489910987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33116377402331598993273991 49674566103497398489910987)
    ·
      refine ⟨74511849155246097734866481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49674566103497398489910987 74511849155246097734866481)
      ·
        refine ⟨55883886866434573301149861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74511849155246097734866481 55883886866434573301149861)
        ·
          refine ⟨10478228787456482493965599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55883886866434573301149861 10478228787456482493965599)
          ·
            refine ⟨15717343181184723740948399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478228787456482493965599 15717343181184723740948399)
            ·
              refine ⟨23576014771777085611422599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717343181184723740948399 23576014771777085611422599)
              ·
                refine ⟨35364022157665628417133899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23576014771777085611422599 35364022157665628417133899)
                ·
                  refine ⟨53046033236498442625700849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35364022157665628417133899 53046033236498442625700849)
                  ·
                    refine ⟨39784524927373831969275637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53046033236498442625700849 39784524927373831969275637)
                    ·
                      refine ⟨3729799211941296747119591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39784524927373831969275637 3729799211941296747119591)
                      ·
                        rfl

theorem cell23_7263758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_7263758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263758 prefixEnd_7263758 := by exact prefixLift 7263758
  have htrace : WordTrace (prefixWord ++ tailWord_7263758) baseStart_7263758 baseEnd_7263758 := by
    simpa [prefixWord, tailWord_7263758, baseEnd_7263758] using wordTrace_append hprefix tailTrace_7263758
  have hstable : (prefixWord ++ tailWord_7263758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263758).length < 2 ^ (prefixWord ++ tailWord_7263758).sum := by decide
  have hdescent : baseEnd_7263758 < baseStart_7263758 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263778 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7263778 : Nat := 118140960795 + 7263778 * 2 ^ 59
def prefixEnd_7263778 : Nat := 4983230072969 + 3 ^ 40 * 7263778 * 2
def baseEnd_7263778 : Nat := 1243269827184795556289833

theorem tailTrace_7263778 : CollatzResearch.WordTrace tailWord_7263778 prefixEnd_7263778 1243269827184795556289833 := by
  unfold tailWord_7263778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66232937169645083840479997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176621165785720223574613325 66232937169645083840479997)
  ·
    refine ⟨24837351438616906440179999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66232937169645083840479997 24837351438616906440179999)
    ·
      refine ⟨37256027157925359660269999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24837351438616906440179999 37256027157925359660269999)
      ·
        refine ⟨55884040736888039490404999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37256027157925359660269999 55884040736888039490404999)
        ·
          refine ⟨83826061105332059235607499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55884040736888039490404999 83826061105332059235607499)
          ·
            refine ⟨125739091657998088853411249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83826061105332059235607499 125739091657998088853411249)
            ·
              refine ⟨94304318743498566640058437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125739091657998088853411249 94304318743498566640058437)
              ·
                refine ⟨17682059764405981245010957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94304318743498566640058437 17682059764405981245010957)
                ·
                  refine ⟨6630772411652242966879109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17682059764405981245010957 6630772411652242966879109)
                  ·
                    refine ⟨1243269827184795556289833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6630772411652242966879109 1243269827184795556289833)
                    ·
                      rfl

theorem cell23_7263778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7263778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263778 prefixEnd_7263778 := by exact prefixLift 7263778
  have htrace : WordTrace (prefixWord ++ tailWord_7263778) baseStart_7263778 baseEnd_7263778 := by
    simpa [prefixWord, tailWord_7263778, baseEnd_7263778] using wordTrace_append hprefix tailTrace_7263778
  have hstable : (prefixWord ++ tailWord_7263778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263778).length < 2 ^ (prefixWord ++ tailWord_7263778).sum := by decide
  have hdescent : baseEnd_7263778 < baseStart_7263778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263845 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 5, 2]
def baseStart_7263845 : Nat := 118140960795 + 7263845 * 2 ^ 59
def prefixEnd_7263845 : Nat := 4983230072969 + 3 ^ 40 * 7263845 * 2
def baseEnd_7263845 : Nat := 3729843884758237906731691

theorem tailTrace_7263845 : CollatzResearch.WordTrace tailWord_7263845 prefixEnd_7263845 3729843884758237906731691 := by
  unfold tailWord_7263845
  simp only [CollatzResearch.WordTrace]
  refine ⟨264934192369337605804608989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176622794912891737203072659 264934192369337605804608989)
  ·
    refine ⟨99350322138501602176728371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264934192369337605804608989 99350322138501602176728371)
    ·
      refine ⟨149025483207752403265092557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99350322138501602176728371 149025483207752403265092557)
      ·
        refine ⟨55884556202907151224409709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149025483207752403265092557 55884556202907151224409709)
        ·
          refine ⟨20956708576090181709153641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55884556202907151224409709 20956708576090181709153641)
          ·
            refine ⟨15717531432067636281865231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20956708576090181709153641 15717531432067636281865231)
            ·
              refine ⟨23576297148101454422797847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15717531432067636281865231 23576297148101454422797847)
              ·
                refine ⟨35364445722152181634196771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23576297148101454422797847 35364445722152181634196771)
                ·
                  refine ⟨53046668583228272451295157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35364445722152181634196771 53046668583228272451295157)
                  ·
                    refine ⟨4973125179677650542308921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53046668583228272451295157 4973125179677650542308921)
                    ·
                      refine ⟨3729843884758237906731691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973125179677650542308921 3729843884758237906731691)
                      ·
                        rfl

theorem cell23_7263845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 5, 2].length) (baseStart_7263845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263845 prefixEnd_7263845 := by exact prefixLift 7263845
  have htrace : WordTrace (prefixWord ++ tailWord_7263845) baseStart_7263845 baseEnd_7263845 := by
    simpa [prefixWord, tailWord_7263845, baseEnd_7263845] using wordTrace_append hprefix tailTrace_7263845
  have hstable : (prefixWord ++ tailWord_7263845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263845).length < 2 ^ (prefixWord ++ tailWord_7263845).sum := by decide
  have hdescent : baseEnd_7263845 < baseStart_7263845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263895 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_7263895 : Nat := 118140960795 + 7263895 * 2 ^ 59
def prefixEnd_7263895 : Nat := 4983230072969 + 3 ^ 40 * 7263895 * 2
def baseEnd_7263895 : Nat := 3729869558790962711106461

theorem tailTrace_7263895 : CollatzResearch.WordTrace tailWord_7263895 prefixEnd_7263895 3729869558790962711106461 := by
  unfold tailWord_7263895
  simp only [CollatzResearch.WordTrace]
  refine ⟨264936016019156464343929139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176624010679437642895952759 264936016019156464343929139)
  ·
    refine ⟨397404024028734696515893709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264936016019156464343929139 397404024028734696515893709)
    ·
      refine ⟨149026509010775511193460141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397404024028734696515893709 149026509010775511193460141)
      ·
        refine ⟨55884940879040816697547553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149026509010775511193460141 55884940879040816697547553)
        ·
          refine ⟨41913705659280612523160665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55884940879040816697547553 41913705659280612523160665)
          ·
            refine ⟨31435279244460459392370499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41913705659280612523160665 31435279244460459392370499)
            ·
              refine ⟨47152918866690689088555749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31435279244460459392370499 47152918866690689088555749)
              ·
                refine ⟨8841172287504504204104203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47152918866690689088555749 8841172287504504204104203)
                ·
                  refine ⟨13261758431256756306156305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8841172287504504204104203 13261758431256756306156305)
                  ·
                    refine ⟨9946318823442567229617229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13261758431256756306156305 9946318823442567229617229)
                    ·
                      refine ⟨3729869558790962711106461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9946318823442567229617229 3729869558790962711106461)
                      ·
                        rfl

theorem cell23_7263895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_7263895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263895 prefixEnd_7263895 := by exact prefixLift 7263895
  have htrace : WordTrace (prefixWord ++ tailWord_7263895) baseStart_7263895 baseEnd_7263895 := by
    simpa [prefixWord, tailWord_7263895, baseEnd_7263895] using wordTrace_append hprefix tailTrace_7263895
  have hstable : (prefixWord ++ tailWord_7263895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263895).length < 2 ^ (prefixWord ++ tailWord_7263895).sum := by decide
  have hdescent : baseEnd_7263895 < baseStart_7263895 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263903 : List Nat := [1, 1, 2, 7, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7263903 : Nat := 118140960795 + 7263903 * 2 ^ 59
def prefixEnd_7263903 : Nat := 4983230072969 + 3 ^ 40 * 7263903 * 2
def baseEnd_7263903 : Nat := 3729873666636198679806425

theorem tailTrace_7263903 : CollatzResearch.WordTrace tailWord_7263903 prefixEnd_7263903 3729873666636198679806425 := by
  unfold tailWord_7263903
  simp only [CollatzResearch.WordTrace]
  refine ⟨264936307803127481710220363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176624205202084987806813575 264936307803127481710220363)
  ·
    refine ⟨397404461704691222565330545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264936307803127481710220363 397404461704691222565330545)
    ·
      refine ⟨298053346278518416923997909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397404461704691222565330545 298053346278518416923997909)
      ·
        refine ⟨6985625303402775396656201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 298053346278518416923997909 6985625303402775396656201)
        ·
          refine ⟨5239218977552081547492151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6985625303402775396656201 5239218977552081547492151)
          ·
            refine ⟨7858828466328122321238227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5239218977552081547492151 7858828466328122321238227)
            ·
              refine ⟨11788242699492183481857341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7858828466328122321238227 11788242699492183481857341)
              ·
                refine ⟨4420591012309568805696503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11788242699492183481857341 4420591012309568805696503)
                ·
                  refine ⟨6630886518464353208544755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420591012309568805696503 6630886518464353208544755)
                  ·
                    refine ⟨9946329777696529812817133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6630886518464353208544755 9946329777696529812817133)
                    ·
                      refine ⟨3729873666636198679806425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9946329777696529812817133 3729873666636198679806425)
                      ·
                        rfl

theorem cell23_7263903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7263903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263903 prefixEnd_7263903 := by exact prefixLift 7263903
  have htrace : WordTrace (prefixWord ++ tailWord_7263903) baseStart_7263903 baseEnd_7263903 := by
    simpa [prefixWord, tailWord_7263903, baseEnd_7263903] using wordTrace_append hprefix tailTrace_7263903
  have hstable : (prefixWord ++ tailWord_7263903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263903).length < 2 ^ (prefixWord ++ tailWord_7263903).sum := by decide
  have hdescent : baseEnd_7263903 < baseStart_7263903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263909 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 1, 2, 2]
def baseStart_7263909 : Nat := 118140960795 + 7263909 * 2 ^ 59
def prefixEnd_7263909 : Nat := 4983230072969 + 3 ^ 40 * 7263909 * 2
def baseEnd_7263909 : Nat := 3729876747520125656331397

theorem tailTrace_7263909 : CollatzResearch.WordTrace tailWord_7263909 prefixEnd_7263909 3729876747520125656331397 := by
  unfold tailWord_7263909
  simp only [CollatzResearch.WordTrace]
  refine ⟨264936526641105744734938781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176624351094070496489959187 264936526641105744734938781)
  ·
    refine ⟨99351197490414654275602043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264936526641105744734938781 99351197490414654275602043)
    ·
      refine ⟨149026796235621981413403065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99351197490414654275602043 149026796235621981413403065)
      ·
        refine ⟨111770097176716486060052299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149026796235621981413403065 111770097176716486060052299)
        ·
          refine ⟨167655145765074729090078449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111770097176716486060052299 167655145765074729090078449)
          ·
            refine ⟨125741359323806046817558837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167655145765074729090078449 125741359323806046817558837)
            ·
              refine ⟨11788252436606816889146141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 125741359323806046817558837 11788252436606816889146141)
              ·
                refine ⟨4420594663727556333429803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11788252436606816889146141 4420594663727556333429803)
                ·
                  refine ⟨6630891995591334500144705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420594663727556333429803 6630891995591334500144705)
                  ·
                    refine ⟨4973168996693500875108529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6630891995591334500144705 4973168996693500875108529)
                    ·
                      refine ⟨3729876747520125656331397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973168996693500875108529 3729876747520125656331397)
                      ·
                        rfl

theorem cell23_7263909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 1, 2, 2].length) (baseStart_7263909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263909 prefixEnd_7263909 := by exact prefixLift 7263909
  have htrace : WordTrace (prefixWord ++ tailWord_7263909) baseStart_7263909 baseEnd_7263909 := by
    simpa [prefixWord, tailWord_7263909, baseEnd_7263909] using wordTrace_append hprefix tailTrace_7263909
  have hstable : (prefixWord ++ tailWord_7263909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263909).length < 2 ^ (prefixWord ++ tailWord_7263909).sum := by decide
  have hdescent : baseEnd_7263909 < baseStart_7263909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263926 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2]
def baseStart_7263926 : Nat := 118140960795 + 7263926 * 2 ^ 59
def prefixEnd_7263926 : Nat := 4983230072969 + 3 ^ 40 * 7263926 * 2
def baseEnd_7263926 : Nat := 3729885476691252089818819

theorem tailTrace_7263926 : CollatzResearch.WordTrace tailWord_7263926 prefixEnd_7263926 3729885476691252089818819 := by
  unfold tailWord_7263926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16558571667627759789894227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176624764454696104425538421 16558571667627759789894227)
  ·
    refine ⟨24837857501441639684841341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16558571667627759789894227 24837857501441639684841341)
    ·
      refine ⟨9314196563040614881815503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24837857501441639684841341 9314196563040614881815503)
      ·
        refine ⟨13971294844560922322723255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314196563040614881815503 13971294844560922322723255)
        ·
          refine ⟨20956942266841383484084883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13971294844560922322723255 20956942266841383484084883)
          ·
            refine ⟨31435413400262075226127325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20956942266841383484084883 31435413400262075226127325)
            ·
              refine ⟨11788280025098278209797747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31435413400262075226127325 11788280025098278209797747)
              ·
                refine ⟨17682420037647417314696621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788280025098278209797747 17682420037647417314696621)
                ·
                  refine ⟨6630907514117781493011233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17682420037647417314696621 6630907514117781493011233)
                  ·
                    refine ⟨4973180635588336119758425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6630907514117781493011233 4973180635588336119758425)
                    ·
                      refine ⟨3729885476691252089818819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973180635588336119758425 3729885476691252089818819)
                      ·
                        rfl

theorem cell23_7263926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_7263926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263926 prefixEnd_7263926 := by exact prefixLift 7263926
  have htrace : WordTrace (prefixWord ++ tailWord_7263926) baseStart_7263926 baseEnd_7263926 := by
    simpa [prefixWord, tailWord_7263926, baseEnd_7263926] using wordTrace_append hprefix tailTrace_7263926
  have hstable : (prefixWord ++ tailWord_7263926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263926).length < 2 ^ (prefixWord ++ tailWord_7263926).sum := by decide
  have hdescent : baseEnd_7263926 < baseStart_7263926 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263935 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 3, 3, 2]
def baseStart_7263935 : Nat := 118140960795 + 7263935 * 2 ^ 59
def prefixEnd_7263935 : Nat := 4983230072969 + 3 ^ 40 * 7263935 * 2
def baseEnd_7263935 : Nat := 3729890098017142554606277

theorem tailTrace_7263935 : CollatzResearch.WordTrace tailWord_7263935 prefixEnd_7263935 3729890098017142554606277 := by
  unfold tailWord_7263935
  simp only [CollatzResearch.WordTrace]
  refine ⟨264937474939011551175385259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176624983292674367450256839 264937474939011551175385259)
  ·
    refine ⟨397406212408517326763077889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264937474939011551175385259 397406212408517326763077889)
    ·
      refine ⟨298054659306387995072308417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397406212408517326763077889 298054659306387995072308417)
      ·
        refine ⟨223540994479790996304231313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 298054659306387995072308417 223540994479790996304231313)
        ·
          refine ⟨167655745859843247228173485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223540994479790996304231313 167655745859843247228173485)
          ·
            refine ⟨62870904697441217710565057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 167655745859843247228173485 62870904697441217710565057)
            ·
              refine ⟨47153178523080913282923793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62870904697441217710565057 47153178523080913282923793)
              ·
                refine ⟨35364883892310684962192845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47153178523080913282923793 35364883892310684962192845)
                ·
                  refine ⟨13261831459616506860822317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35364883892310684962192845 13261831459616506860822317)
                  ·
                    refine ⟨4973186797356190072808369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13261831459616506860822317 4973186797356190072808369)
                    ·
                      refine ⟨3729890098017142554606277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973186797356190072808369 3729890098017142554606277)
                      ·
                        rfl

theorem cell23_7263935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 3, 2].length) (baseStart_7263935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263935 prefixEnd_7263935 := by exact prefixLift 7263935
  have htrace : WordTrace (prefixWord ++ tailWord_7263935) baseStart_7263935 baseEnd_7263935 := by
    simpa [prefixWord, tailWord_7263935, baseEnd_7263935] using wordTrace_append hprefix tailTrace_7263935
  have hstable : (prefixWord ++ tailWord_7263935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263935).length < 2 ^ (prefixWord ++ tailWord_7263935).sum := by decide
  have hdescent : baseEnd_7263935 < baseStart_7263935 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7263968 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5]
def baseStart_7263968 : Nat := 118140960795 + 7263968 * 2 ^ 59
def prefixEnd_7263968 : Nat := 4983230072969 + 3 ^ 40 * 7263968 * 2
def baseEnd_7263968 : Nat := 3729907042878740925493625

theorem tailTrace_7263968 : CollatzResearch.WordTrace tailWord_7263968 prefixEnd_7263968 3729907042878740925493625 := by
  unfold tailWord_7263968
  simp only [CollatzResearch.WordTrace]
  refine ⟨132469339273945998905668279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176625785698594665207557705 132469339273945998905668279)
  ·
    refine ⟨198704008910918998358502419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132469339273945998905668279 198704008910918998358502419)
    ·
      refine ⟨298056013366378497537753629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198704008910918998358502419 298056013366378497537753629)
      ·
        refine ⟨111771005012391936576657611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 298056013366378497537753629 111771005012391936576657611)
        ·
          refine ⟨167656507518587904864986417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111771005012391936576657611 167656507518587904864986417)
          ·
            refine ⟨125742380638940928648739813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167656507518587904864986417 125742380638940928648739813)
            ·
              refine ⟨23576696369801424121638715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125742380638940928648739813 23576696369801424121638715)
              ·
                refine ⟨35365044554702136182458073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23576696369801424121638715 35365044554702136182458073)
                ·
                  refine ⟨26523783416026602136843555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35365044554702136182458073 26523783416026602136843555)
                  ·
                    refine ⟨39785675124039903205265333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26523783416026602136843555 39785675124039903205265333)
                    ·
                      refine ⟨3729907042878740925493625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39785675124039903205265333 3729907042878740925493625)
                      ·
                        rfl

theorem cell23_7263968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_7263968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7263968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7263968 prefixEnd_7263968 := by exact prefixLift 7263968
  have htrace : WordTrace (prefixWord ++ tailWord_7263968) baseStart_7263968 baseEnd_7263968 := by
    simpa [prefixWord, tailWord_7263968, baseEnd_7263968] using wordTrace_append hprefix tailTrace_7263968
  have hstable : (prefixWord ++ tailWord_7263968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7263968).length < 2 ^ (prefixWord ++ tailWord_7263968).sum := by decide
  have hdescent : baseEnd_7263968 < baseStart_7263968 := by decide
  rcases family_descends (prefixWord ++ tailWord_7263968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264055 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 6, 2]
def baseStart_7264055 : Nat := 118140960795 + 7264055 * 2 ^ 59
def prefixEnd_7264055 : Nat := 4983230072969 + 3 ^ 40 * 7264055 * 2
def baseEnd_7264055 : Nat := 3729951715695682085105725

theorem tailTrace_7264055 : CollatzResearch.WordTrace tailWord_7264055 prefixEnd_7264055 3729951715695682085105725 := by
  unfold tailWord_7264055
  simp only [CollatzResearch.WordTrace]
  refine ⟨264941851698576811669753619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176627901132384541113169079 264941851698576811669753619)
  ·
    refine ⟨397412777547865217504630429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264941851698576811669753619 397412777547865217504630429)
    ·
      refine ⟨149029791580449456564236411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 397412777547865217504630429 149029791580449456564236411)
      ·
        refine ⟨223544687370674184846354617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149029791580449456564236411 223544687370674184846354617)
        ·
          refine ⟨167658515528005638634765963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 223544687370674184846354617 167658515528005638634765963)
          ·
            refine ⟨251487773292008457952148945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167658515528005638634765963 251487773292008457952148945)
            ·
              refine ⟨188615829969006343464111709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 251487773292008457952148945 188615829969006343464111709)
              ·
                refine ⟨70730936238377378799041891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 188615829969006343464111709 70730936238377378799041891)
                ·
                  refine ⟨106096404357566068198562837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70730936238377378799041891 106096404357566068198562837)
                  ·
                    refine ⟨4973268954260909446807633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106096404357566068198562837 4973268954260909446807633)
                    ·
                      refine ⟨3729951715695682085105725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973268954260909446807633 3729951715695682085105725)
                      ·
                        rfl

theorem cell23_7264055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 6, 2].length) (baseStart_7264055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264055 prefixEnd_7264055 := by exact prefixLift 7264055
  have htrace : WordTrace (prefixWord ++ tailWord_7264055) baseStart_7264055 baseEnd_7264055 := by
    simpa [prefixWord, tailWord_7264055, baseEnd_7264055] using wordTrace_append hprefix tailTrace_7264055
  have hstable : (prefixWord ++ tailWord_7264055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264055).length < 2 ^ (prefixWord ++ tailWord_7264055).sum := by decide
  have hdescent : baseEnd_7264055 < baseStart_7264055 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264099 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 3, 4]
def baseStart_7264099 : Nat := 118140960795 + 7264099 * 2 ^ 59
def prefixEnd_7264099 : Nat := 4983230072969 + 3 ^ 40 * 7264099 * 2
def baseEnd_7264099 : Nat := 1243324769614826637651841

theorem tailTrace_7264099 : CollatzResearch.WordTrace tailWord_7264099 prefixEnd_7264099 1243324769614826637651841 := by
  unfold tailWord_7264099
  simp only [CollatzResearch.WordTrace]
  refine ⟨264943456510417407184355351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176628971006944938122903567 264943456510417407184355351)
  ·
    refine ⟨397415184765626110776533027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264943456510417407184355351 397415184765626110776533027)
    ·
      refine ⟨596122777148439166164799541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397415184765626110776533027 596122777148439166164799541)
      ·
        refine ⟨55886510357666171827949957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 596122777148439166164799541 55886510357666171827949957)
        ·
          refine ⟨10478720692062407217740617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55886510357666171827949957 10478720692062407217740617)
          ·
            refine ⟨7859040519046805413305463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10478720692062407217740617 7859040519046805413305463)
            ·
              refine ⟨11788560778570208119958195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859040519046805413305463 11788560778570208119958195)
              ·
                refine ⟨17682841167855312179937293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788560778570208119958195 17682841167855312179937293)
                ·
                  refine ⟨6631065437945742067476485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17682841167855312179937293 6631065437945742067476485)
                  ·
                    refine ⟨1243324769614826637651841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631065437945742067476485 1243324769614826637651841)
                    ·
                      rfl

theorem cell23_7264099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 4].length) (baseStart_7264099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264099 prefixEnd_7264099 := by exact prefixLift 7264099
  have htrace : WordTrace (prefixWord ++ tailWord_7264099) baseStart_7264099 baseEnd_7264099 := by
    simpa [prefixWord, tailWord_7264099, baseEnd_7264099] using wordTrace_append hprefix tailTrace_7264099
  have hstable : (prefixWord ++ tailWord_7264099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264099).length < 2 ^ (prefixWord ++ tailWord_7264099).sum := by decide
  have hdescent : baseEnd_7264099 < baseStart_7264099 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264122 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3]
def baseStart_7264122 : Nat := 118140960795 + 7264122 * 2 ^ 59
def prefixEnd_7264122 : Nat := 4983230072969 + 3 ^ 40 * 7264122 * 2
def baseEnd_7264122 : Nat := 3729986118899533322967917

theorem tailTrace_7264122 : CollatzResearch.WordTrace tailWord_7264122 prefixEnd_7264122 3729986118899533322967917 := by
  unfold tailWord_7264122
  simp only [CollatzResearch.WordTrace]
  refine ⟨66236073847333520528110655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176629530259556054741628413 66236073847333520528110655)
  ·
    refine ⟨99354110771000280792165983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66236073847333520528110655 99354110771000280792165983)
    ·
      refine ⟨149031166156500421188248975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99354110771000280792165983 149031166156500421188248975)
      ·
        refine ⟨223546749234750631782373463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149031166156500421188248975 223546749234750631782373463)
        ·
          refine ⟨335320123852125947673560195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223546749234750631782373463 335320123852125947673560195)
          ·
            refine ⟨502980185778188921510340293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335320123852125947673560195 502980185778188921510340293)
            ·
              refine ⟨94308784833410422783188805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 502980185778188921510340293 94308784833410422783188805)
              ·
                refine ⟨17682897156264454271847901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94308784833410422783188805 17682897156264454271847901)
                ·
                  refine ⟨6631086433599170351942963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17682897156264454271847901 6631086433599170351942963)
                  ·
                    refine ⟨9946629650398755527914445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631086433599170351942963 9946629650398755527914445)
                    ·
                      refine ⟨3729986118899533322967917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9946629650398755527914445 3729986118899533322967917)
                      ·
                        rfl

theorem cell23_7264122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3, 1, 3].length) (baseStart_7264122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264122 prefixEnd_7264122 := by exact prefixLift 7264122
  have htrace : WordTrace (prefixWord ++ tailWord_7264122) baseStart_7264122 baseEnd_7264122 := by
    simpa [prefixWord, tailWord_7264122, baseEnd_7264122] using wordTrace_append hprefix tailTrace_7264122
  have hstable : (prefixWord ++ tailWord_7264122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264122).length < 2 ^ (prefixWord ++ tailWord_7264122).sum := by decide
  have hdescent : baseEnd_7264122 < baseStart_7264122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264126 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7264126 : Nat := 118140960795 + 7264126 * 2 ^ 59
def prefixEnd_7264126 : Nat := 4983230072969 + 3 ^ 40 * 7264126 * 2
def baseEnd_7264126 : Nat := 3729988172822151307317899

theorem tailTrace_7264126 : CollatzResearch.WordTrace tailWord_7264126 prefixEnd_7264126 3729988172822151307317899 := by
  unfold tailWord_7264126
  simp only [CollatzResearch.WordTrace]
  refine ⟨33118055160164948849448529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176629627520879727197058821 33118055160164948849448529)
  ·
    refine ⟨24838541370123711637086397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33118055160164948849448529 24838541370123711637086397)
    ·
      refine ⟨9314453013796391863907399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24838541370123711637086397 9314453013796391863907399)
      ·
        refine ⟨13971679520694587795861099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314453013796391863907399 13971679520694587795861099)
        ·
          refine ⟨20957519281041881693791649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13971679520694587795861099 20957519281041881693791649)
          ·
            refine ⟨15718139460781411270343737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20957519281041881693791649 15718139460781411270343737)
            ·
              refine ⟨11788604595586058452757803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15718139460781411270343737 11788604595586058452757803)
              ·
                refine ⟨17682906893379087679136705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11788604595586058452757803 17682906893379087679136705)
                ·
                  refine ⟨13262180170034315759352529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17682906893379087679136705 13262180170034315759352529)
                  ·
                    refine ⟨9946635127525736819514397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13262180170034315759352529 9946635127525736819514397)
                    ·
                      refine ⟨3729988172822151307317899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9946635127525736819514397 3729988172822151307317899)
                      ·
                        rfl

theorem cell23_7264126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7264126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264126 prefixEnd_7264126 := by exact prefixLift 7264126
  have htrace : WordTrace (prefixWord ++ tailWord_7264126) baseStart_7264126 baseEnd_7264126 := by
    simpa [prefixWord, tailWord_7264126, baseEnd_7264126] using wordTrace_append hprefix tailTrace_7264126
  have hstable : (prefixWord ++ tailWord_7264126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264126).length < 2 ^ (prefixWord ++ tailWord_7264126).sum := by decide
  have hdescent : baseEnd_7264126 < baseStart_7264126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264132 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_7264132 : Nat := 118140960795 + 7264132 * 2 ^ 59
def prefixEnd_7264132 : Nat := 4983230072969 + 3 ^ 40 * 7264132 * 2
def baseEnd_7264132 : Nat := 3729991253706078283842871

theorem tailTrace_7264132 : CollatzResearch.WordTrace tailWord_7264132 prefixEnd_7264132 3729991253706078283842871 := by
  unfold tailWord_7264132
  simp only [CollatzResearch.WordTrace]
  refine ⟨132472330059648926910153325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176629773412865235880204433 132472330059648926910153325)
  ·
    refine ⟨49677123772368347591307497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132472330059648926910153325 49677123772368347591307497)
    ·
      refine ⟨37257842829276260693480623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49677123772368347591307497 37257842829276260693480623)
      ·
        refine ⟨55886764243914391040220935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37257842829276260693480623 55886764243914391040220935)
        ·
          refine ⟨83830146365871586560331403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55886764243914391040220935 83830146365871586560331403)
          ·
            refine ⟨125745219548807379840497105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83830146365871586560331403 125745219548807379840497105)
            ·
              refine ⟨94308914661605534880372829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125745219548807379840497105 94308914661605534880372829)
              ·
                refine ⟨35365842998102075580139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94308914661605534880372829 35365842998102075580139811)
                ·
                  refine ⟨53048764497153113370209717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35365842998102075580139811 53048764497153113370209717)
                  ·
                    refine ⟨4973321671608104378457161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53048764497153113370209717 4973321671608104378457161)
                    ·
                      refine ⟨3729991253706078283842871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973321671608104378457161 3729991253706078283842871)
                      ·
                        rfl

theorem cell23_7264132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_7264132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264132 prefixEnd_7264132 := by exact prefixLift 7264132
  have htrace : WordTrace (prefixWord ++ tailWord_7264132) baseStart_7264132 baseEnd_7264132 := by
    simpa [prefixWord, tailWord_7264132, baseEnd_7264132] using wordTrace_append hprefix tailTrace_7264132
  have hstable : (prefixWord ++ tailWord_7264132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264132).length < 2 ^ (prefixWord ++ tailWord_7264132).sum := by decide
  have hdescent : baseEnd_7264132 < baseStart_7264132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264139 : List Nat := [1, 1, 1, 1, 4, 2, 1, 7, 1, 1, 3]
def baseStart_7264139 : Nat := 118140960795 + 7264139 * 2 ^ 59
def prefixEnd_7264139 : Nat := 4983230072969 + 3 ^ 40 * 7264139 * 2
def baseEnd_7264139 : Nat := 3729994848070659756455339

theorem tailTrace_7264139 : CollatzResearch.WordTrace tailWord_7264139 prefixEnd_7264139 3729994848070659756455339 := by
  unfold tailWord_7264139
  simp only [CollatzResearch.WordTrace]
  refine ⟨264944915430272494015811471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176629943620181662677207647 264944915430272494015811471)
  ·
    refine ⟨397417373145408741023717207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264944915430272494015811471 397417373145408741023717207)
    ·
      refine ⟨596126059718113111535575811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397417373145408741023717207 596126059718113111535575811)
      ·
        refine ⟨894189089577169667303363717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596126059718113111535575811 894189089577169667303363717)
        ·
          refine ⟨167660454295719312619380697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 894189089577169667303363717 167660454295719312619380697)
          ·
            refine ⟨125745340721789484464535523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 167660454295719312619380697 125745340721789484464535523)
            ·
              refine ⟨188618011082684226696803285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 125745340721789484464535523 188618011082684226696803285)
              ·
                refine ⟨4420734634750411563206327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 188618011082684226696803285 4420734634750411563206327)
                ·
                  refine ⟨6631101952125617344809491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420734634750411563206327 6631101952125617344809491)
                  ·
                    refine ⟨9946652928188426017214237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631101952125617344809491 9946652928188426017214237)
                    ·
                      refine ⟨3729994848070659756455339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9946652928188426017214237 3729994848070659756455339)
                      ·
                        rfl

theorem cell23_7264139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 7, 1, 1, 3].length) (baseStart_7264139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264139 prefixEnd_7264139 := by exact prefixLift 7264139
  have htrace : WordTrace (prefixWord ++ tailWord_7264139) baseStart_7264139 baseEnd_7264139 := by
    simpa [prefixWord, tailWord_7264139, baseEnd_7264139] using wordTrace_append hprefix tailTrace_7264139
  have hstable : (prefixWord ++ tailWord_7264139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264139).length < 2 ^ (prefixWord ++ tailWord_7264139).sum := by decide
  have hdescent : baseEnd_7264139 < baseStart_7264139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264150 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_7264150 : Nat := 118140960795 + 7264150 * 2 ^ 59
def prefixEnd_7264150 : Nat := 4983230072969 + 3 ^ 40 * 7264150 * 2
def baseEnd_7264150 : Nat := 1243333498785953071139263

theorem tailTrace_7264150 : CollatzResearch.WordTrace tailWord_7264150 prefixEnd_7264150 1243333498785953071139263 := by
  unfold tailWord_7264150
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559082289577040180903869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176630211088821761929641269 16559082289577040180903869)
  ·
    refine ⟨6209655858591390067838951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16559082289577040180903869 6209655858591390067838951)
    ·
      refine ⟨9314483787887085101758427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209655858591390067838951 9314483787887085101758427)
      ·
        refine ⟨13971725681830627652637641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314483787887085101758427 13971725681830627652637641)
        ·
          refine ⟨10478794261372970739478231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13971725681830627652637641 10478794261372970739478231)
          ·
            refine ⟨15718191392059456109217347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10478794261372970739478231 15718191392059456109217347)
            ·
              refine ⟨23577287088089184163826021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15718191392059456109217347 23577287088089184163826021)
              ·
                refine ⟨4420741329016722030717379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23577287088089184163826021 4420741329016722030717379)
                ·
                  refine ⟨6631111993525083046076069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420741329016722030717379 6631111993525083046076069)
                  ·
                    refine ⟨1243333498785953071139263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631111993525083046076069 1243333498785953071139263)
                    ·
                      rfl

theorem cell23_7264150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_7264150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264150 prefixEnd_7264150 := by exact prefixLift 7264150
  have htrace : WordTrace (prefixWord ++ tailWord_7264150) baseStart_7264150 baseEnd_7264150 := by
    simpa [prefixWord, tailWord_7264150, baseEnd_7264150] using wordTrace_append hprefix tailTrace_7264150
  have hstable : (prefixWord ++ tailWord_7264150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264150).length < 2 ^ (prefixWord ++ tailWord_7264150).sum := by decide
  have hdescent : baseEnd_7264150 < baseStart_7264150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264165 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 5]
def baseStart_7264165 : Nat := 118140960795 + 7264165 * 2 ^ 59
def prefixEnd_7264165 : Nat := 4983230072969 + 3 ^ 40 * 7264165 * 2
def baseEnd_7264165 : Nat := 3730008198567676654730219

theorem tailTrace_7264165 : CollatzResearch.WordTrace tailWord_7264165 prefixEnd_7264165 3730008198567676654730219 := by
  unfold tailWord_7264165
  simp only [CollatzResearch.WordTrace]
  refine ⟨264945863728178300456257949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176630575818785533637505299 264945863728178300456257949)
  ·
    refine ⟨99354698898066862671096731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264945863728178300456257949 99354698898066862671096731)
    ·
      refine ⟨149032048347100294006645097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99354698898066862671096731 149032048347100294006645097)
      ·
        refine ⟨111774036260325220504983823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149032048347100294006645097 111774036260325220504983823)
        ·
          refine ⟨167661054390487830757475735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111774036260325220504983823 167661054390487830757475735)
          ·
            refine ⟨251491581585731746136213603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167661054390487830757475735 251491581585731746136213603)
            ·
              refine ⟨377237372378597619204320405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251491581585731746136213603 377237372378597619204320405)
              ·
                refine ⟨17683001830246763400202519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 377237372378597619204320405 17683001830246763400202519)
                ·
                  refine ⟨26524502745370145100303779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17683001830246763400202519 26524502745370145100303779)
                  ·
                    refine ⟨39786754118055217650455669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26524502745370145100303779 39786754118055217650455669)
                    ·
                      refine ⟨3730008198567676654730219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39786754118055217650455669 3730008198567676654730219)
                      ·
                        rfl

theorem cell23_7264165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_7264165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264165 prefixEnd_7264165 := by exact prefixLift 7264165
  have htrace : WordTrace (prefixWord ++ tailWord_7264165) baseStart_7264165 baseEnd_7264165 := by
    simpa [prefixWord, tailWord_7264165, baseEnd_7264165] using wordTrace_append hprefix tailTrace_7264165
  have hstable : (prefixWord ++ tailWord_7264165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264165).length < 2 ^ (prefixWord ++ tailWord_7264165).sum := by decide
  have hdescent : baseEnd_7264165 < baseStart_7264165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264179 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 3, 2, 2]
def baseStart_7264179 : Nat := 118140960795 + 7264179 * 2 ^ 59
def prefixEnd_7264179 : Nat := 4983230072969 + 3 ^ 40 * 7264179 * 2
def baseEnd_7264179 : Nat := 3730015387296839599955155

theorem tailTrace_7264179 : CollatzResearch.WordTrace tailWord_7264179 prefixEnd_7264179 3730015387296839599955155 := by
  unfold tailWord_7264179
  simp only [CollatzResearch.WordTrace]
  refine ⟨264946374350127580847267591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176630916233418387231511727 264946374350127580847267591)
  ·
    refine ⟨397419561525191371270901387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264946374350127580847267591 397419561525191371270901387)
    ·
      refine ⟨596129342287787056906352081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397419561525191371270901387 596129342287787056906352081)
      ·
        refine ⟨447097006715840292679764061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596129342287787056906352081 447097006715840292679764061)
        ·
          refine ⟨167661377518440109754911523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 447097006715840292679764061 167661377518440109754911523)
          ·
            refine ⟨251492066277660164632367285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 167661377518440109754911523 251492066277660164632367285)
            ·
              refine ⟨23577381213530640434284433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 251492066277660164632367285 23577381213530640434284433)
              ·
                refine ⟨17683035910147980325713325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23577381213530640434284433 17683035910147980325713325)
                ·
                  refine ⟨6631138466305492622142497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17683035910147980325713325 6631138466305492622142497)
                  ·
                    refine ⟨4973353849729119466606873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6631138466305492622142497 4973353849729119466606873)
                    ·
                      refine ⟨3730015387296839599955155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973353849729119466606873 3730015387296839599955155)
                      ·
                        rfl

theorem cell23_7264179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 3, 2, 2].length) (baseStart_7264179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264179 prefixEnd_7264179 := by exact prefixLift 7264179
  have htrace : WordTrace (prefixWord ++ tailWord_7264179) baseStart_7264179 baseEnd_7264179 := by
    simpa [prefixWord, tailWord_7264179, baseEnd_7264179] using wordTrace_append hprefix tailTrace_7264179
  have hstable : (prefixWord ++ tailWord_7264179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264179).length < 2 ^ (prefixWord ++ tailWord_7264179).sum := by decide
  have hdescent : baseEnd_7264179 < baseStart_7264179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264213 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_7264213 : Nat := 118140960795 + 7264213 * 2 ^ 59
def prefixEnd_7264213 : Nat := 4983230072969 + 3 ^ 40 * 7264213 * 2
def baseEnd_7264213 : Nat := 3730032845639092466929999

theorem tailTrace_7264213 : CollatzResearch.WordTrace tailWord_7264213 prefixEnd_7264213 3730032845639092466929999 := by
  unfold tailWord_7264213
  simp only [CollatzResearch.WordTrace]
  refine ⟨264947614432004404654005293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176631742954669603102670195 264947614432004404654005293)
  ·
    refine ⟨99355355412001651745251985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264947614432004404654005293 99355355412001651745251985)
    ·
      refine ⟨74516516559001238808938989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99355355412001651745251985 74516516559001238808938989)
      ·
        refine ⟨27943693709625464553352121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74516516559001238808938989 27943693709625464553352121)
        ·
          refine ⟨20957770282219098415014091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27943693709625464553352121 20957770282219098415014091)
          ·
            refine ⟨31436655423328647622521137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20957770282219098415014091 31436655423328647622521137)
            ·
              refine ⟨23577491567496485716890853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31436655423328647622521137 23577491567496485716890853)
              ·
                refine ⟨4420779668905591071917035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23577491567496485716890853 4420779668905591071917035)
                ·
                  refine ⟨6631169503358386607875553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420779668905591071917035 6631169503358386607875553)
                  ·
                    refine ⟨4973377127518789955906665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6631169503358386607875553 4973377127518789955906665)
                    ·
                      refine ⟨3730032845639092466929999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973377127518789955906665 3730032845639092466929999)
                      ·
                        rfl

theorem cell23_7264213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_7264213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264213 prefixEnd_7264213 := by exact prefixLift 7264213
  have htrace : WordTrace (prefixWord ++ tailWord_7264213) baseStart_7264213 baseEnd_7264213 := by
    simpa [prefixWord, tailWord_7264213, baseEnd_7264213] using wordTrace_append hprefix tailTrace_7264213
  have hstable : (prefixWord ++ tailWord_7264213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264213).length < 2 ^ (prefixWord ++ tailWord_7264213).sum := by decide
  have hdescent : baseEnd_7264213 < baseStart_7264213 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264235 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4]
def baseStart_7264235 : Nat := 118140960795 + 7264235 * 2 ^ 59
def prefixEnd_7264235 : Nat := 4983230072969 + 3 ^ 40 * 7264235 * 2
def baseEnd_7264235 : Nat := 3730044142213491380854897

theorem tailTrace_7264235 : CollatzResearch.WordTrace tailWord_7264235 prefixEnd_7264235 3730044142213491380854897 := by
  unfold tailWord_7264235
  simp only [CollatzResearch.WordTrace]
  refine ⟨264948416837924702411306159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176632277891949801607537439 264948416837924702411306159)
  ·
    refine ⟨397422625256887053616959239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264948416837924702411306159 397422625256887053616959239)
    ·
      refine ⟨596133937885330580425438859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397422625256887053616959239 596133937885330580425438859)
      ·
        refine ⟨894200906827995870638158289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596133937885330580425438859 894200906827995870638158289)
        ·
          refine ⟨670650680120996902978618717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894200906827995870638158289 670650680120996902978618717)
          ·
            refine ⟨251494005045373838616982019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 670650680120996902978618717 251494005045373838616982019)
            ·
              refine ⟨377241007568060757925473029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 251494005045373838616982019 377241007568060757925473029)
              ·
                refine ⟨70732688919011392111026193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 377241007568060757925473029 70732688919011392111026193)
                ·
                  refine ⟨53049516689258544083269645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 70732688919011392111026193 53049516689258544083269645)
                  ·
                    refine ⟨19893568758471954031226117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53049516689258544083269645 19893568758471954031226117)
                    ·
                      refine ⟨3730044142213491380854897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19893568758471954031226117 3730044142213491380854897)
                      ·
                        rfl

theorem cell23_7264235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_7264235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264235 prefixEnd_7264235 := by exact prefixLift 7264235
  have htrace : WordTrace (prefixWord ++ tailWord_7264235) baseStart_7264235 baseEnd_7264235 := by
    simpa [prefixWord, tailWord_7264235, baseEnd_7264235] using wordTrace_append hprefix tailTrace_7264235
  have hstable : (prefixWord ++ tailWord_7264235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264235).length < 2 ^ (prefixWord ++ tailWord_7264235).sum := by decide
  have hdescent : baseEnd_7264235 < baseStart_7264235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264315 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7]
def baseStart_7264315 : Nat := 118140960795 + 7264315 * 2 ^ 59
def prefixEnd_7264315 : Nat := 4983230072969 + 3 ^ 40 * 7264315 * 2
def baseEnd_7264315 : Nat := 3730085220665851067854529

theorem tailTrace_7264315 : CollatzResearch.WordTrace tailWord_7264315 prefixEnd_7264315 3730085220665851067854529 := by
  unfold tailWord_7264315
  simp only [CollatzResearch.WordTrace]
  refine ⟨264951334677634876074218399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176634223118423250716145599 264951334677634876074218399)
  ·
    refine ⟨397427002016452314111327599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264951334677634876074218399 397427002016452314111327599)
    ·
      refine ⟨596140503024678471166991399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397427002016452314111327599 596140503024678471166991399)
      ·
        refine ⟨894210754537017706750487099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596140503024678471166991399 894210754537017706750487099)
        ·
          refine ⟨1341316131805526560125730649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894210754537017706750487099 1341316131805526560125730649)
          ·
            refine ⟨1005987098854144920094297987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341316131805526560125730649 1005987098854144920094297987)
            ·
              refine ⟨1508980648281217380141446981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1005987098854144920094297987 1508980648281217380141446981)
              ·
                refine ⟨282933871552728258776521309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1508980648281217380141446981 282933871552728258776521309)
                ·
                  refine ⟨106100201832273097041195491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 282933871552728258776521309 106100201832273097041195491)
                  ·
                    refine ⟨159150302748409645561793237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106100201832273097041195491 159150302748409645561793237)
                    ·
                      refine ⟨3730085220665851067854529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 159150302748409645561793237 3730085220665851067854529)
                      ·
                        rfl

theorem cell23_7264315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_7264315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264315 prefixEnd_7264315 := by exact prefixLift 7264315
  have htrace : WordTrace (prefixWord ++ tailWord_7264315) baseStart_7264315 baseEnd_7264315 := by
    simpa [prefixWord, tailWord_7264315, baseEnd_7264315] using wordTrace_append hprefix tailTrace_7264315
  have hstable : (prefixWord ++ tailWord_7264315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264315).length < 2 ^ (prefixWord ++ tailWord_7264315).sum := by decide
  have hdescent : baseEnd_7264315 < baseStart_7264315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264332 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7264332 : Nat := 118140960795 + 7264332 * 2 ^ 59
def prefixEnd_7264332 : Nat := 4983230072969 + 3 ^ 40 * 7264332 * 2
def baseEnd_7264332 : Nat := 3730093949836977501341951

theorem tailTrace_7264332 : CollatzResearch.WordTrace tailWord_7264332 prefixEnd_7264332 3730093949836977501341951 := by
  unfold tailWord_7264332
  simp only [CollatzResearch.WordTrace]
  refine ⟨132475977359286643988793625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176634636479048858651724833 132475977359286643988793625)
  ·
    refine ⟨99356983019464982991595219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132475977359286643988793625 99356983019464982991595219)
    ·
      refine ⟨149035474529197474487392829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99356983019464982991595219 149035474529197474487392829)
      ·
        refine ⟨55888302948449052932772311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149035474529197474487392829 55888302948449052932772311)
        ·
          refine ⟨83832454422673579399158467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55888302948449052932772311 83832454422673579399158467)
          ·
            refine ⟨125748681634010369098737701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 83832454422673579399158467 125748681634010369098737701)
            ·
              refine ⟨23577877806376944206013319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125748681634010369098737701 23577877806376944206013319)
              ·
                refine ⟨35366816709565416309019979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23577877806376944206013319 35366816709565416309019979)
                ·
                  refine ⟨53050225064348124463529969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35366816709565416309019979 53050225064348124463529969)
                  ·
                    refine ⟨39787668798261093347647477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53050225064348124463529969 39787668798261093347647477)
                    ·
                      refine ⟨3730093949836977501341951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39787668798261093347647477 3730093949836977501341951)
                      ·
                        rfl

theorem cell23_7264332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7264332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264332 prefixEnd_7264332 := by exact prefixLift 7264332
  have htrace : WordTrace (prefixWord ++ tailWord_7264332) baseStart_7264332 baseEnd_7264332 := by
    simpa [prefixWord, tailWord_7264332, baseEnd_7264332] using wordTrace_append hprefix tailTrace_7264332
  have hstable : (prefixWord ++ tailWord_7264332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264332).length < 2 ^ (prefixWord ++ tailWord_7264332).sum := by decide
  have hdescent : baseEnd_7264332 < baseStart_7264332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264359 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 6, 2]
def baseStart_7264359 : Nat := 118140960795 + 7264359 * 2 ^ 59
def prefixEnd_7264359 : Nat := 4983230072969 + 3 ^ 40 * 7264359 * 2
def baseEnd_7264359 : Nat := 3730107813814648895704327

theorem tailTrace_7264359 : CollatzResearch.WordTrace tailWord_7264359 prefixEnd_7264359 3730107813814648895704327 := by
  unfold tailWord_7264359
  simp only [CollatzResearch.WordTrace]
  refine ⟨264952939489475471588820131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176635292992983647725880087 264952939489475471588820131)
  ·
    refine ⟨397429409234213207383230197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264952939489475471588820131 397429409234213207383230197)
    ·
      refine ⟨37259007115707488192177831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 397429409234213207383230197 37259007115707488192177831)
      ·
        refine ⟨55888510673561232288266747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37259007115707488192177831 55888510673561232288266747)
        ·
          refine ⟨83832766010341848432400121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55888510673561232288266747 83832766010341848432400121)
          ·
            refine ⟨62874574507756386324300091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 83832766010341848432400121 62874574507756386324300091)
            ·
              refine ⟨94311861761634579486450137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62874574507756386324300091 94311861761634579486450137)
              ·
                refine ⟨70733896321225934614837603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94311861761634579486450137 70733896321225934614837603)
                ·
                  refine ⟨106100844481838901922256405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70733896321225934614837603 106100844481838901922256405)
                  ·
                    refine ⟨4973477085086198527605769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106100844481838901922256405 4973477085086198527605769)
                    ·
                      refine ⟨3730107813814648895704327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973477085086198527605769 3730107813814648895704327)
                      ·
                        rfl

theorem cell23_7264359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_7264359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264359 prefixEnd_7264359 := by exact prefixLift 7264359
  have htrace : WordTrace (prefixWord ++ tailWord_7264359) baseStart_7264359 baseEnd_7264359 := by
    simpa [prefixWord, tailWord_7264359, baseEnd_7264359] using wordTrace_append hprefix tailTrace_7264359
  have hstable : (prefixWord ++ tailWord_7264359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264359).length < 2 ^ (prefixWord ++ tailWord_7264359).sum := by decide
  have hdescent : baseEnd_7264359 < baseStart_7264359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264420 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 1, 4]
def baseStart_7264420 : Nat := 118140960795 + 7264420 * 2 ^ 59
def prefixEnd_7264420 : Nat := 4983230072969 + 3 ^ 40 * 7264420 * 2
def baseEnd_7264420 : Nat := 1243379712044857719013849

theorem tailTrace_7264420 : CollatzResearch.WordTrace tailWord_7264420 prefixEnd_7264420 1243379712044857719013849 := by
  unfold tailWord_7264420
  simp only [CollatzResearch.WordTrace]
  refine ⟨132477582171127239503395357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176636776228169652671193809 132477582171127239503395357)
  ·
    refine ⟨49679093314172714813773259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132477582171127239503395357 49679093314172714813773259)
    ·
      refine ⟨74518639971259072220659889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49679093314172714813773259 74518639971259072220659889)
      ·
        refine ⟨55888979978444304165494917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74518639971259072220659889 55888979978444304165494917)
        ·
          refine ⟨10479183745958307031030297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55888979978444304165494917 10479183745958307031030297)
          ·
            refine ⟨7859387809468730273272723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10479183745958307031030297 7859387809468730273272723)
            ·
              refine ⟨11789081714203095409909085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859387809468730273272723 11789081714203095409909085)
              ·
                refine ⟨4420905642826160778715907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11789081714203095409909085 4420905642826160778715907)
                ·
                  refine ⟨6631358464239241168073861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420905642826160778715907 6631358464239241168073861)
                  ·
                    refine ⟨1243379712044857719013849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631358464239241168073861 1243379712044857719013849)
                    ·
                      rfl

theorem cell23_7264420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_7264420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264420 prefixEnd_7264420 := by exact prefixLift 7264420
  have htrace : WordTrace (prefixWord ++ tailWord_7264420) baseStart_7264420 baseEnd_7264420 := by
    simpa [prefixWord, tailWord_7264420, baseEnd_7264420] using wordTrace_append hprefix tailTrace_7264420
  have hstable : (prefixWord ++ tailWord_7264420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264420).length < 2 ^ (prefixWord ++ tailWord_7264420).sum := by decide
  have hdescent : baseEnd_7264420 < baseStart_7264420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264430 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_7264430 : Nat := 118140960795 + 7264430 * 2 ^ 59
def prefixEnd_7264430 : Nat := 4983230072969 + 3 ^ 40 * 7264430 * 2
def baseEnd_7264430 : Nat := 3730144270941118117916501

theorem tailTrace_7264430 : CollatzResearch.WordTrace tailWord_7264430 prefixEnd_7264430 3730144270941118117916501 := by
  unfold tailWord_7264430
  simp only [CollatzResearch.WordTrace]
  refine ⟨33119441134027281339331843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176637019381478833809769829 33119441134027281339331843)
  ·
    refine ⟨49679161701040922008997765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33119441134027281339331843 49679161701040922008997765)
    ·
      refine ⟨9314842818945172876687081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49679161701040922008997765 9314842818945172876687081)
      ·
        refine ⟨6986132114208879657515311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9314842818945172876687081 6986132114208879657515311)
        ·
          refine ⟨10479198171313319486272967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986132114208879657515311 10479198171313319486272967)
          ·
            refine ⟨15718797256969979229409451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479198171313319486272967 15718797256969979229409451)
            ·
              refine ⟨23578195885454968844114177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15718797256969979229409451 23578195885454968844114177)
              ·
                refine ⟨17683646914091226633085633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23578195885454968844114177 17683646914091226633085633)
                ·
                  refine ⟨13262735185568419974814225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17683646914091226633085633 13262735185568419974814225)
                  ·
                    refine ⟨9947051389176314981110669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13262735185568419974814225 9947051389176314981110669)
                    ·
                      refine ⟨3730144270941118117916501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947051389176314981110669 3730144270941118117916501)
                      ·
                        rfl

theorem cell23_7264430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_7264430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264430 prefixEnd_7264430 := by exact prefixLift 7264430
  have htrace : WordTrace (prefixWord ++ tailWord_7264430) baseStart_7264430 baseEnd_7264430 := by
    simpa [prefixWord, tailWord_7264430, baseEnd_7264430] using wordTrace_append hprefix tailTrace_7264430
  have hstable : (prefixWord ++ tailWord_7264430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264430).length < 2 ^ (prefixWord ++ tailWord_7264430).sum := by decide
  have hdescent : baseEnd_7264430 < baseStart_7264430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264437 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 1, 4]
def baseStart_7264437 : Nat := 118140960795 + 7264437 * 2 ^ 59
def prefixEnd_7264437 : Nat := 4983230072969 + 3 ^ 40 * 7264437 * 2
def baseEnd_7264437 : Nat := 1243382621768566530176323

theorem tailTrace_7264437 : CollatzResearch.WordTrace tailWord_7264437 prefixEnd_7264437 1243382621768566530176323 := by
  unfold tailWord_7264437
  simp only [CollatzResearch.WordTrace]
  refine ⟨264955784383192890910159565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176637189588795260606773043 264955784383192890910159565)
  ·
    refine ⟨99358419143697334091309837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264955784383192890910159565 99358419143697334091309837)
    ·
      refine ⟨37259407178886500284241189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99358419143697334091309837 37259407178886500284241189)
      ·
        refine ⟨6986138846041218803295223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37259407178886500284241189 6986138846041218803295223)
        ·
          refine ⟨10479208269061828204942835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986138846041218803295223 10479208269061828204942835)
          ·
            refine ⟨15718812403592742307414253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479208269061828204942835 15718812403592742307414253)
            ·
              refine ⟨5894554651347278365280345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15718812403592742307414253 5894554651347278365280345)
              ·
                refine ⟨4420915988510458773960259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5894554651347278365280345 4420915988510458773960259)
                ·
                  refine ⟨6631373982765688160940389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4420915988510458773960259 6631373982765688160940389)
                  ·
                    refine ⟨1243382621768566530176323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631373982765688160940389 1243382621768566530176323)
                    ·
                      rfl

theorem cell23_7264437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_7264437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264437 prefixEnd_7264437 := by exact prefixLift 7264437
  have htrace : WordTrace (prefixWord ++ tailWord_7264437) baseStart_7264437 baseEnd_7264437 := by
    simpa [prefixWord, tailWord_7264437, baseEnd_7264437] using wordTrace_append hprefix tailTrace_7264437
  have hstable : (prefixWord ++ tailWord_7264437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264437).length < 2 ^ (prefixWord ++ tailWord_7264437).sum := by decide
  have hdescent : baseEnd_7264437 < baseStart_7264437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264450 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7264450 : Nat := 118140960795 + 7264450 * 2 ^ 59
def prefixEnd_7264450 : Nat := 4983230072969 + 3 ^ 40 * 7264450 * 2
def baseEnd_7264450 : Nat := 414461615617134226629601

theorem tailTrace_7264450 : CollatzResearch.WordTrace tailWord_7264450 prefixEnd_7264450 414461615617134226629601 := by
  unfold tailWord_7264450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66239064633036448532595701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176637505688097196086921869 66239064633036448532595701)
  ·
    refine ⟨6209912309347167049930847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66239064633036448532595701 6209912309347167049930847)
    ·
      refine ⟨9314868464020750574896271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209912309347167049930847 9314868464020750574896271)
      ·
        refine ⟨13972302696031125862344407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314868464020750574896271 13972302696031125862344407)
        ·
          refine ⟨20958454044046688793516611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13972302696031125862344407 20958454044046688793516611)
          ·
            refine ⟨31437681066070033190274917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20958454044046688793516611 31437681066070033190274917)
            ·
              refine ⟨5894565199888131223176547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31437681066070033190274917 5894565199888131223176547)
              ·
                refine ⟨8841847799832196834764821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894565199888131223176547 8841847799832196834764821)
                ·
                  refine ⟨414461615617134226629601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8841847799832196834764821 414461615617134226629601)
                  ·
                    rfl

theorem cell23_7264450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7264450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264450 prefixEnd_7264450 := by exact prefixLift 7264450
  have htrace : WordTrace (prefixWord ++ tailWord_7264450) baseStart_7264450 baseEnd_7264450 := by
    simpa [prefixWord, tailWord_7264450, baseEnd_7264450] using wordTrace_append hprefix tailTrace_7264450
  have hstable : (prefixWord ++ tailWord_7264450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264450).length < 2 ^ (prefixWord ++ tailWord_7264450).sum := by decide
  have hdescent : baseEnd_7264450 < baseStart_7264450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264466 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7264466 : Nat := 118140960795 + 7264466 * 2 ^ 59
def prefixEnd_7264466 : Nat := 4983230072969 + 3 ^ 40 * 7264466 * 2
def baseEnd_7264466 : Nat := 3730162756244679977066335

theorem tailTrace_7264466 : CollatzResearch.WordTrace tailWord_7264466 prefixEnd_7264466 3730162756244679977066335 := by
  unfold tailWord_7264466
  simp only [CollatzResearch.WordTrace]
  refine ⟨66239210525021957215741313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176637894733391885908643501 66239210525021957215741313)
  ·
    refine ⟨49679407893766467911805985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66239210525021957215741313 49679407893766467911805985)
    ·
      refine ⟨37259555920324850933854489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49679407893766467911805985 37259555920324850933854489)
      ·
        refine ⟨27944666940243638200390867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37259555920324850933854489 27944666940243638200390867)
        ·
          refine ⟨41917000410365457300586301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27944666940243638200390867 41917000410365457300586301)
          ·
            refine ⟨15718875153887046487719863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41917000410365457300586301 15718875153887046487719863)
            ·
              refine ⟨23578312730830569731579795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15718875153887046487719863 23578312730830569731579795)
              ·
                refine ⟨35367469096245854597369693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23578312730830569731579795 35367469096245854597369693)
                ·
                  refine ⟨13262800911092195474013635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35367469096245854597369693 13262800911092195474013635)
                  ·
                    refine ⟨19894201366638293211020453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13262800911092195474013635 19894201366638293211020453)
                    ·
                      refine ⟨3730162756244679977066335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19894201366638293211020453 3730162756244679977066335)
                      ·
                        rfl

theorem cell23_7264466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7264466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264466 prefixEnd_7264466 := by exact prefixLift 7264466
  have htrace : WordTrace (prefixWord ++ tailWord_7264466) baseStart_7264466 baseEnd_7264466 := by
    simpa [prefixWord, tailWord_7264466, baseEnd_7264466] using wordTrace_append hprefix tailTrace_7264466
  have hstable : (prefixWord ++ tailWord_7264466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264466).length < 2 ^ (prefixWord ++ tailWord_7264466).sum := by decide
  have hdescent : baseEnd_7264466 < baseStart_7264466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264470 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_7264470 : Nat := 118140960795 + 7264470 * 2 ^ 59
def prefixEnd_7264470 : Nat := 4983230072969 + 3 ^ 40 * 7264470 * 2
def baseEnd_7264470 : Nat := 3730164810167297961416317

theorem tailTrace_7264470 : CollatzResearch.WordTrace tailWord_7264470 prefixEnd_7264470 3730164810167297961416317 := by
  unfold tailWord_7264470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16559811749504583596631929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 176637991994715558364073909 16559811749504583596631929)
  ·
    refine ⟨12419858812128437697473947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16559811749504583596631929 12419858812128437697473947)
    ·
      refine ⟨18629788218192656546210921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12419858812128437697473947 18629788218192656546210921)
      ·
        refine ⟨13972341163644492409658191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18629788218192656546210921 13972341163644492409658191)
        ·
          refine ⟨20958511745466738614487287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13972341163644492409658191 20958511745466738614487287)
          ·
            refine ⟨31437767618200107921730931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20958511745466738614487287 31437767618200107921730931)
            ·
              refine ⟨47156651427300161882596397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31437767618200107921730931 47156651427300161882596397)
              ·
                refine ⟨17683744285237560705973649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47156651427300161882596397 17683744285237560705973649)
                ·
                  refine ⟨13262808213928170529480237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17683744285237560705973649 13262808213928170529480237)
                  ·
                    refine ⟨4973553080223063948555089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13262808213928170529480237 4973553080223063948555089)
                    ·
                      refine ⟨3730164810167297961416317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973553080223063948555089 3730164810167297961416317)
                      ·
                        rfl

theorem cell23_7264470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_7264470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264470 prefixEnd_7264470 := by exact prefixLift 7264470
  have htrace : WordTrace (prefixWord ++ tailWord_7264470) baseStart_7264470 baseEnd_7264470 := by
    simpa [prefixWord, tailWord_7264470, baseEnd_7264470] using wordTrace_append hprefix tailTrace_7264470
  have hstable : (prefixWord ++ tailWord_7264470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264470).length < 2 ^ (prefixWord ++ tailWord_7264470).sum := by decide
  have hdescent : baseEnd_7264470 < baseStart_7264470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264499 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3]
def baseStart_7264499 : Nat := 118140960795 + 7264499 * 2 ^ 59
def prefixEnd_7264499 : Nat := 4983230072969 + 3 ^ 40 * 7264499 * 2
def baseEnd_7264499 : Nat := 3730179701106278347953683

theorem tailTrace_7264499 : CollatzResearch.WordTrace tailWord_7264499 prefixEnd_7264499 3730179701106278347953683 := by
  unfold tailWord_7264499
  simp only [CollatzResearch.WordTrace]
  refine ⟨264958045708968275498916551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176638697139312183665944367 264958045708968275498916551)
  ·
    refine ⟨397437068563452413248374827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264958045708968275498916551 397437068563452413248374827)
    ·
      refine ⟨596155602845178619872562241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397437068563452413248374827 596155602845178619872562241)
      ·
        refine ⟨447116702133883964904421681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 596155602845178619872562241 447116702133883964904421681)
        ·
          refine ⟨335337526600412973678316261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447116702133883964904421681 335337526600412973678316261)
          ·
            refine ⟨62875786237577432564684299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 335337526600412973678316261 62875786237577432564684299)
            ·
              refine ⟨94313679356366148847026449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62875786237577432564684299 94313679356366148847026449)
              ·
                refine ⟨70735259517274611635269837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94313679356366148847026449 70735259517274611635269837)
                ·
                  refine ⟨26525722318977979363226189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70735259517274611635269837 26525722318977979363226189)
                  ·
                    refine ⟨9947145869616742261209821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26525722318977979363226189 9947145869616742261209821)
                    ·
                      refine ⟨3730179701106278347953683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947145869616742261209821 3730179701106278347953683)
                      ·
                        rfl

theorem cell23_7264499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_7264499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264499 prefixEnd_7264499 := by exact prefixLift 7264499
  have htrace : WordTrace (prefixWord ++ tailWord_7264499) baseStart_7264499 baseEnd_7264499 := by
    simpa [prefixWord, tailWord_7264499, baseEnd_7264499] using wordTrace_append hprefix tailTrace_7264499
  have hstable : (prefixWord ++ tailWord_7264499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264499).length < 2 ^ (prefixWord ++ tailWord_7264499).sum := by decide
  have hdescent : baseEnd_7264499 < baseStart_7264499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264556 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 3, 4, 2]
def baseStart_7264556 : Nat := 118140960795 + 7264556 * 2 ^ 59
def prefixEnd_7264556 : Nat := 4983230072969 + 3 ^ 40 * 7264556 * 2
def baseEnd_7264556 : Nat := 3730208969503584624940921

theorem tailTrace_7264556 : CollatzResearch.WordTrace tailWord_7264556 prefixEnd_7264556 3730208969503584624940921 := by
  unfold tailWord_7264556
  simp only [CollatzResearch.WordTrace]
  refine ⟨132480062334880887116870761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176640083113174516155827681 132480062334880887116870761)
  ·
    refine ⟨99360046751160665337653071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132480062334880887116870761 99360046751160665337653071)
    ·
      refine ⟨149040070126740998006479607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99360046751160665337653071 149040070126740998006479607)
      ·
        refine ⟨223560105190111497009719411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149040070126740998006479607 223560105190111497009719411)
        ·
          refine ⟨335340157785167245514579117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223560105190111497009719411 335340157785167245514579117)
          ·
            refine ⟨125752559169437717067967169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335340157785167245514579117 125752559169437717067967169)
            ·
              refine ⟨94314419377078287800975377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125752559169437717067967169 94314419377078287800975377)
              ·
                refine ⟨70735814532808715850731533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94314419377078287800975377 70735814532808715850731533)
                ·
                  refine ⟨26525930449803268444024325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 70735814532808715850731533 26525930449803268444024325)
                  ·
                    refine ⟨4973611959338112833254561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26525930449803268444024325 4973611959338112833254561)
                    ·
                      refine ⟨3730208969503584624940921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973611959338112833254561 3730208969503584624940921)
                      ·
                        rfl

theorem cell23_7264556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 4, 2].length) (baseStart_7264556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264556 prefixEnd_7264556 := by exact prefixLift 7264556
  have htrace : WordTrace (prefixWord ++ tailWord_7264556) baseStart_7264556 baseEnd_7264556 := by
    simpa [prefixWord, tailWord_7264556, baseEnd_7264556] using wordTrace_append hprefix tailTrace_7264556
  have hstable : (prefixWord ++ tailWord_7264556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264556).length < 2 ^ (prefixWord ++ tailWord_7264556).sum := by decide
  have hdescent : baseEnd_7264556 < baseStart_7264556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264559 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3]
def baseStart_7264559 : Nat := 118140960795 + 7264559 * 2 ^ 59
def prefixEnd_7264559 : Nat := 4983230072969 + 3 ^ 40 * 7264559 * 2
def baseEnd_7264559 : Nat := 3730210509945548113203407

theorem tailTrace_7264559 : CollatzResearch.WordTrace tailWord_7264559 prefixEnd_7264559 3730210509945548113203407 := by
  unfold tailWord_7264559
  simp only [CollatzResearch.WordTrace]
  refine ⟨264960234088750905746100731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176640156059167270497400487 264960234088750905746100731)
  ·
    refine ⟨397440351133126358619151097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264960234088750905746100731 397440351133126358619151097)
    ·
      refine ⟨298080263349844768964363323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 397440351133126358619151097 298080263349844768964363323)
      ·
        refine ⟨447120395024767153446544985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298080263349844768964363323 447120395024767153446544985)
        ·
          refine ⟨335340296268575365084908739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447120395024767153446544985 335340296268575365084908739)
          ·
            refine ⟨503010444402863047627363109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 335340296268575365084908739 503010444402863047627363109)
            ·
              refine ⟨94314458325536821430130583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 503010444402863047627363109 94314458325536821430130583)
              ·
                refine ⟨141471687488305232145195875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94314458325536821430130583 141471687488305232145195875)
                ·
                  refine ⟨212207531232457848217793813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141471687488305232145195875 212207531232457848217793813)
                  ·
                    refine ⟨9947228026521461635209085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 212207531232457848217793813 9947228026521461635209085)
                    ·
                      refine ⟨3730210509945548113203407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947228026521461635209085 3730210509945548113203407)
                      ·
                        rfl

theorem cell23_7264559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 6, 3].length) (baseStart_7264559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264559 prefixEnd_7264559 := by exact prefixLift 7264559
  have htrace : WordTrace (prefixWord ++ tailWord_7264559) baseStart_7264559 baseEnd_7264559 := by
    simpa [prefixWord, tailWord_7264559, baseEnd_7264559] using wordTrace_append hprefix tailTrace_7264559
  have hstable : (prefixWord ++ tailWord_7264559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264559).length < 2 ^ (prefixWord ++ tailWord_7264559).sum := by decide
  have hdescent : baseEnd_7264559 < baseStart_7264559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264577 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7264577 : Nat := 118140960795 + 7264577 * 2 ^ 59
def prefixEnd_7264577 : Nat := 4983230072969 + 3 ^ 40 * 7264577 * 2
def baseEnd_7264577 : Nat := 3730219752597329042778325

theorem tailTrace_7264577 : CollatzResearch.WordTrace tailWord_7264577 prefixEnd_7264577 3730219752597329042778325 := by
  unfold tailWord_7264577
  simp only [CollatzResearch.WordTrace]
  refine ⟨264960890602685694820255985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176640593735123796546837323 264960890602685694820255985)
  ·
    refine ⟨198720667952014271115191989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264960890602685694820255985 198720667952014271115191989)
    ·
      refine ⟨18630062620501337917049249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 198720667952014271115191989 18630062620501337917049249)
      ·
        refine ⟨13972546965376003437786937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18630062620501337917049249 13972546965376003437786937)
        ·
          refine ⟨10479410224032002578340203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13972546965376003437786937 10479410224032002578340203)
          ·
            refine ⟨15719115336048003867510305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479410224032002578340203 15719115336048003867510305)
            ·
              refine ⟨11789336502036002900632729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719115336048003867510305 11789336502036002900632729)
              ·
                refine ⟨8842002376527002175474547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11789336502036002900632729 8842002376527002175474547)
                ·
                  refine ⟨13263003564790503263211821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8842002376527002175474547 13263003564790503263211821)
                  ·
                    refine ⟨4973626336796438723704433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13263003564790503263211821 4973626336796438723704433)
                    ·
                      refine ⟨3730219752597329042778325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973626336796438723704433 3730219752597329042778325)
                      ·
                        rfl

theorem cell23_7264577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7264577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264577 prefixEnd_7264577 := by exact prefixLift 7264577
  have htrace : WordTrace (prefixWord ++ tailWord_7264577) baseStart_7264577 baseEnd_7264577 := by
    simpa [prefixWord, tailWord_7264577, baseEnd_7264577] using wordTrace_append hprefix tailTrace_7264577
  have hstable : (prefixWord ++ tailWord_7264577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264577).length < 2 ^ (prefixWord ++ tailWord_7264577).sum := by decide
  have hdescent : baseEnd_7264577 < baseStart_7264577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264579 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 7]
def baseStart_7264579 : Nat := 118140960795 + 7264579 * 2 ^ 59
def prefixEnd_7264579 : Nat := 4983230072969 + 3 ^ 40 * 7264579 * 2
def baseEnd_7264579 : Nat := 414468975506515337217035

theorem tailTrace_7264579 : CollatzResearch.WordTrace tailWord_7264579 prefixEnd_7264579 414468975506515337217035 := by
  unfold tailWord_7264579
  simp only [CollatzResearch.WordTrace]
  refine ⟨264960963548678449161828791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176640642365785632774552527 264960963548678449161828791)
  ·
    refine ⟨397441445323017673742743187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264960963548678449161828791 397441445323017673742743187)
    ·
      refine ⟨596162167984526510614114781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397441445323017673742743187 596162167984526510614114781)
      ·
        refine ⟨223560812994197441480293043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596162167984526510614114781 223560812994197441480293043)
        ·
          refine ⟨335341219491296162220439565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223560812994197441480293043 335341219491296162220439565)
          ·
            refine ⟨125752957309236060832664837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335341219491296162220439565 125752957309236060832664837)
            ·
              refine ⟨23578679495481761406124657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 125752957309236060832664837 23578679495481761406124657)
              ·
                refine ⟨17684009621611321054593493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23578679495481761406124657 17684009621611321054593493)
                ·
                  refine ⟨414468975506515337217035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17684009621611321054593493 414468975506515337217035)
                  ·
                    rfl

theorem cell23_7264579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 7].length) (baseStart_7264579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264579 prefixEnd_7264579 := by exact prefixLift 7264579
  have htrace : WordTrace (prefixWord ++ tailWord_7264579) baseStart_7264579 baseEnd_7264579 := by
    simpa [prefixWord, tailWord_7264579, baseEnd_7264579] using wordTrace_append hprefix tailTrace_7264579
  have hstable : (prefixWord ++ tailWord_7264579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264579).length < 2 ^ (prefixWord ++ tailWord_7264579).sum := by decide
  have hdescent : baseEnd_7264579 < baseStart_7264579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264619 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5]
def baseStart_7264619 : Nat := 118140960795 + 7264619 * 2 ^ 59
def prefixEnd_7264619 : Nat := 4983230072969 + 3 ^ 40 * 7264619 * 2
def baseEnd_7264619 : Nat := 3730241318784817878453131

theorem tailTrace_7264619 : CollatzResearch.WordTrace tailWord_7264619 prefixEnd_7264619 3730241318784817878453131 := by
  unfold tailWord_7264619
  simp only [CollatzResearch.WordTrace]
  refine ⟨264962422468533535993284911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176641614979022357328856607 264962422468533535993284911)
  ·
    refine ⟨397443633702800303989927367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264962422468533535993284911 397443633702800303989927367)
    ·
      refine ⟨596165450554200455984891051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397443633702800303989927367 596165450554200455984891051)
      ·
        refine ⟨894248175831300683977336577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596165450554200455984891051 894248175831300683977336577)
        ·
          refine ⟨670686131873475512983002433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 894248175831300683977336577 670686131873475512983002433)
          ·
            refine ⟨503014598905106634737251825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 670686131873475512983002433 503014598905106634737251825)
            ·
              refine ⟨377260949178829976052938869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 503014598905106634737251825 377260949178829976052938869)
              ·
                refine ⟨35368213985515310254963019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 377260949178829976052938869 35368213985515310254963019)
                ·
                  refine ⟨53052320978272965382444529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35368213985515310254963019 53052320978272965382444529)
                  ·
                    refine ⟨39789240733704724036833397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53052320978272965382444529 39789240733704724036833397)
                    ·
                      refine ⟨3730241318784817878453131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39789240733704724036833397 3730241318784817878453131)
                      ·
                        rfl

theorem cell23_7264619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_7264619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264619 prefixEnd_7264619 := by exact prefixLift 7264619
  have htrace : WordTrace (prefixWord ++ tailWord_7264619) baseStart_7264619 baseEnd_7264619 := by
    simpa [prefixWord, tailWord_7264619, baseEnd_7264619] using wordTrace_append hprefix tailTrace_7264619
  have hstable : (prefixWord ++ tailWord_7264619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264619).length < 2 ^ (prefixWord ++ tailWord_7264619).sum := by decide
  have hdescent : baseEnd_7264619 < baseStart_7264619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264643 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 2, 5]
def baseStart_7264643 : Nat := 118140960795 + 7264643 * 2 ^ 59
def prefixEnd_7264643 : Nat := 4983230072969 + 3 ^ 40 * 7264643 * 2
def baseEnd_7264643 : Nat := 1243417880773508594851007

theorem tailTrace_7264643 : CollatzResearch.WordTrace tailWord_7264643 prefixEnd_7264643 1243417880773508594851007 := by
  unfold tailWord_7264643
  simp only [CollatzResearch.WordTrace]
  refine ⟨264963297820446588092158583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176642198546964392061439055 264963297820446588092158583)
  ·
    refine ⟨397444946730669882138237875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264963297820446588092158583 397444946730669882138237875)
    ·
      refine ⟨596167420096004823207356813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397444946730669882138237875 596167420096004823207356813)
      ·
        refine ⟨223562782536001808702758805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 596167420096004823207356813 223562782536001808702758805)
        ·
          refine ⟨10479505431375084782941819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 223562782536001808702758805 10479505431375084782941819)
          ·
            refine ⟨15719258147062627174412729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10479505431375084782941819 15719258147062627174412729)
            ·
              refine ⟨11789443610296970380809547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719258147062627174412729 11789443610296970380809547)
              ·
                refine ⟨17684165415445455571214321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789443610296970380809547 17684165415445455571214321)
                ·
                  refine ⟨13263124061584091678410741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17684165415445455571214321 13263124061584091678410741)
                  ·
                    refine ⟨1243417880773508594851007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13263124061584091678410741 1243417880773508594851007)
                    ·
                      rfl

theorem cell23_7264643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 2, 5].length) (baseStart_7264643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264643 prefixEnd_7264643 := by exact prefixLift 7264643
  have htrace : WordTrace (prefixWord ++ tailWord_7264643) baseStart_7264643 baseEnd_7264643 := by
    simpa [prefixWord, tailWord_7264643, baseEnd_7264643] using wordTrace_append hprefix tailTrace_7264643
  have hstable : (prefixWord ++ tailWord_7264643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264643).length < 2 ^ (prefixWord ++ tailWord_7264643).sum := by decide
  have hdescent : baseEnd_7264643 < baseStart_7264643 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264680 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_7264680 : Nat := 118140960795 + 7264680 * 2 ^ 59
def prefixEnd_7264680 : Nat := 4983230072969 + 3 ^ 40 * 7264680 * 2
def baseEnd_7264680 : Nat := 3730272641104742139790351

theorem tailTrace_7264680 : CollatzResearch.WordTrace tailWord_7264680 prefixEnd_7264680 3730272641104742139790351 := by
  unfold tailWord_7264680
  simp only [CollatzResearch.WordTrace]
  refine ⟨132482323660656271705627747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176643098214208362274170329 132482323660656271705627747)
  ·
    refine ⟨198723485490984407558441621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132482323660656271705627747 198723485490984407558441621)
    ·
      refine ⟨9315163382389894104301951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 198723485490984407558441621 9315163382389894104301951)
      ·
        refine ⟨13972745073584841156452927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315163382389894104301951 13972745073584841156452927)
        ·
          refine ⟨20959117610377261734679391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13972745073584841156452927 20959117610377261734679391)
          ·
            refine ⟨31438676415565892602019087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20959117610377261734679391 31438676415565892602019087)
            ·
              refine ⟨47158014623348838903028631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31438676415565892602019087 47158014623348838903028631)
              ·
                refine ⟨70737021935023258354542947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47158014623348838903028631 70737021935023258354542947)
                ·
                  refine ⟨106105532902534887531814421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 70737021935023258354542947 106105532902534887531814421)
                  ·
                    refine ⟨4973696854806322853053801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106105532902534887531814421 4973696854806322853053801)
                    ·
                      refine ⟨3730272641104742139790351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973696854806322853053801 3730272641104742139790351)
                      ·
                        rfl

theorem cell23_7264680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_7264680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264680 prefixEnd_7264680 := by exact prefixLift 7264680
  have htrace : WordTrace (prefixWord ++ tailWord_7264680) baseStart_7264680 baseEnd_7264680 := by
    simpa [prefixWord, tailWord_7264680, baseEnd_7264680] using wordTrace_append hprefix tailTrace_7264680
  have hstable : (prefixWord ++ tailWord_7264680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264680).length < 2 ^ (prefixWord ++ tailWord_7264680).sum := by decide
  have hdescent : baseEnd_7264680 < baseStart_7264680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264699 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 4, 9]
def baseStart_7264699 : Nat := 118140960795 + 7264699 * 2 ^ 59
def prefixEnd_7264699 : Nat := 4983230072969 + 3 ^ 40 * 7264699 * 2
def baseEnd_7264699 : Nat := 1243427465745725855150921

theorem tailTrace_7264699 : CollatzResearch.WordTrace tailWord_7264699 prefixEnd_7264699 1243427465745725855150921 := by
  unfold tailWord_7264699
  simp only [CollatzResearch.WordTrace]
  refine ⟨264965340308243709656197151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176643560205495806437464767 264965340308243709656197151)
  ·
    refine ⟨397448010462365564484295727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 264965340308243709656197151 397448010462365564484295727)
    ·
      refine ⟨596172015693548346726443591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 397448010462365564484295727 596172015693548346726443591)
      ·
        refine ⟨894258023540322520089665387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 596172015693548346726443591 894258023540322520089665387)
        ·
          refine ⟨1341387035310483780134498081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 894258023540322520089665387 1341387035310483780134498081)
          ·
            refine ⟨1006040276482862835100873561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1341387035310483780134498081 1006040276482862835100873561)
            ·
              refine ⟨754530207362147126325655171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1006040276482862835100873561 754530207362147126325655171)
              ·
                refine ⟨1131795311043220689488482757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 754530207362147126325655171 1131795311043220689488482757)
                ·
                  refine ⟨212211620820603879279090517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1131795311043220689488482757 212211620820603879279090517)
                  ·
                    refine ⟨1243427465745725855150921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 212211620820603879279090517 1243427465745725855150921)
                    ·
                      rfl

theorem cell23_7264699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 9].length) (baseStart_7264699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264699 prefixEnd_7264699 := by exact prefixLift 7264699
  have htrace : WordTrace (prefixWord ++ tailWord_7264699) baseStart_7264699 baseEnd_7264699 := by
    simpa [prefixWord, tailWord_7264699, baseEnd_7264699] using wordTrace_append hprefix tailTrace_7264699
  have hstable : (prefixWord ++ tailWord_7264699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264699).length < 2 ^ (prefixWord ++ tailWord_7264699).sum := by decide
  have hdescent : baseEnd_7264699 < baseStart_7264699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264700 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 2, 2, 3]
def baseStart_7264700 : Nat := 118140960795 + 7264700 * 2 ^ 59
def prefixEnd_7264700 : Nat := 4983230072969 + 3 ^ 40 * 7264700 * 2
def baseEnd_7264700 : Nat := 3730282910717832061540259

theorem tailTrace_7264700 : CollatzResearch.WordTrace tailWord_7264700 prefixEnd_7264700 3730282910717832061540259 := by
  unfold tailWord_7264700
  simp only [CollatzResearch.WordTrace]
  refine ⟨132482688390620043413491777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176643584520826724551322369 132482688390620043413491777)
  ·
    refine ⟨99362016292965032560118833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 132482688390620043413491777 99362016292965032560118833)
    ·
      refine ⟨74521512219723774420089125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99362016292965032560118833 74521512219723774420089125)
      ·
        refine ⟨13972783541198207703766711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74521512219723774420089125 13972783541198207703766711)
        ·
          refine ⟨20959175311797311555650067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13972783541198207703766711 20959175311797311555650067)
          ·
            refine ⟨31438762967695967333475101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20959175311797311555650067 31438762967695967333475101)
            ·
              refine ⟨11789536112885987750053163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31438762967695967333475101 11789536112885987750053163)
              ·
                refine ⟨17684304169328981625079745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789536112885987750053163 17684304169328981625079745)
                ·
                  refine ⟨13263228126996736218809809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17684304169328981625079745 13263228126996736218809809)
                  ·
                    refine ⟨9947421095247552164107357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13263228126996736218809809 9947421095247552164107357)
                    ·
                      refine ⟨3730282910717832061540259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947421095247552164107357 3730282910717832061540259)
                      ·
                        rfl

theorem cell23_7264700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_7264700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264700 prefixEnd_7264700 := by exact prefixLift 7264700
  have htrace : WordTrace (prefixWord ++ tailWord_7264700) baseStart_7264700 baseEnd_7264700 := by
    simpa [prefixWord, tailWord_7264700, baseEnd_7264700] using wordTrace_append hprefix tailTrace_7264700
  have hstable : (prefixWord ++ tailWord_7264700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264700).length < 2 ^ (prefixWord ++ tailWord_7264700).sum := by decide
  have hdescent : baseEnd_7264700 < baseStart_7264700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264730 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3]
def baseStart_7264730 : Nat := 118140960795 + 7264730 * 2 ^ 59
def prefixEnd_7264730 : Nat := 4983230072969 + 3 ^ 40 * 7264730 * 2
def baseEnd_7264730 : Nat := 3730298315137466944165121

theorem tailTrace_7264730 : CollatzResearch.WordTrace tailWord_7264730 prefixEnd_7264730 3730298315137466944165121 := by
  unfold tailWord_7264730
  simp only [CollatzResearch.WordTrace]
  refine ⟨66241617742782850487643911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 176644313980754267967050429 66241617742782850487643911)
  ·
    refine ⟨99362426614174275731465867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66241617742782850487643911 99362426614174275731465867)
    ·
      refine ⟨149043639921261413597198801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99362426614174275731465867 149043639921261413597198801)
      ·
        refine ⟨111782729940946060197899101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149043639921261413597198801 111782729940946060197899101)
        ·
          refine ⟨41918523727854772574212163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111782729940946060197899101 41918523727854772574212163)
          ·
            refine ⟨62877785591782158861318245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41918523727854772574212163 62877785591782158861318245)
            ·
              refine ⟨11789584798459154786497171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62877785591782158861318245 11789584798459154786497171)
              ·
                refine ⟨17684377197688732179745757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789584798459154786497171 17684377197688732179745757)
                ·
                  refine ⟨6631641449133274567404659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17684377197688732179745757 6631641449133274567404659)
                  ·
                    refine ⟨9947462173699911851106989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631641449133274567404659 9947462173699911851106989)
                    ·
                      refine ⟨3730298315137466944165121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947462173699911851106989 3730298315137466944165121)
                      ·
                        rfl

theorem cell23_7264730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_7264730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264730 prefixEnd_7264730 := by exact prefixLift 7264730
  have htrace : WordTrace (prefixWord ++ tailWord_7264730) baseStart_7264730 baseEnd_7264730 := by
    simpa [prefixWord, tailWord_7264730, baseEnd_7264730] using wordTrace_append hprefix tailTrace_7264730
  have hstable : (prefixWord ++ tailWord_7264730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264730).length < 2 ^ (prefixWord ++ tailWord_7264730).sum := by decide
  have hdescent : baseEnd_7264730 < baseStart_7264730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264750 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_7264750 : Nat := 118140960795 + 7264750 * 2 ^ 59
def prefixEnd_7264750 : Nat := 4983230072969 + 3 ^ 40 * 7264750 * 2
def baseEnd_7264750 : Nat := 1243436194916852288638343

theorem tailTrace_7264750 : CollatzResearch.WordTrace tailWord_7264750 prefixEnd_7264750 1243436194916852288638343 := by
  unfold tailWord_7264750
  simp only [CollatzResearch.WordTrace]
  refine ⟨33120900053882368170787963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 176644800287372630244202469 33120900053882368170787963)
  ·
    refine ⟨49681350080823552256181945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33120900053882368170787963 49681350080823552256181945)
    ·
      refine ⟨37261012560617664192136459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49681350080823552256181945 37261012560617664192136459)
      ·
        refine ⟨55891518840926496288204689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37261012560617664192136459 55891518840926496288204689)
        ·
          refine ⟨41918639130694872216153517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55891518840926496288204689 41918639130694872216153517)
          ·
            refine ⟨15719489674010577081057569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41918639130694872216153517 15719489674010577081057569)
            ·
              refine ⟨11789617255507932810793177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719489674010577081057569 11789617255507932810793177)
              ·
                refine ⟨8842212941630949608094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11789617255507932810793177 8842212941630949608094883)
                ·
                  refine ⟨13263319412446424412142325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8842212941630949608094883 13263319412446424412142325)
                  ·
                    refine ⟨1243436194916852288638343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13263319412446424412142325 1243436194916852288638343)
                    ·
                      rfl

theorem cell23_7264750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_7264750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264750 prefixEnd_7264750 := by exact prefixLift 7264750
  have htrace : WordTrace (prefixWord ++ tailWord_7264750) baseStart_7264750 baseEnd_7264750 := by
    simpa [prefixWord, tailWord_7264750, baseEnd_7264750] using wordTrace_append hprefix tailTrace_7264750
  have hstable : (prefixWord ++ tailWord_7264750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264750).length < 2 ^ (prefixWord ++ tailWord_7264750).sum := by decide
  have hdescent : baseEnd_7264750 < baseStart_7264750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264753 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_7264753 : Nat := 118140960795 + 7264753 * 2 ^ 59
def prefixEnd_7264753 : Nat := 4983230072969 + 3 ^ 40 * 7264753 * 2
def baseEnd_7264753 : Nat := 3730310125192520354177515

theorem tailTrace_7264753 : CollatzResearch.WordTrace tailWord_7264753 prefixEnd_7264753 3730310125192520354177515 := by
  unfold tailWord_7264753
  simp only [CollatzResearch.WordTrace]
  refine ⟨264967309850048076878662913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176644873233365384585775275 264967309850048076878662913)
  ·
    refine ⟨198725482387536057658997185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 264967309850048076878662913 198725482387536057658997185)
    ·
      refine ⟨149044111790652043244247889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 198725482387536057658997185 149044111790652043244247889)
      ·
        refine ⟨111783083842989032433185917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149044111790652043244247889 111783083842989032433185917)
        ·
          refine ⟨41918656441120887162444719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111783083842989032433185917 41918656441120887162444719)
          ·
            refine ⟨62877984661681330743667079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41918656441120887162444719 62877984661681330743667079)
            ·
              refine ⟨94316976992521996115500619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62877984661681330743667079 94316976992521996115500619)
              ·
                refine ⟨141475465488782994173250929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94316976992521996115500619 141475465488782994173250929)
                ·
                  refine ⟨106106599116587245629938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 141475465488782994173250929 106106599116587245629938197)
                  ·
                    refine ⟨4973746833590027138903353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 106106599116587245629938197 4973746833590027138903353)
                    ·
                      refine ⟨3730310125192520354177515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4973746833590027138903353 3730310125192520354177515)
                      ·
                        rfl

theorem cell23_7264753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_7264753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264753 prefixEnd_7264753 := by exact prefixLift 7264753
  have htrace : WordTrace (prefixWord ++ tailWord_7264753) baseStart_7264753 baseEnd_7264753 := by
    simpa [prefixWord, tailWord_7264753, baseEnd_7264753] using wordTrace_append hprefix tailTrace_7264753
  have hstable : (prefixWord ++ tailWord_7264753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264753).length < 2 ^ (prefixWord ++ tailWord_7264753).sum := by decide
  have hdescent : baseEnd_7264753 < baseStart_7264753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264781 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7264781 : Nat := 118140960795 + 7264781 * 2 ^ 59
def prefixEnd_7264781 : Nat := 4983230072969 + 3 ^ 40 * 7264781 * 2
def baseEnd_7264781 : Nat := 3730324502650846244627387

theorem tailTrace_7264781 : CollatzResearch.WordTrace tailWord_7264781 prefixEnd_7264781 3730324502650846244627387 := by
  unfold tailWord_7264781
  simp only [CollatzResearch.WordTrace]
  refine ⟨264968331093946637660682197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176645554062631091773788131 264968331093946637660682197)
  ·
    refine ⟨6210195260014374320172239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 264968331093946637660682197 6210195260014374320172239)
    ·
      refine ⟨9315292890021561480258359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6210195260014374320172239 9315292890021561480258359)
      ·
        refine ⟨13972939335032342220387539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9315292890021561480258359 13972939335032342220387539)
        ·
          refine ⟨20959409002548513330581309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13972939335032342220387539 20959409002548513330581309)
          ·
            refine ⟨7859778375955692498967991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20959409002548513330581309 7859778375955692498967991)
            ·
              refine ⟨11789667563933538748451987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859778375955692498967991 11789667563933538748451987)
              ·
                refine ⟨17684501345900308122677981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11789667563933538748451987 17684501345900308122677981)
                ·
                  refine ⟨6631688004712615546004243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17684501345900308122677981 6631688004712615546004243)
                  ·
                    refine ⟨9947532007068923319006365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631688004712615546004243 9947532007068923319006365)
                    ·
                      refine ⟨3730324502650846244627387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947532007068923319006365 3730324502650846244627387)
                      ·
                        rfl

theorem cell23_7264781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7264781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264781 prefixEnd_7264781 := by exact prefixLift 7264781
  have htrace : WordTrace (prefixWord ++ tailWord_7264781) baseStart_7264781 baseEnd_7264781 := by
    simpa [prefixWord, tailWord_7264781, baseEnd_7264781] using wordTrace_append hprefix tailTrace_7264781
  have hstable : (prefixWord ++ tailWord_7264781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264781).length < 2 ^ (prefixWord ++ tailWord_7264781).sum := by decide
  have hdescent : baseEnd_7264781 < baseStart_7264781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264797 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 2, 4]
def baseStart_7264797 : Nat := 118140960795 + 7264797 * 2 ^ 59
def prefixEnd_7264797 : Nat := 4983230072969 + 3 ^ 40 * 7264797 * 2
def baseEnd_7264797 : Nat := 1243444239447106060675771

theorem tailTrace_7264797 : CollatzResearch.WordTrace tailWord_7264797 prefixEnd_7264797 1243444239447106060675771 := by
  unfold tailWord_7264797
  simp only [CollatzResearch.WordTrace]
  refine ⟨264968914661888672393264645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176645943107925781595509763 264968914661888672393264645)
  ·
    refine ⟨49681671499104126073737121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 264968914661888672393264645 49681671499104126073737121)
    ·
      refine ⟨37261253624328094555302841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49681671499104126073737121 37261253624328094555302841)
      ·
        refine ⟨27945940218246070916477131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37261253624328094555302841 27945940218246070916477131)
        ·
          refine ⟨41918910327369106374715697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27945940218246070916477131 41918910327369106374715697)
          ·
            refine ⟨31439182745526829781036773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41918910327369106374715697 31439182745526829781036773)
            ·
              refine ⟨5894846764786280583944395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31439182745526829781036773 5894846764786280583944395)
              ·
                refine ⟨8842270147179420875916593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5894846764786280583944395 8842270147179420875916593)
                ·
                  refine ⟨6631702610384565656937445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842270147179420875916593 6631702610384565656937445)
                  ·
                    refine ⟨1243444239447106060675771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6631702610384565656937445 1243444239447106060675771)
                    ·
                      rfl

theorem cell23_7264797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_7264797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264797 prefixEnd_7264797 := by exact prefixLift 7264797
  have htrace : WordTrace (prefixWord ++ tailWord_7264797) baseStart_7264797 baseEnd_7264797 := by
    simpa [prefixWord, tailWord_7264797, baseEnd_7264797] using wordTrace_append hprefix tailTrace_7264797
  have hstable : (prefixWord ++ tailWord_7264797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264797).length < 2 ^ (prefixWord ++ tailWord_7264797).sum := by decide
  have hdescent : baseEnd_7264797 < baseStart_7264797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264804 : List Nat := [2, 3, 1, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_7264804 : Nat := 118140960795 + 7264804 * 2 ^ 59
def prefixEnd_7264804 : Nat := 4983230072969 + 3 ^ 40 * 7264804 * 2
def baseEnd_7264804 : Nat := 3730336312705899654639781

theorem tailTrace_7264804 : CollatzResearch.WordTrace tailWord_7264804 prefixEnd_7264804 3730336312705899654639781 := by
  unfold tailWord_7264804
  simp only [CollatzResearch.WordTrace]
  refine ⟨132484584986431656294384733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176646113315242208392512977 132484584986431656294384733)
  ·
    refine ⟨49681719369911871110394275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 132484584986431656294384733 49681719369911871110394275)
    ·
      refine ⟨74522579054867806665591413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49681719369911871110394275 74522579054867806665591413)
      ·
        refine ⟨6986491786393856874899195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74522579054867806665591413 6986491786393856874899195)
        ·
          refine ⟨10479737679590785312348793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6986491786393856874899195 10479737679590785312348793)
          ·
            refine ⟨7859803259693088984261595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10479737679590785312348793 7859803259693088984261595)
            ·
              refine ⟨11789704889539633476392393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7859803259693088984261595 11789704889539633476392393)
              ·
                refine ⟨8842278667154725107294295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11789704889539633476392393 8842278667154725107294295)
                ·
                  refine ⟨13263418000732087660941443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8842278667154725107294295 13263418000732087660941443)
                  ·
                    refine ⟨19895127001098131491412165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13263418000732087660941443 19895127001098131491412165)
                    ·
                      refine ⟨3730336312705899654639781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19895127001098131491412165 3730336312705899654639781)
                      ·
                        rfl

theorem cell23_7264804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_7264804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264804 prefixEnd_7264804 := by exact prefixLift 7264804
  have htrace : WordTrace (prefixWord ++ tailWord_7264804) baseStart_7264804 baseEnd_7264804 := by
    simpa [prefixWord, tailWord_7264804, baseEnd_7264804] using wordTrace_append hprefix tailTrace_7264804
  have hstable : (prefixWord ++ tailWord_7264804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264804).length < 2 ^ (prefixWord ++ tailWord_7264804).sum := by decide
  have hdescent : baseEnd_7264804 < baseStart_7264804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264816 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5]
def baseStart_7264816 : Nat := 118140960795 + 7264816 * 2 ^ 59
def prefixEnd_7264816 : Nat := 4983230072969 + 3 ^ 40 * 7264816 * 2
def baseEnd_7264816 : Nat := 3730342474473753607689725

theorem tailTrace_7264816 : CollatzResearch.WordTrace tailWord_7264816 prefixEnd_7264816 3730342474473753607689725 := by
  unfold tailWord_7264816
  simp only [CollatzResearch.WordTrace]
  refine ⟨132484803824409919319103151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 176646405099213225758804201 132484803824409919319103151)
  ·
    refine ⟨198727205736614878978654727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 132484803824409919319103151 198727205736614878978654727)
    ·
      refine ⟨298090808604922318467982091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 198727205736614878978654727 298090808604922318467982091)
      ·
        refine ⟨447136212907383477701973137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 298090808604922318467982091 447136212907383477701973137)
        ·
          refine ⟨335352159680537608276479853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 447136212907383477701973137 335352159680537608276479853)
          ·
            refine ⟨125757059880201603103679945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 335352159680537608276479853 125757059880201603103679945)
            ·
              refine ⟨94317794910151202327759959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 125757059880201603103679945 94317794910151202327759959)
              ·
                refine ⟨141476692365226803491639939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94317794910151202327759959 141476692365226803491639939)
                ·
                  refine ⟨212215038547840205237459909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 141476692365226803491639939 212215038547840205237459909)
                  ·
                    refine ⟨39790319727720038482023733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 212215038547840205237459909 39790319727720038482023733)
                    ·
                      refine ⟨3730342474473753607689725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39790319727720038482023733 3730342474473753607689725)
                      ·
                        rfl

theorem cell23_7264816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_7264816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264816 prefixEnd_7264816 := by exact prefixLift 7264816
  have htrace : WordTrace (prefixWord ++ tailWord_7264816) baseStart_7264816 baseEnd_7264816 := by
    simpa [prefixWord, tailWord_7264816, baseEnd_7264816] using wordTrace_append hprefix tailTrace_7264816
  have hstable : (prefixWord ++ tailWord_7264816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264816).length < 2 ^ (prefixWord ++ tailWord_7264816).sum := by decide
  have hdescent : baseEnd_7264816 < baseStart_7264816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7264837 : List Nat := [1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 3]
def baseStart_7264837 : Nat := 118140960795 + 7264837 * 2 ^ 59
def prefixEnd_7264837 : Nat := 4983230072969 + 3 ^ 40 * 7264837 * 2
def baseEnd_7264837 : Nat := 3730353257567498025527129

theorem tailTrace_7264837 : CollatzResearch.WordTrace tailWord_7264837 prefixEnd_7264837 3730353257567498025527129 := by
  unfold tailWord_7264837
  simp only [CollatzResearch.WordTrace]
  refine ⟨264970373581743759224720765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 176646915721162506149813843 264970373581743759224720765)
  ·
    refine ⟨99363890093153909709270287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 264970373581743759224720765 99363890093153909709270287)
    ·
      refine ⟨149045835139730864563905431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99363890093153909709270287 149045835139730864563905431)
      ·
        refine ⟨223568752709596296845858147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149045835139730864563905431 223568752709596296845858147)
        ·
          refine ⟨335353129064394445268787221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 223568752709596296845858147 335353129064394445268787221)
          ·
            refine ⟨15719677924893489621974401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 335353129064394445268787221 15719677924893489621974401)
            ·
              refine ⟨11789758443670117216480801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15719677924893489621974401 11789758443670117216480801)
              ·
                refine ⟨8842318832752587912360601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11789758443670117216480801 8842318832752587912360601)
                ·
                  refine ⟨6631739124564440934270451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8842318832752587912360601 6631739124564440934270451)
                  ·
                    refine ⟨9947608686846661401405677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6631739124564440934270451 9947608686846661401405677)
                    ·
                      refine ⟨3730353257567498025527129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9947608686846661401405677 3730353257567498025527129)
                      ·
                        rfl

theorem cell23_7264837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 1, 3].length) (baseStart_7264837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7264837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7264837 prefixEnd_7264837 := by exact prefixLift 7264837
  have htrace : WordTrace (prefixWord ++ tailWord_7264837) baseStart_7264837 baseEnd_7264837 := by
    simpa [prefixWord, tailWord_7264837, baseEnd_7264837] using wordTrace_append hprefix tailTrace_7264837
  have hstable : (prefixWord ++ tailWord_7264837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7264837).length < 2 ^ (prefixWord ++ tailWord_7264837).sum := by decide
  have hdescent : baseEnd_7264837 < baseStart_7264837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7264837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
