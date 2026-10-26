import V185TrunkScan23Chunk1239

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7346037 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7346037 : Nat := 118140960795 + 7346037 * 2 ^ 59
def prefixEnd_7346037 : Nat := 4983230072969 + 3 ^ 40 * 7346037 * 2
def baseEnd_7346037 : Nat := 3772047886712580330153697

theorem tailTrace_7346037 : CollatzResearch.WordTrace tailWord_7346037 prefixEnd_7346037 3772047886712580330153697 := by
  unfold tailWord_7346037
  simp only [CollatzResearch.WordTrace]
  refine ⟨267931980887570027080644365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178621320591713351387096243 267931980887570027080644365)
  ·
    refine ⟨100474492832838760155241637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267931980887570027080644365 100474492832838760155241637)
    ·
      refine ⟨18838967406157267529107807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100474492832838760155241637 18838967406157267529107807)
      ·
        refine ⟨28258451109235901293661711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18838967406157267529107807 28258451109235901293661711)
        ·
          refine ⟨42387676663853851940492567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28258451109235901293661711 42387676663853851940492567)
          ·
            refine ⟨63581514995780777910738851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42387676663853851940492567 63581514995780777910738851)
            ·
              refine ⟨95372272493671166866108277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63581514995780777910738851 95372272493671166866108277)
              ·
                refine ⟨8941150546281671893697651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95372272493671166866108277 8941150546281671893697651)
                ·
                  refine ⟨13411725819422507840546477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941150546281671893697651 13411725819422507840546477)
                  ·
                    refine ⟨5029397182283440440204929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13411725819422507840546477 5029397182283440440204929)
                    ·
                      refine ⟨3772047886712580330153697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029397182283440440204929 3772047886712580330153697)
                      ·
                        rfl

theorem cell23_7346037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7346037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346037 prefixEnd_7346037 := by exact prefixLift 7346037
  have htrace : WordTrace (prefixWord ++ tailWord_7346037) baseStart_7346037 baseEnd_7346037 := by
    simpa [prefixWord, tailWord_7346037, baseEnd_7346037] using wordTrace_append hprefix tailTrace_7346037
  have hstable : (prefixWord ++ tailWord_7346037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346037).length < 2 ^ (prefixWord ++ tailWord_7346037).sum := by decide
  have hdescent : baseEnd_7346037 < baseStart_7346037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346053 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_7346053 : Nat := 118140960795 + 7346053 * 2 ^ 59
def prefixEnd_7346053 : Nat := 4983230072969 + 3 ^ 40 * 7346053 * 2
def baseEnd_7346053 : Nat := 3772056102403052267553623

theorem tailTrace_7346053 : CollatzResearch.WordTrace tailWord_7346053 prefixEnd_7346053 3772056102403052267553623 := by
  unfold tailWord_7346053
  simp only [CollatzResearch.WordTrace]
  refine ⟨267932564455512061813226813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178621709637008041208817875 267932564455512061813226813)
  ·
    refine ⟨100474711670817023179960055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267932564455512061813226813 100474711670817023179960055)
    ·
      refine ⟨150712067506225534769940083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100474711670817023179960055 150712067506225534769940083)
      ·
        refine ⟨226068101259338302154910125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150712067506225534769940083 226068101259338302154910125)
        ·
          refine ⟨84775537972251863308091297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226068101259338302154910125 84775537972251863308091297)
          ·
            refine ⟨63581653479188897481068473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84775537972251863308091297 63581653479188897481068473)
            ·
              refine ⟨47686240109391673110801355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63581653479188897481068473 47686240109391673110801355)
              ·
                refine ⟨71529360164087509666202033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47686240109391673110801355 71529360164087509666202033)
                ·
                  refine ⟨53647020123065632249651525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71529360164087509666202033 53647020123065632249651525)
                  ·
                    refine ⟨10058816273074806046809661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53647020123065632249651525 10058816273074806046809661)
                    ·
                      refine ⟨3772056102403052267553623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058816273074806046809661 3772056102403052267553623)
                      ·
                        rfl

theorem cell23_7346053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_7346053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346053 prefixEnd_7346053 := by exact prefixLift 7346053
  have htrace : WordTrace (prefixWord ++ tailWord_7346053) baseStart_7346053 baseEnd_7346053 := by
    simpa [prefixWord, tailWord_7346053, baseEnd_7346053] using wordTrace_append hprefix tailTrace_7346053
  have hstable : (prefixWord ++ tailWord_7346053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346053).length < 2 ^ (prefixWord ++ tailWord_7346053).sum := by decide
  have hdescent : baseEnd_7346053 < baseStart_7346053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346083 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3]
def baseStart_7346083 : Nat := 118140960795 + 7346083 * 2 ^ 59
def prefixEnd_7346083 : Nat := 4983230072969 + 3 ^ 40 * 7346083 * 2
def baseEnd_7346083 : Nat := 3772071506822687150178485

theorem tailTrace_7346083 : CollatzResearch.WordTrace tailWord_7346083 prefixEnd_7346083 3772071506822687150178485 := by
  unfold tailWord_7346083
  simp only [CollatzResearch.WordTrace]
  refine ⟨267933658645403376936818903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178622439096935584624545935 267933658645403376936818903)
  ·
    refine ⟨401900487968105065405228355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267933658645403376936818903 401900487968105065405228355)
    ·
      refine ⟨602850731952157598107842533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401900487968105065405228355 602850731952157598107842533)
      ·
        refine ⟨113034512241029549645220475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602850731952157598107842533 113034512241029549645220475)
        ·
          refine ⟨169551768361544324467830713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113034512241029549645220475 169551768361544324467830713)
          ·
            refine ⟨127163826271158243350873035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169551768361544324467830713 127163826271158243350873035)
            ·
              refine ⟨190745739406737365026309553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127163826271158243350873035 190745739406737365026309553)
              ·
                refine ⟨143059304555053023769732165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190745739406737365026309553 143059304555053023769732165)
                ·
                  refine ⟨26823619604072441956824781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143059304555053023769732165 26823619604072441956824781)
                  ·
                    refine ⟨10058857351527165733809293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26823619604072441956824781 10058857351527165733809293)
                    ·
                      refine ⟨3772071506822687150178485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058857351527165733809293 3772071506822687150178485)
                      ·
                        rfl

theorem cell23_7346083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_7346083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346083 prefixEnd_7346083 := by exact prefixLift 7346083
  have htrace : WordTrace (prefixWord ++ tailWord_7346083) baseStart_7346083 baseEnd_7346083 := by
    simpa [prefixWord, tailWord_7346083, baseEnd_7346083] using wordTrace_append hprefix tailTrace_7346083
  have hstable : (prefixWord ++ tailWord_7346083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346083).length < 2 ^ (prefixWord ++ tailWord_7346083).sum := by decide
  have hdescent : baseEnd_7346083 < baseStart_7346083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346088 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_7346088 : Nat := 118140960795 + 7346088 * 2 ^ 59
def prefixEnd_7346088 : Nat := 4983230072969 + 3 ^ 40 * 7346088 * 2
def baseEnd_7346088 : Nat := 3772074074225959630615963

theorem tailTrace_7346088 : CollatzResearch.WordTrace tailWord_7346088 prefixEnd_7346088 3772074074225959630615963 := by
  unfold tailWord_7346088
  simp only [CollatzResearch.WordTrace]
  refine ⟨133966920505192631395375459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178622560673590175193833945 133966920505192631395375459)
  ·
    refine ⟨200950380757788947093063189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133966920505192631395375459 200950380757788947093063189)
    ·
      refine ⟨9419549098021356894987337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200950380757788947093063189 9419549098021356894987337)
      ·
        refine ⟨7064661823516017671240503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9419549098021356894987337 7064661823516017671240503)
        ·
          refine ⟨10596992735274026506860755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7064661823516017671240503 10596992735274026506860755)
          ·
            refine ⟨15895489102911039760291133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10596992735274026506860755 15895489102911039760291133)
            ·
              refine ⟨5960808413591639910109175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15895489102911039760291133 5960808413591639910109175)
              ·
                refine ⟨8941212620387459865163763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960808413591639910109175 8941212620387459865163763)
                ·
                  refine ⟨13411818930581189797745645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941212620387459865163763 13411818930581189797745645)
                  ·
                    refine ⟨5029432098967946174154617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13411818930581189797745645 5029432098967946174154617)
                    ·
                      refine ⟨3772074074225959630615963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029432098967946174154617 3772074074225959630615963)
                      ·
                        rfl

theorem cell23_7346088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_7346088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346088 prefixEnd_7346088 := by exact prefixLift 7346088
  have htrace : WordTrace (prefixWord ++ tailWord_7346088) baseStart_7346088 baseEnd_7346088 := by
    simpa [prefixWord, tailWord_7346088, baseEnd_7346088] using wordTrace_append hprefix tailTrace_7346088
  have hstable : (prefixWord ++ tailWord_7346088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346088).length < 2 ^ (prefixWord ++ tailWord_7346088).sum := by decide
  have hdescent : baseEnd_7346088 < baseStart_7346088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346123 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4]
def baseStart_7346123 : Nat := 118140960795 + 7346123 * 2 ^ 59
def prefixEnd_7346123 : Nat := 4983230072969 + 3 ^ 40 * 7346123 * 2
def baseEnd_7346123 : Nat := 3772092046048866993678301

theorem tailTrace_7346123 : CollatzResearch.WordTrace tailWord_7346123 prefixEnd_7346123 3772092046048866993678301 := by
  unfold tailWord_7346123
  simp only [CollatzResearch.WordTrace]
  refine ⟨267935117565258463768275023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178623411710172309178850015 267935117565258463768275023)
  ·
    refine ⟨401902676347887695652412535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267935117565258463768275023 401902676347887695652412535)
    ·
      refine ⟨602854014521831543478618803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401902676347887695652412535 602854014521831543478618803)
      ·
        refine ⟨904281021782747315217928205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602854014521831543478618803 904281021782747315217928205)
        ·
          refine ⟨339105383168530243206723077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 904281021782747315217928205 339105383168530243206723077)
          ·
            refine ⟨63582259344099420601260577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339105383168530243206723077 63582259344099420601260577)
            ·
              refine ⟨47686694508074565450945433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63582259344099420601260577 47686694508074565450945433)
              ·
                refine ⟨35765020881055924088209075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47686694508074565450945433 35765020881055924088209075)
                ·
                  refine ⟨53647531321583886132313613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35765020881055924088209075 53647531321583886132313613)
                  ·
                    refine ⟨20117824245593957299617605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53647531321583886132313613 20117824245593957299617605)
                    ·
                      refine ⟨3772092046048866993678301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20117824245593957299617605 3772092046048866993678301)
                      ·
                        rfl

theorem cell23_7346123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 4].length) (baseStart_7346123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346123 prefixEnd_7346123 := by exact prefixLift 7346123
  have htrace : WordTrace (prefixWord ++ tailWord_7346123) baseStart_7346123 baseEnd_7346123 := by
    simpa [prefixWord, tailWord_7346123, baseEnd_7346123] using wordTrace_append hprefix tailTrace_7346123
  have hstable : (prefixWord ++ tailWord_7346123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346123).length < 2 ^ (prefixWord ++ tailWord_7346123).sum := by decide
  have hdescent : baseEnd_7346123 < baseStart_7346123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346137 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 2, 5]
def baseStart_7346137 : Nat := 118140960795 + 7346137 * 2 ^ 59
def prefixEnd_7346137 : Nat := 4983230072969 + 3 ^ 40 * 7346137 * 2
def baseEnd_7346137 : Nat := 1257366411592676646301079

theorem tailTrace_7346137 : CollatzResearch.WordTrace tailWord_7346137 prefixEnd_7346137 1257366411592676646301079 := by
  unfold tailWord_7346137
  simp only [CollatzResearch.WordTrace]
  refine ⟨267935628187207744159284665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178623752124805162772856443 267935628187207744159284665)
  ·
    refine ⟨200951721140405808119463499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267935628187207744159284665 200951721140405808119463499)
    ·
      refine ⟨301427581710608712179195249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200951721140405808119463499 301427581710608712179195249)
      ·
        refine ⟨226070686282956534134396437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301427581710608712179195249 226070686282956534134396437)
        ·
          refine ⟨10597063419513587537549833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226070686282956534134396437 10597063419513587537549833)
          ·
            refine ⟨7947797564635190653162375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597063419513587537549833 7947797564635190653162375)
            ·
              refine ⟨11921696346952785979743563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947797564635190653162375 11921696346952785979743563)
              ·
                refine ⟨17882544520429178969615345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921696346952785979743563 17882544520429178969615345)
                ·
                  refine ⟨13411908390321884227211509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17882544520429178969615345 13411908390321884227211509)
                  ·
                    refine ⟨1257366411592676646301079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13411908390321884227211509 1257366411592676646301079)
                    ·
                      rfl

theorem cell23_7346137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 5].length) (baseStart_7346137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346137 prefixEnd_7346137 := by exact prefixLift 7346137
  have htrace : WordTrace (prefixWord ++ tailWord_7346137) baseStart_7346137 baseEnd_7346137 := by
    simpa [prefixWord, tailWord_7346137, baseEnd_7346137] using wordTrace_append hprefix tailTrace_7346137
  have hstable : (prefixWord ++ tailWord_7346137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346137).length < 2 ^ (prefixWord ++ tailWord_7346137).sum := by decide
  have hdescent : baseEnd_7346137 < baseStart_7346137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346160 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_7346160 : Nat := 118140960795 + 7346160 * 2 ^ 59
def prefixEnd_7346160 : Nat := 4983230072969 + 3 ^ 40 * 7346160 * 2
def baseEnd_7346160 : Nat := 3772111044833083348915631

theorem tailTrace_7346160 : CollatzResearch.WordTrace tailWord_7346160 prefixEnd_7346160 3772111044833083348915631 := by
  unfold tailWord_7346160
  simp only [CollatzResearch.WordTrace]
  refine ⟨133968233533062209543685967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178624311377416279391581289 133968233533062209543685967)
  ·
    refine ⟨200952350299593314315528951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133968233533062209543685967 200952350299593314315528951)
    ·
      refine ⟨301428525449389971473293427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200952350299593314315528951 301428525449389971473293427)
      ·
        refine ⟨452142788174084957209940141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301428525449389971473293427 452142788174084957209940141)
        ·
          refine ⟨169553545565281858953727553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452142788174084957209940141 169553545565281858953727553)
          ·
            refine ⟨127165159173961394215295665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169553545565281858953727553 127165159173961394215295665)
            ·
              refine ⟨95373869380471045661471749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127165159173961394215295665 95373869380471045661471749)
              ·
                refine ⟨17882600508838321061525953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95373869380471045661471749 17882600508838321061525953)
                ·
                  refine ⟨13411950381628740796144465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17882600508838321061525953 13411950381628740796144465)
                  ·
                    refine ⟨10058962786221555597108349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13411950381628740796144465 10058962786221555597108349)
                    ·
                      refine ⟨3772111044833083348915631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10058962786221555597108349 3772111044833083348915631)
                      ·
                        rfl

theorem cell23_7346160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_7346160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346160 prefixEnd_7346160 := by exact prefixLift 7346160
  have htrace : WordTrace (prefixWord ++ tailWord_7346160) baseStart_7346160 baseEnd_7346160 := by
    simpa [prefixWord, tailWord_7346160, baseEnd_7346160] using wordTrace_append hprefix tailTrace_7346160
  have hstable : (prefixWord ++ tailWord_7346160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346160).length < 2 ^ (prefixWord ++ tailWord_7346160).sum := by decide
  have hdescent : baseEnd_7346160 < baseStart_7346160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346174 : List Nat := [4, 2, 2, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_7346174 : Nat := 118140960795 + 7346174 * 2 ^ 59
def prefixEnd_7346174 : Nat := 4983230072969 + 3 ^ 40 * 7346174 * 2
def baseEnd_7346174 : Nat := 3772118233562246294140567

theorem tailTrace_7346174 : CollatzResearch.WordTrace tailWord_7346174 prefixEnd_7346174 3772118233562246294140567 := by
  unfold tailWord_7346174
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492122211009212434797697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178624651792049132985587717 33492122211009212434797697)
  ·
    refine ⟨25119091658256909326098273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33492122211009212434797697 25119091658256909326098273)
    ·
      refine ⟨18839318743692681994573705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25119091658256909326098273 18839318743692681994573705)
      ·
        refine ⟨14129489057769511495930279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18839318743692681994573705 14129489057769511495930279)
        ·
          refine ⟨21194233586654267243895419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129489057769511495930279 21194233586654267243895419)
          ·
            refine ⟨31791350379981400865843129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21194233586654267243895419 31791350379981400865843129)
            ·
              refine ⟨23843512784986050649382347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31791350379981400865843129 23843512784986050649382347)
              ·
                refine ⟨35765269177479075974073521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23843512784986050649382347 35765269177479075974073521)
                ·
                  refine ⟨26823951883109306980555141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35765269177479075974073521 26823951883109306980555141)
                  ·
                    refine ⟨5029490978082995058854089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26823951883109306980555141 5029490978082995058854089)
                    ·
                      refine ⟨3772118233562246294140567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029490978082995058854089 3772118233562246294140567)
                      ·
                        rfl

theorem cell23_7346174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_7346174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346174 prefixEnd_7346174 := by exact prefixLift 7346174
  have htrace : WordTrace (prefixWord ++ tailWord_7346174) baseStart_7346174 baseEnd_7346174 := by
    simpa [prefixWord, tailWord_7346174, baseEnd_7346174] using wordTrace_append hprefix tailTrace_7346174
  have hstable : (prefixWord ++ tailWord_7346174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346174).length < 2 ^ (prefixWord ++ tailWord_7346174).sum := by decide
  have hdescent : baseEnd_7346174 < baseStart_7346174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346190 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7346190 : Nat := 118140960795 + 7346190 * 2 ^ 59
def prefixEnd_7346190 : Nat := 4983230072969 + 3 ^ 40 * 7346190 * 2
def baseEnd_7346190 : Nat := 3772126449252718231540493

theorem tailTrace_7346190 : CollatzResearch.WordTrace tailWord_7346190 prefixEnd_7346190 3772126449252718231540493 := by
  unfold tailWord_7346190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492195157001966776370503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178625040837343822807309349 33492195157001966776370503)
  ·
    refine ⟨50238292735502950164555755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33492195157001966776370503 50238292735502950164555755)
    ·
      refine ⟨75357439103254425246833633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50238292735502950164555755 75357439103254425246833633)
      ·
        refine ⟨56518079327440818935125225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75357439103254425246833633 56518079327440818935125225)
        ·
          refine ⟨42388559495580614201343919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56518079327440818935125225 42388559495580614201343919)
          ·
            refine ⟨63582839243370921302015879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42388559495580614201343919 63582839243370921302015879)
            ·
              refine ⟨95374258865056381953023819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63582839243370921302015879 95374258865056381953023819)
              ·
                refine ⟨143061388297584572929535729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95374258865056381953023819 143061388297584572929535729)
                ·
                  refine ⟨107296041223188429697151797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143061388297584572929535729 107296041223188429697151797)
                  ·
                    refine ⟨10059003864673915284107981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107296041223188429697151797 10059003864673915284107981)
                    ·
                      refine ⟨3772126449252718231540493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059003864673915284107981 3772126449252718231540493)
                      ·
                        rfl

theorem cell23_7346190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7346190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346190 prefixEnd_7346190 := by exact prefixLift 7346190
  have htrace : WordTrace (prefixWord ++ tailWord_7346190) baseStart_7346190 baseEnd_7346190 := by
    simpa [prefixWord, tailWord_7346190, baseEnd_7346190] using wordTrace_append hprefix tailTrace_7346190
  have hstable : (prefixWord ++ tailWord_7346190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346190).length < 2 ^ (prefixWord ++ tailWord_7346190).sum := by decide
  have hdescent : baseEnd_7346190 < baseStart_7346190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346223 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 5, 6]
def baseStart_7346223 : Nat := 118140960795 + 7346223 * 2 ^ 59
def prefixEnd_7346223 : Nat := 4983230072969 + 3 ^ 40 * 7346223 * 2
def baseEnd_7346223 : Nat := 1257381131371438867475947

theorem tailTrace_7346223 : CollatzResearch.WordTrace tailWord_7346223 prefixEnd_7346223 1257381131371438867475947 := by
  unfold tailWord_7346223
  simp only [CollatzResearch.WordTrace]
  refine ⟨267938764864896180846915323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178625843243264120564610215 267938764864896180846915323)
  ·
    refine ⟨401908147297344271270372985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267938764864896180846915323 401908147297344271270372985)
    ·
      refine ⟨301431110473008203452779739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401908147297344271270372985 301431110473008203452779739)
      ·
        refine ⟨452146665709512305179169609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301431110473008203452779739 452146665709512305179169609)
        ·
          refine ⟨339109999282134228884377207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452146665709512305179169609 339109999282134228884377207)
          ·
            refine ⟨508664998923201343326565811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339109999282134228884377207 508664998923201343326565811)
            ·
              refine ⟨762997498384802014989848717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508664998923201343326565811 762997498384802014989848717)
              ·
                refine ⟨286124061894300755621193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762997498384802014989848717 286124061894300755621193269)
                ·
                  refine ⟨26824130802590695839486869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286124061894300755621193269 26824130802590695839486869)
                  ·
                    refine ⟨1257381131371438867475947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26824130802590695839486869 1257381131371438867475947)
                    ·
                      rfl

theorem cell23_7346223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 6].length) (baseStart_7346223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346223 prefixEnd_7346223 := by exact prefixLift 7346223
  have htrace : WordTrace (prefixWord ++ tailWord_7346223) baseStart_7346223 baseEnd_7346223 := by
    simpa [prefixWord, tailWord_7346223, baseEnd_7346223] using wordTrace_append hprefix tailTrace_7346223
  have hstable : (prefixWord ++ tailWord_7346223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346223).length < 2 ^ (prefixWord ++ tailWord_7346223).sum := by decide
  have hdescent : baseEnd_7346223 < baseStart_7346223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346224 : List Nat := [2, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3]
def baseStart_7346224 : Nat := 118140960795 + 7346224 * 2 ^ 59
def prefixEnd_7346224 : Nat := 4983230072969 + 3 ^ 40 * 7346224 * 2
def baseEnd_7346224 : Nat := 3772143907594971098515337

theorem tailTrace_7346224 : CollatzResearch.WordTrace tailWord_7346224 prefixEnd_7346224 3772143907594971098515337 := by
  unfold tailWord_7346224
  simp only [CollatzResearch.WordTrace]
  refine ⟨133969400668946279008850863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178625867558595038678467817 133969400668946279008850863)
  ·
    refine ⟨200954101003419418513276295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133969400668946279008850863 200954101003419418513276295)
    ·
      refine ⟨301431151505129127769914443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200954101003419418513276295 301431151505129127769914443)
      ·
        refine ⟨452146727257693691654871665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301431151505129127769914443 452146727257693691654871665)
        ·
          refine ⟨339110045443270268741153749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452146727257693691654871665 339110045443270268741153749)
          ·
            refine ⟨7947891690076646923620791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 339110045443270268741153749 7947891690076646923620791)
            ·
              refine ⟨11921837535114970385431187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947891690076646923620791 11921837535114970385431187)
              ·
                refine ⟨17882756302672455578146781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921837535114970385431187 17882756302672455578146781)
                ·
                  refine ⟨6706033613502170841805043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17882756302672455578146781 6706033613502170841805043)
                  ·
                    refine ⟨10059050420253256262707565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706033613502170841805043 10059050420253256262707565)
                    ·
                      refine ⟨3772143907594971098515337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059050420253256262707565 3772143907594971098515337)
                      ·
                        rfl

theorem cell23_7346224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_7346224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346224 prefixEnd_7346224 := by exact prefixLift 7346224
  have htrace : WordTrace (prefixWord ++ tailWord_7346224) baseStart_7346224 baseEnd_7346224 := by
    simpa [prefixWord, tailWord_7346224, baseEnd_7346224] using wordTrace_append hprefix tailTrace_7346224
  have hstable : (prefixWord ++ tailWord_7346224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346224).length < 2 ^ (prefixWord ++ tailWord_7346224).sum := by decide
  have hdescent : baseEnd_7346224 < baseStart_7346224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346264 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4]
def baseStart_7346264 : Nat := 118140960795 + 7346264 * 2 ^ 59
def prefixEnd_7346264 : Nat := 4983230072969 + 3 ^ 40 * 7346264 * 2
def baseEnd_7346264 : Nat := 3772164446821150942015153

theorem tailTrace_7346264 : CollatzResearch.WordTrace tailWord_7346264 prefixEnd_7346264 3772164446821150942015153 := by
  unfold tailWord_7346264
  simp only [CollatzResearch.WordTrace]
  refine ⟨133970130128873822424578923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178626840171831763232771897 133970130128873822424578923)
  ·
    refine ⟨200955195193310733636868385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133970130128873822424578923 200955195193310733636868385)
    ·
      refine ⟨150716396394983050227651289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200955195193310733636868385 150716396394983050227651289)
      ·
        refine ⟨113037297296237287670738467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150716396394983050227651289 113037297296237287670738467)
        ·
          refine ⟨169555945944355931506107701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113037297296237287670738467 169555945944355931506107701)
          ·
            refine ⟨15895869932283368578697597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169555945944355931506107701 15895869932283368578697597)
            ·
              refine ⟨5960951224606263217011599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15895869932283368578697597 5960951224606263217011599)
              ·
                refine ⟨8941426836909394825517399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960951224606263217011599 8941426836909394825517399)
                ·
                  refine ⟨13412140255364092238276099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941426836909394825517399 13412140255364092238276099)
                  ·
                    refine ⟨20118210383046138357414149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13412140255364092238276099 20118210383046138357414149)
                    ·
                      refine ⟨3772164446821150942015153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20118210383046138357414149 3772164446821150942015153)
                      ·
                        rfl

theorem cell23_7346264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 1, 1, 4].length) (baseStart_7346264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346264 prefixEnd_7346264 := by exact prefixLift 7346264
  have htrace : WordTrace (prefixWord ++ tailWord_7346264) baseStart_7346264 baseEnd_7346264 := by
    simpa [prefixWord, tailWord_7346264, baseEnd_7346264] using wordTrace_append hprefix tailTrace_7346264
  have hstable : (prefixWord ++ tailWord_7346264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346264).length < 2 ^ (prefixWord ++ tailWord_7346264).sum := by decide
  have hdescent : baseEnd_7346264 < baseStart_7346264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346281 : List Nat := [1, 2, 1, 1, 1, 5, 3, 4, 1, 2, 2]
def baseStart_7346281 : Nat := 118140960795 + 7346281 * 2 ^ 59
def prefixEnd_7346281 : Nat := 4983230072969 + 3 ^ 40 * 7346281 * 2
def baseEnd_7346281 : Nat := 3772173175992277375502575

theorem tailTrace_7346281 : CollatzResearch.WordTrace tailWord_7346281 prefixEnd_7346281 3772173175992277375502575 := by
  unfold tailWord_7346281
  simp only [CollatzResearch.WordTrace]
  refine ⟨267940880298686056752526697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178627253532457371168351131 267940880298686056752526697)
  ·
    refine ⟨200955660224014542564395023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267940880298686056752526697 200955660224014542564395023)
    ·
      refine ⟨301433490336021813846592535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200955660224014542564395023 301433490336021813846592535)
      ·
        refine ⟨452150235504032720769888803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301433490336021813846592535 452150235504032720769888803)
        ·
          refine ⟨678225353256049081154833205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452150235504032720769888803 678225353256049081154833205)
          ·
            refine ⟨63583626867754601358265613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 678225353256049081154833205 63583626867754601358265613)
            ·
              refine ⟨23843860075407975509349605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63583626867754601358265613 23843860075407975509349605)
              ·
                refine ⟨4470723764138995408003051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23843860075407975509349605 4470723764138995408003051)
                ·
                  refine ⟨6706085646208493112004577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470723764138995408003051 6706085646208493112004577)
                  ·
                    refine ⟨5029564234656369834003433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706085646208493112004577 5029564234656369834003433)
                    ·
                      refine ⟨3772173175992277375502575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029564234656369834003433 3772173175992277375502575)
                      ·
                        rfl

theorem cell23_7346281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 4, 1, 2, 2].length) (baseStart_7346281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346281 prefixEnd_7346281 := by exact prefixLift 7346281
  have htrace : WordTrace (prefixWord ++ tailWord_7346281) baseStart_7346281 baseEnd_7346281 := by
    simpa [prefixWord, tailWord_7346281, baseEnd_7346281] using wordTrace_append hprefix tailTrace_7346281
  have hstable : (prefixWord ++ tailWord_7346281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346281).length < 2 ^ (prefixWord ++ tailWord_7346281).sum := by decide
  have hdescent : baseEnd_7346281 < baseStart_7346281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346294 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_7346294 : Nat := 118140960795 + 7346294 * 2 ^ 59
def prefixEnd_7346294 : Nat := 4983230072969 + 3 ^ 40 * 7346294 * 2
def baseEnd_7346294 : Nat := 3772179851240785824640015

theorem tailTrace_7346294 : CollatzResearch.WordTrace tailWord_7346294 prefixEnd_7346294 3772179851240785824640015 := by
  unfold tailWord_7346294
  simp only [CollatzResearch.WordTrace]
  refine ⟨16746334652977434998296871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178627569631759306648499957 16746334652977434998296871)
  ·
    refine ⟨25119501979466152497445307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16746334652977434998296871 25119501979466152497445307)
    ·
      refine ⟨37679252969199228746167961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25119501979466152497445307 37679252969199228746167961)
      ·
        refine ⟨28259439726899421559625971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37679252969199228746167961 28259439726899421559625971)
        ·
          refine ⟨42389159590349132339438957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28259439726899421559625971 42389159590349132339438957)
          ·
            refine ⟨15895934846380924627289609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42389159590349132339438957 15895934846380924627289609)
            ·
              refine ⟨11921951134785693470467207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15895934846380924627289609 11921951134785693470467207)
              ·
                refine ⟨17882926702178540205700811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921951134785693470467207 17882926702178540205700811)
                ·
                  refine ⟨26824390053267810308551217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882926702178540205700811 26824390053267810308551217)
                  ·
                    refine ⟨20118292539950857731413413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26824390053267810308551217 20118292539950857731413413)
                    ·
                      refine ⟨3772179851240785824640015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20118292539950857731413413 3772179851240785824640015)
                      ·
                        rfl

theorem cell23_7346294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_7346294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346294 prefixEnd_7346294 := by exact prefixLift 7346294
  have htrace : WordTrace (prefixWord ++ tailWord_7346294) baseStart_7346294 baseEnd_7346294 := by
    simpa [prefixWord, tailWord_7346294, baseEnd_7346294] using wordTrace_append hprefix tailTrace_7346294
  have hstable : (prefixWord ++ tailWord_7346294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346294).length < 2 ^ (prefixWord ++ tailWord_7346294).sum := by decide
  have hdescent : baseEnd_7346294 < baseStart_7346294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346297 : List Nat := [1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 3]
def baseStart_7346297 : Nat := 118140960795 + 7346297 * 2 ^ 59
def prefixEnd_7346297 : Nat := 4983230072969 + 3 ^ 40 * 7346297 * 2
def baseEnd_7346297 : Nat := 3772181391682749312902501

theorem tailTrace_7346297 : CollatzResearch.WordTrace tailWord_7346297 prefixEnd_7346297 3772181391682749312902501 := by
  unfold tailWord_7346297
  simp only [CollatzResearch.WordTrace]
  refine ⟨267941463866628091485109145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178627642577752060990072763 267941463866628091485109145)
  ·
    refine ⟨200956097899971068613831859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267941463866628091485109145 200956097899971068613831859)
    ·
      refine ⟨301434146849956602920747789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200956097899971068613831859 301434146849956602920747789)
      ·
        refine ⟨113037805068733726095280421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301434146849956602920747789 113037805068733726095280421)
        ·
          refine ⟨21194588450387573642865079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113037805068733726095280421 21194588450387573642865079)
          ·
            refine ⟨31791882675581360464297619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21194588450387573642865079 31791882675581360464297619)
            ·
              refine ⟨47687824013372040696446429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31791882675581360464297619 47687824013372040696446429)
              ·
                refine ⟨17882934005014515261167411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47687824013372040696446429 17882934005014515261167411)
                ·
                  refine ⟨26824401007521772891751117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882934005014515261167411 26824401007521772891751117)
                  ·
                    refine ⟨10059150377820664834406669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26824401007521772891751117 10059150377820664834406669)
                    ·
                      refine ⟨3772181391682749312902501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059150377820664834406669 3772181391682749312902501)
                      ·
                        rfl

theorem cell23_7346297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_7346297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346297 prefixEnd_7346297 := by exact prefixLift 7346297
  have htrace : WordTrace (prefixWord ++ tailWord_7346297) baseStart_7346297 baseEnd_7346297 := by
    simpa [prefixWord, tailWord_7346297, baseEnd_7346297] using wordTrace_append hprefix tailTrace_7346297
  have hstable : (prefixWord ++ tailWord_7346297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346297).length < 2 ^ (prefixWord ++ tailWord_7346297).sum := by decide
  have hdescent : baseEnd_7346297 < baseStart_7346297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346318 : List Nat := [4, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7346318 : Nat := 118140960795 + 7346318 * 2 ^ 59
def prefixEnd_7346318 : Nat := 4983230072969 + 3 ^ 40 * 7346318 * 2
def baseEnd_7346318 : Nat := 3772192174776493730739905

theorem tailTrace_7346318 : CollatzResearch.WordTrace tailWord_7346318 prefixEnd_7346318 3772192174776493730739905 := by
  unfold tailWord_7346318
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492778724944001508952951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178628153199701341381082405 33492778724944001508952951)
  ·
    refine ⟨50239168087416002263429427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33492778724944001508952951 50239168087416002263429427)
    ·
      refine ⟨75358752131124003395144141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50239168087416002263429427 75358752131124003395144141)
      ·
        refine ⟨28259532049171501273179053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75358752131124003395144141 28259532049171501273179053)
        ·
          refine ⟨10597324518439312977442145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28259532049171501273179053 10597324518439312977442145)
          ·
            refine ⟨7947993388829484733081609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597324518439312977442145 7947993388829484733081609)
            ·
              refine ⟨5960995041622113549811207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7947993388829484733081609 5960995041622113549811207)
              ·
                refine ⟨8941492562433170324716811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960995041622113549811207 8941492562433170324716811)
                ·
                  refine ⟨13412238843649755487075217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8941492562433170324716811 13412238843649755487075217)
                  ·
                    refine ⟨10059179132737316615306413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13412238843649755487075217 10059179132737316615306413)
                    ·
                      refine ⟨3772192174776493730739905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059179132737316615306413 3772192174776493730739905)
                      ·
                        rfl

theorem cell23_7346318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7346318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346318 prefixEnd_7346318 := by exact prefixLift 7346318
  have htrace : WordTrace (prefixWord ++ tailWord_7346318) baseStart_7346318 baseEnd_7346318 := by
    simpa [prefixWord, tailWord_7346318, baseEnd_7346318] using wordTrace_append hprefix tailTrace_7346318
  have hstable : (prefixWord ++ tailWord_7346318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346318).length < 2 ^ (prefixWord ++ tailWord_7346318).sum := by decide
  have hdescent : baseEnd_7346318 < baseStart_7346318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346360 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 7]
def baseStart_7346360 : Nat := 118140960795 + 7346360 * 2 ^ 59
def prefixEnd_7346360 : Nat := 4983230072969 + 3 ^ 40 * 7346360 * 2
def baseEnd_7346360 : Nat := 419134860107109174046079

theorem tailTrace_7346360 : CollatzResearch.WordTrace tailWord_7346360 prefixEnd_7346360 419134860107109174046079 := by
  unfold tailWord_7346360
  simp only [CollatzResearch.WordTrace]
  refine ⟨133971880832699926622326267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178629174443599902163101689 133971880832699926622326267)
  ·
    refine ⟨200957821249049889933489401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133971880832699926622326267 200957821249049889933489401)
    ·
      refine ⟨150718365936787417450117051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200957821249049889933489401 150718365936787417450117051)
      ·
        refine ⟨226077548905181126175175577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150718365936787417450117051 226077548905181126175175577)
        ·
          refine ⟨169558161678885844631381683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226077548905181126175175577 169558161678885844631381683)
          ·
            refine ⟨254337242518328766947072525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169558161678885844631381683 254337242518328766947072525)
            ·
              refine ⟨95376465944373287605152197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254337242518328766947072525 95376465944373287605152197)
              ·
                refine ⟨17883087364569991425966037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95376465944373287605152197 17883087364569991425966037)
                ·
                  refine ⟨419134860107109174046079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17883087364569991425966037 419134860107109174046079)
                  ·
                    rfl

theorem cell23_7346360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 7].length) (baseStart_7346360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346360 prefixEnd_7346360 := by exact prefixLift 7346360
  have htrace : WordTrace (prefixWord ++ tailWord_7346360) baseStart_7346360 baseEnd_7346360 := by
    simpa [prefixWord, tailWord_7346360, baseEnd_7346360] using wordTrace_append hprefix tailTrace_7346360
  have hstable : (prefixWord ++ tailWord_7346360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346360).length < 2 ^ (prefixWord ++ tailWord_7346360).sum := by decide
  have hdescent : baseEnd_7346360 < baseStart_7346360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346377 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 5]
def baseStart_7346377 : Nat := 118140960795 + 7346377 * 2 ^ 59
def prefixEnd_7346377 : Nat := 4983230072969 + 3 ^ 40 * 7346377 * 2
def baseEnd_7346377 : Nat := 419135830015012111100237

theorem tailTrace_7346377 : CollatzResearch.WordTrace tailWord_7346377 prefixEnd_7346377 419135830015012111100237 := by
  unfold tailWord_7346377
  simp only [CollatzResearch.WordTrace]
  refine ⟨267944381706338265148021385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178629587804225510098680923 267944381706338265148021385)
  ·
    refine ⟨200958286279753698861016039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267944381706338265148021385 200958286279753698861016039)
    ·
      refine ⟨301437429419630548291524059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200958286279753698861016039 301437429419630548291524059)
      ·
        refine ⟨452156144129445822437286089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301437429419630548291524059 452156144129445822437286089)
        ·
          refine ⟨339117108097084366827964567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452156144129445822437286089 339117108097084366827964567)
          ·
            refine ⟨508675662145626550241946851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339117108097084366827964567 508675662145626550241946851)
            ·
              refine ⟨763013493218439825362920277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508675662145626550241946851 763013493218439825362920277)
              ·
                refine ⟨4470782186826795851735861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 763013493218439825362920277 4470782186826795851735861)
                ·
                  refine ⟨419135830015012111100237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470782186826795851735861 419135830015012111100237)
                  ·
                    rfl

theorem cell23_7346377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 5].length) (baseStart_7346377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346377 prefixEnd_7346377 := by exact prefixLift 7346377
  have htrace : WordTrace (prefixWord ++ tailWord_7346377) baseStart_7346377 baseEnd_7346377 := by
    simpa [prefixWord, tailWord_7346377, baseEnd_7346377] using wordTrace_append hprefix tailTrace_7346377
  have hstable : (prefixWord ++ tailWord_7346377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346377).length < 2 ^ (prefixWord ++ tailWord_7346377).sum := by decide
  have hdescent : baseEnd_7346377 < baseStart_7346377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346405 : List Nat := [1, 3, 1, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7346405 : Nat := 118140960795 + 7346405 * 2 ^ 59
def prefixEnd_7346405 : Nat := 4983230072969 + 3 ^ 40 * 7346405 * 2
def baseEnd_7346405 : Nat := 3772236847593434890352005

theorem tailTrace_7346405 : CollatzResearch.WordTrace tailWord_7346405 prefixEnd_7346405 3772236847593434890352005 := by
  unfold tailWord_7346405
  simp only [CollatzResearch.WordTrace]
  refine ⟨267945402950236825930040669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178630268633491217286693779 267945402950236825930040669)
  ·
    refine ⟨100479526106338809723765251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267945402950236825930040669 100479526106338809723765251)
    ·
      refine ⟨150719289159508214585647877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100479526106338809723765251 150719289159508214585647877)
      ·
        refine ⟨28259866717407790234808977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150719289159508214585647877 28259866717407790234808977)
        ·
          refine ⟨21194900038055842676106733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28259866717407790234808977 21194900038055842676106733)
          ·
            refine ⟨7948087514270941003540025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21194900038055842676106733 7948087514270941003540025)
            ·
              refine ⟨5961065635703205752655019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7948087514270941003540025 5961065635703205752655019)
              ·
                refine ⟨8941598453554808628982529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961065635703205752655019 8941598453554808628982529)
                ·
                  refine ⟨6706198840166106471736897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8941598453554808628982529 6706198840166106471736897)
                  ·
                    refine ⟨5029649130124579853802673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706198840166106471736897 5029649130124579853802673)
                    ·
                      refine ⟨3772236847593434890352005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029649130124579853802673 3772236847593434890352005)
                      ·
                        rfl

theorem cell23_7346405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7346405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346405 prefixEnd_7346405 := by exact prefixLift 7346405
  have htrace : WordTrace (prefixWord ++ tailWord_7346405) baseStart_7346405 baseEnd_7346405 := by
    simpa [prefixWord, tailWord_7346405, baseEnd_7346405] using wordTrace_append hprefix tailTrace_7346405
  have hstable : (prefixWord ++ tailWord_7346405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346405).length < 2 ^ (prefixWord ++ tailWord_7346405).sum := by decide
  have hdescent : baseEnd_7346405 < baseStart_7346405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346434 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 1, 2, 5]
def baseStart_7346434 : Nat := 118140960795 + 7346434 * 2 ^ 59
def prefixEnd_7346434 : Nat := 4983230072969 + 3 ^ 40 * 7346434 * 2
def baseEnd_7346434 : Nat := 3772251738532415276889371

theorem tailTrace_7346434 : CollatzResearch.WordTrace tailWord_7346434 prefixEnd_7346434 3772251738532415276889371 := by
  unfold tailWord_7346434
  simp only [CollatzResearch.WordTrace]
  refine ⟨66986615166782940970711589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178630973778087842588564237 66986615166782940970711589)
  ·
    refine ⟨12559990343771801432008423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66986615166782940970711589 12559990343771801432008423)
    ·
      refine ⟨18839985515657702148012635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12559990343771801432008423 18839985515657702148012635)
      ·
        refine ⟨28259978273486553222018953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18839985515657702148012635 28259978273486553222018953)
        ·
          refine ⟨21194983705114914916514215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28259978273486553222018953 21194983705114914916514215)
          ·
            refine ⟨31792475557672372374771323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21194983705114914916514215 31792475557672372374771323)
            ·
              refine ⟨47688713336508558562156985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31792475557672372374771323 47688713336508558562156985)
              ·
                refine ⟨35766535002381418921617739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47688713336508558562156985 35766535002381418921617739)
                ·
                  refine ⟨53649802503572128382426609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35766535002381418921617739 53649802503572128382426609)
                  ·
                    refine ⟨40237351877679096286819957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53649802503572128382426609 40237351877679096286819957)
                    ·
                      refine ⟨3772251738532415276889371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40237351877679096286819957 3772251738532415276889371)
                      ·
                        rfl

theorem cell23_7346434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_7346434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346434 prefixEnd_7346434 := by exact prefixLift 7346434
  have htrace : WordTrace (prefixWord ++ tailWord_7346434) baseStart_7346434 baseEnd_7346434 := by
    simpa [prefixWord, tailWord_7346434, baseEnd_7346434] using wordTrace_append hprefix tailTrace_7346434
  have hstable : (prefixWord ++ tailWord_7346434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346434).length < 2 ^ (prefixWord ++ tailWord_7346434).sum := by decide
  have hdescent : baseEnd_7346434 < baseStart_7346434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346437 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 7, 4]
def baseStart_7346437 : Nat := 118140960795 + 7346437 * 2 ^ 59
def prefixEnd_7346437 : Nat := 4983230072969 + 3 ^ 40 * 7346437 * 2
def baseEnd_7346437 : Nat := 1257417759658126255050619

theorem tailTrace_7346437 : CollatzResearch.WordTrace tailWord_7346437 prefixEnd_7346437 1257417759658126255050619 := by
  unfold tailWord_7346437
  simp only [CollatzResearch.WordTrace]
  refine ⟨267946570086120895395205565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178631046724080596930137043 267946570086120895395205565)
  ·
    refine ⟨100479963782295335773202087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267946570086120895395205565 100479963782295335773202087)
    ·
      refine ⟨150719945673443003659803131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100479963782295335773202087 150719945673443003659803131)
      ·
        refine ⟨226079918510164505489704697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150719945673443003659803131 226079918510164505489704697)
        ·
          refine ⟨169559938882623379117278523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226079918510164505489704697 169559938882623379117278523)
          ·
            refine ⟨254339908323935068675917785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169559938882623379117278523 254339908323935068675917785)
            ·
              refine ⟨190754931242951301506938339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254339908323935068675917785 190754931242951301506938339)
              ·
                refine ⟨286132396864426952260407509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190754931242951301506938339 286132396864426952260407509)
                ·
                  refine ⟨6706228051510006693603301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 286132396864426952260407509 6706228051510006693603301)
                  ·
                    refine ⟨1257417759658126255050619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706228051510006693603301 1257417759658126255050619)
                    ·
                      rfl

theorem cell23_7346437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_7346437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346437 prefixEnd_7346437 := by exact prefixLift 7346437
  have htrace : WordTrace (prefixWord ++ tailWord_7346437) baseStart_7346437 baseEnd_7346437 := by
    simpa [prefixWord, tailWord_7346437, baseEnd_7346437] using wordTrace_append hprefix tailTrace_7346437
  have hstable : (prefixWord ++ tailWord_7346437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346437).length < 2 ^ (prefixWord ++ tailWord_7346437).sum := by decide
  have hdescent : baseEnd_7346437 < baseStart_7346437 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346444 : List Nat := [2, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2]
def baseStart_7346444 : Nat := 118140960795 + 7346444 * 2 ^ 59
def prefixEnd_7346444 : Nat := 4983230072969 + 3 ^ 40 * 7346444 * 2
def baseEnd_7346444 : Nat := 3772256873338960237764325

theorem tailTrace_7346444 : CollatzResearch.WordTrace tailWord_7346444 prefixEnd_7346444 3772256873338960237764325 := by
  unfold tailWord_7346444
  simp only [CollatzResearch.WordTrace]
  refine ⟨133973412698547767795355193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178631216931397023727140257 133973412698547767795355193)
  ·
    refine ⟨100480059523910825846516395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133973412698547767795355193 100480059523910825846516395)
    ·
      refine ⟨150720089285866238769774593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100480059523910825846516395 150720089285866238769774593)
      ·
        refine ⟨113040066964399679077330945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150720089285866238769774593 113040066964399679077330945)
        ·
          refine ⟨84780050223299759307998209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113040066964399679077330945 84780050223299759307998209)
          ·
            refine ⟨63585037667474819480998657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84780050223299759307998209 63585037667474819480998657)
            ·
              refine ⟨47688778250606114610748993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63585037667474819480998657 47688778250606114610748993)
              ·
                refine ⟨35766583687954585958061745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47688778250606114610748993 35766583687954585958061745)
                ·
                  refine ⟨26824937765965939468546309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35766583687954585958061745 26824937765965939468546309)
                  ·
                    refine ⟨5029675831118613650352433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26824937765965939468546309 5029675831118613650352433)
                    ·
                      refine ⟨3772256873338960237764325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029675831118613650352433 3772256873338960237764325)
                      ·
                        rfl

theorem cell23_7346444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_7346444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346444 prefixEnd_7346444 := by exact prefixLift 7346444
  have htrace : WordTrace (prefixWord ++ tailWord_7346444) baseStart_7346444 baseEnd_7346444 := by
    simpa [prefixWord, tailWord_7346444, baseEnd_7346444] using wordTrace_append hprefix tailTrace_7346444
  have hstable : (prefixWord ++ tailWord_7346444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346444).length < 2 ^ (prefixWord ++ tailWord_7346444).sum := by decide
  have hdescent : baseEnd_7346444 < baseStart_7346444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346467 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 6]
def baseStart_7346467 : Nat := 118140960795 + 7346467 * 2 ^ 59
def prefixEnd_7346467 : Nat := 4983230072969 + 3 ^ 40 * 7346467 * 2
def baseEnd_7346467 : Nat := 419140964821557071975191

theorem tailTrace_7346467 : CollatzResearch.WordTrace tailWord_7346467 prefixEnd_7346467 419140964821557071975191 := by
  unfold tailWord_7346467
  simp only [CollatzResearch.WordTrace]
  refine ⟨267947664276012210518797655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178631776184008140345865103 267947664276012210518797655)
  ·
    refine ⟨401921496414018315778196483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267947664276012210518797655 401921496414018315778196483)
    ·
      refine ⟨602882244621027473667294725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401921496414018315778196483 602882244621027473667294725)
      ·
        refine ⟨113040420866442651312617761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602882244621027473667294725 113040420866442651312617761)
        ·
          refine ⟨84780315649831988484463321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113040420866442651312617761 84780315649831988484463321)
          ·
            refine ⟨63585236737373991363347491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84780315649831988484463321 63585236737373991363347491)
            ·
              refine ⟨95377855106060987045021237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63585236737373991363347491 95377855106060987045021237)
              ·
                refine ⟨8941673916193217535470741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95377855106060987045021237 8941673916193217535470741)
                ·
                  refine ⟨419140964821557071975191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8941673916193217535470741 419140964821557071975191)
                  ·
                    rfl

theorem cell23_7346467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 6].length) (baseStart_7346467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346467 prefixEnd_7346467 := by exact prefixLift 7346467
  have htrace : WordTrace (prefixWord ++ tailWord_7346467) baseStart_7346467 baseEnd_7346467 := by
    simpa [prefixWord, tailWord_7346467, baseEnd_7346467] using wordTrace_append hprefix tailTrace_7346467
  have hstable : (prefixWord ++ tailWord_7346467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346467).length < 2 ^ (prefixWord ++ tailWord_7346467).sum := by decide
  have hdescent : baseEnd_7346467 < baseStart_7346467 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346537 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 5]
def baseStart_7346537 : Nat := 118140960795 + 7346537 * 2 ^ 59
def prefixEnd_7346537 : Nat := 4983230072969 + 3 ^ 40 * 7346537 * 2
def baseEnd_7346537 : Nat := 3772304627039828373901397

theorem tailTrace_7346537 : CollatzResearch.WordTrace tailWord_7346537 prefixEnd_7346537 3772304627039828373901397 := by
  unfold tailWord_7346537
  simp only [CollatzResearch.WordTrace]
  refine ⟨267950217385758612473845865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178633478257172408315897243 267950217385758612473845865)
  ·
    refine ⟨200962663039318959355384399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267950217385758612473845865 200962663039318959355384399)
    ·
      refine ⟨301443994558978439033076599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200962663039318959355384399 301443994558978439033076599)
      ·
        refine ⟨452165991838467658549614899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301443994558978439033076599 452165991838467658549614899)
        ·
          refine ⟨678248987757701487824422349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452165991838467658549614899 678248987757701487824422349)
          ·
            refine ⟨254343370409138057934158381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678248987757701487824422349 254343370409138057934158381)
            ·
              refine ⟨95378763903426771725309393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254343370409138057934158381 95378763903426771725309393)
              ·
                refine ⟨71534072927570078793982045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95378763903426771725309393 71534072927570078793982045)
                ·
                  refine ⟨26825277347838779547743267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71534072927570078793982045 26825277347838779547743267)
                  ·
                    refine ⟨40237916021758169321614901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26825277347838779547743267 40237916021758169321614901)
                    ·
                      refine ⟨3772304627039828373901397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40237916021758169321614901 3772304627039828373901397)
                      ·
                        rfl

theorem cell23_7346537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 1, 5].length) (baseStart_7346537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346537 prefixEnd_7346537 := by exact prefixLift 7346537
  have htrace : WordTrace (prefixWord ++ tailWord_7346537) baseStart_7346537 baseEnd_7346537 := by
    simpa [prefixWord, tailWord_7346537, baseEnd_7346537] using wordTrace_append hprefix tailTrace_7346537
  have hstable : (prefixWord ++ tailWord_7346537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346537).length < 2 ^ (prefixWord ++ tailWord_7346537).sum := by decide
  have hdescent : baseEnd_7346537 < baseStart_7346537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346544 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 4, 4]
def baseStart_7346544 : Nat := 118140960795 + 7346544 * 2 ^ 59
def prefixEnd_7346544 : Nat := 4983230072969 + 3 ^ 40 * 7346544 * 2
def baseEnd_7346544 : Nat := 1257436073801469948837955

theorem tailTrace_7346544 : CollatzResearch.WordTrace tailWord_7346544 prefixEnd_7346544 1257436073801469948837955 := by
  unfold tailWord_7346544
  simp only [CollatzResearch.WordTrace]
  refine ⟨133975236348366626334675343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178633648464488835112900457 133975236348366626334675343)
  ·
    refine ⟨200962854522549939502013015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133975236348366626334675343 200962854522549939502013015)
    ·
      refine ⟨301444281783824909253019523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200962854522549939502013015 301444281783824909253019523)
      ·
        refine ⟨452166422675737363879529285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301444281783824909253019523 452166422675737363879529285)
        ·
          refine ⟨84781204251700755727411741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452166422675737363879529285 84781204251700755727411741)
          ·
            refine ⟨31792951594387783397779403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84781204251700755727411741 31792951594387783397779403)
            ·
              refine ⟨47689427391581675096669105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31792951594387783397779403 47689427391581675096669105)
              ·
                refine ⟨35767070543686256322501829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47689427391581675096669105 35767070543686256322501829)
                ·
                  refine ⟨6706325726941173060469093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35767070543686256322501829 6706325726941173060469093)
                  ·
                    refine ⟨1257436073801469948837955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706325726941173060469093 1257436073801469948837955)
                    ·
                      rfl

theorem cell23_7346544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 4].length) (baseStart_7346544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346544 prefixEnd_7346544 := by exact prefixLift 7346544
  have htrace : WordTrace (prefixWord ++ tailWord_7346544) baseStart_7346544 baseEnd_7346544 := by
    simpa [prefixWord, tailWord_7346544, baseEnd_7346544] using wordTrace_append hprefix tailTrace_7346544
  have hstable : (prefixWord ++ tailWord_7346544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346544).length < 2 ^ (prefixWord ++ tailWord_7346544).sum := by decide
  have hdescent : baseEnd_7346544 < baseStart_7346544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346557 : List Nat := [1, 4, 1, 1, 2, 3, 11]
def baseStart_7346557 : Nat := 118140960795 + 7346557 * 2 ^ 59
def prefixEnd_7346557 : Nat := 4983230072969 + 3 ^ 40 * 7346557 * 2
def baseEnd_7346557 : Nat := 46571788847566892538905

theorem tailTrace_7346557 : CollatzResearch.WordTrace tailWord_7346557 prefixEnd_7346557 46571788847566892538905 := by
  unfold tailWord_7346557
  simp only [CollatzResearch.WordTrace]
  refine ⟨267950946845686155889573925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178633964563790770593049283 267950946845686155889573925)
  ·
    refine ⟨50240802533566154229295111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267950946845686155889573925 50240802533566154229295111)
    ·
      refine ⟨75361203800349231343942667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50240802533566154229295111 75361203800349231343942667)
      ·
        refine ⟨113041805700523847015914001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75361203800349231343942667 113041805700523847015914001)
        ·
          refine ⟨84781354275392885261935501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113041805700523847015914001 84781354275392885261935501)
          ·
            refine ⟨31793007853272331973225813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84781354275392885261935501 31793007853272331973225813)
            ·
              refine ⟨46571788847566892538905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31793007853272331973225813 46571788847566892538905)
              ·
                rfl

theorem cell23_7346557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 11].length) (baseStart_7346557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346557 prefixEnd_7346557 := by exact prefixLift 7346557
  have htrace : WordTrace (prefixWord ++ tailWord_7346557) baseStart_7346557 baseEnd_7346557 := by
    simpa [prefixWord, tailWord_7346557, baseEnd_7346557] using wordTrace_append hprefix tailTrace_7346557
  have hstable : (prefixWord ++ tailWord_7346557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346557).length < 2 ^ (prefixWord ++ tailWord_7346557).sum := by decide
  have hdescent : baseEnd_7346557 < baseStart_7346557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346561 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 4, 4]
def baseStart_7346561 : Nat := 118140960795 + 7346561 * 2 ^ 59
def prefixEnd_7346561 : Nat := 4983230072969 + 3 ^ 40 * 7346561 * 2
def baseEnd_7346561 : Nat := 1257438983525178760000429

theorem tailTrace_7346561 : CollatzResearch.WordTrace tailWord_7346561 prefixEnd_7346561 1257438983525178760000429 := by
  unfold tailWord_7346561
  simp only [CollatzResearch.WordTrace]
  refine ⟨267951092737671664572719537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178634061825114443048479691 267951092737671664572719537)
  ·
    refine ⟨200963319553253748429539653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267951092737671664572719537 200963319553253748429539653)
    ·
      refine ⟨37680622416235077830538685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200963319553253748429539653 37680622416235077830538685)
      ·
        refine ⟨14130233406088154186452007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37680622416235077830538685 14130233406088154186452007)
        ·
          refine ⟨21195350109132231279678011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130233406088154186452007 21195350109132231279678011)
          ·
            refine ⟨31793025163698346919517017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21195350109132231279678011 31793025163698346919517017)
            ·
              refine ⟨23844768872773760189637763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31793025163698346919517017 23844768872773760189637763)
              ·
                refine ⟨35767153309160640284456645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23844768872773760189637763 35767153309160640284456645)
                ·
                  refine ⟨6706341245467620053335621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35767153309160640284456645 6706341245467620053335621)
                  ·
                    refine ⟨1257438983525178760000429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706341245467620053335621 1257438983525178760000429)
                    ·
                      rfl

theorem cell23_7346561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_7346561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346561 prefixEnd_7346561 := by exact prefixLift 7346561
  have htrace : WordTrace (prefixWord ++ tailWord_7346561) baseStart_7346561 baseEnd_7346561 := by
    simpa [prefixWord, tailWord_7346561, baseEnd_7346561] using wordTrace_append hprefix tailTrace_7346561
  have hstable : (prefixWord ++ tailWord_7346561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346561).length < 2 ^ (prefixWord ++ tailWord_7346561).sum := by decide
  have hdescent : baseEnd_7346561 < baseStart_7346561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346562 : List Nat := [3, 4, 2, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_7346562 : Nat := 118140960795 + 7346562 * 2 ^ 59
def prefixEnd_7346562 : Nat := 4983230072969 + 3 ^ 40 * 7346562 * 2
def baseEnd_7346562 : Nat := 3772317464056190776088783

theorem tailTrace_7346562 : CollatzResearch.WordTrace tailWord_7346562 prefixEnd_7346562 3772317464056190776088783 := by
  unfold tailWord_7346562
  simp only [CollatzResearch.WordTrace]
  refine ⟨66987782302667010435876485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178634086140445361162337293 66987782302667010435876485)
  ·
    refine ⟨12560209181750064456726841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66987782302667010435876485 12560209181750064456726841)
    ·
      refine ⟨9420156886312548342545131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12560209181750064456726841 9420156886312548342545131)
      ·
        refine ⟨14130235329468822513817697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420156886312548342545131 14130235329468822513817697)
        ·
          refine ⟨10597676497101616885363273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14130235329468822513817697 10597676497101616885363273)
          ·
            refine ⟨7948257372826212664022455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597676497101616885363273 7948257372826212664022455)
            ·
              refine ⟨11922386059239318996033683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948257372826212664022455 11922386059239318996033683)
              ·
                refine ⟨17883579088858978494050525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11922386059239318996033683 17883579088858978494050525)
                ·
                  refine ⟨6706342158322116935268947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17883579088858978494050525 6706342158322116935268947)
                  ·
                    refine ⟨10059513237483175402903421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706342158322116935268947 10059513237483175402903421)
                    ·
                      refine ⟨3772317464056190776088783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059513237483175402903421 3772317464056190776088783)
                      ·
                        rfl

theorem cell23_7346562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_7346562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346562 prefixEnd_7346562 := by exact prefixLift 7346562
  have htrace : WordTrace (prefixWord ++ tailWord_7346562) baseStart_7346562 baseEnd_7346562 := by
    simpa [prefixWord, tailWord_7346562, baseEnd_7346562] using wordTrace_append hprefix tailTrace_7346562
  have hstable : (prefixWord ++ tailWord_7346562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346562).length < 2 ^ (prefixWord ++ tailWord_7346562).sum := by decide
  have hdescent : baseEnd_7346562 < baseStart_7346562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346574 : List Nat := [4, 1, 1, 4, 1, 1, 1, 10]
def baseStart_7346574 : Nat := 118140960795 + 7346574 * 2 ^ 59
def prefixEnd_7346574 : Nat := 4983230072969 + 3 ^ 40 * 7346574 * 2
def baseEnd_7346574 : Nat := 139715689845334989968101

theorem tailTrace_7346574 : CollatzResearch.WordTrace tailWord_7346574 prefixEnd_7346574 139715689845334989968101 := by
  unfold tailWord_7346574
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493945860828070974117847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178634377924416378528628517 33493945860828070974117847)
  ·
    refine ⟨50240918791242106461176771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33493945860828070974117847 50240918791242106461176771)
    ·
      refine ⟨75361378186863159691765157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50240918791242106461176771 75361378186863159691765157)
      ·
        refine ⟨14130258410036842442205967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75361378186863159691765157 14130258410036842442205967)
        ·
          refine ⟨21195387615055263663308951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130258410036842442205967 21195387615055263663308951)
          ·
            refine ⟨31793081422582895494963427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21195387615055263663308951 31793081422582895494963427)
            ·
              refine ⟨47689622133874343242445141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31793081422582895494963427 47689622133874343242445141)
              ·
                refine ⟨139715689845334989968101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47689622133874343242445141 139715689845334989968101)
                ·
                  rfl

theorem cell23_7346574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_7346574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346574 prefixEnd_7346574 := by exact prefixLift 7346574
  have htrace : WordTrace (prefixWord ++ tailWord_7346574) baseStart_7346574 baseEnd_7346574 := by
    simpa [prefixWord, tailWord_7346574, baseEnd_7346574] using wordTrace_append hprefix tailTrace_7346574
  have hstable : (prefixWord ++ tailWord_7346574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346574).length < 2 ^ (prefixWord ++ tailWord_7346574).sum := by decide
  have hdescent : baseEnd_7346574 < baseStart_7346574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346605 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7346605 : Nat := 118140960795 + 7346605 * 2 ^ 59
def prefixEnd_7346605 : Nat := 4983230072969 + 3 ^ 40 * 7346605 * 2
def baseEnd_7346605 : Nat := 3772339543724334107851085

theorem tailTrace_7346605 : CollatzResearch.WordTrace tailWord_7346605 prefixEnd_7346605 3772339543724334107851085 := by
  unfold tailWord_7346605
  simp only [CollatzResearch.WordTrace]
  refine ⟨267952697549512260087321269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178635131699674840058214179 267952697549512260087321269)
  ·
    refine ⟨25120565395266774383186369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267952697549512260087321269 25120565395266774383186369)
    ·
      refine ⟨18840424046450080787389777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25120565395266774383186369 18840424046450080787389777)
      ·
        refine ⟨14130318034837560590542333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18840424046450080787389777 14130318034837560590542333)
        ·
          refine ⟨5298869263064085221453375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14130318034837560590542333 5298869263064085221453375)
          ·
            refine ⟨7948303894596127832180063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5298869263064085221453375 7948303894596127832180063)
            ·
              refine ⟨11922455841894191748270095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948303894596127832180063 11922455841894191748270095)
              ·
                refine ⟨17883683762841287622405143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11922455841894191748270095 17883683762841287622405143)
                ·
                  refine ⟨26825525644261931433607715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17883683762841287622405143 26825525644261931433607715)
                  ·
                    refine ⟨40238288466392897150411573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26825525644261931433607715 40238288466392897150411573)
                    ·
                      refine ⟨3772339543724334107851085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40238288466392897150411573 3772339543724334107851085)
                      ·
                        rfl

theorem cell23_7346605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7346605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346605 prefixEnd_7346605 := by exact prefixLift 7346605
  have htrace : WordTrace (prefixWord ++ tailWord_7346605) baseStart_7346605 baseEnd_7346605 := by
    simpa [prefixWord, tailWord_7346605, baseEnd_7346605] using wordTrace_append hprefix tailTrace_7346605
  have hstable : (prefixWord ++ tailWord_7346605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346605).length < 2 ^ (prefixWord ++ tailWord_7346605).sum := by decide
  have hdescent : baseEnd_7346605 < baseStart_7346605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346612 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_7346612 : Nat := 118140960795 + 7346612 * 2 ^ 59
def prefixEnd_7346612 : Nat := 4983230072969 + 3 ^ 40 * 7346612 * 2
def baseEnd_7346612 : Nat := 1257447712696305193487851

theorem tailTrace_7346612 : CollatzResearch.WordTrace tailWord_7346612 prefixEnd_7346612 1257447712696305193487851 := by
  unfold tailWord_7346612
  simp only [CollatzResearch.WordTrace]
  refine ⟨133976476430243450141413045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178635301906991266855217393 133976476430243450141413045)
  ·
    refine ⟨12560294665335323450757473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133976476430243450141413045 12560294665335323450757473)
    ·
      refine ⟨9420220999001492588068105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12560294665335323450757473 9420220999001492588068105)
      ·
        refine ⟨7065165749251119441051079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9420220999001492588068105 7065165749251119441051079)
        ·
          refine ⟨10597748623876679161576619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065165749251119441051079 10597748623876679161576619)
          ·
            refine ⟨15896622935815018742364929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10597748623876679161576619 15896622935815018742364929)
            ·
              refine ⟨11922467201861264056773697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15896622935815018742364929 11922467201861264056773697)
              ·
                refine ⟨8941850401395948042580273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11922467201861264056773697 8941850401395948042580273)
                ·
                  refine ⟨6706387801046961031935205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8941850401395948042580273 6706387801046961031935205)
                  ·
                    refine ⟨1257447712696305193487851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706387801046961031935205 1257447712696305193487851)
                    ·
                      rfl

theorem cell23_7346612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_7346612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346612 prefixEnd_7346612 := by exact prefixLift 7346612
  have htrace : WordTrace (prefixWord ++ tailWord_7346612) baseStart_7346612 baseEnd_7346612 := by
    simpa [prefixWord, tailWord_7346612, baseEnd_7346612] using wordTrace_append hprefix tailTrace_7346612
  have hstable : (prefixWord ++ tailWord_7346612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346612).length < 2 ^ (prefixWord ++ tailWord_7346612).sum := by decide
  have hdescent : baseEnd_7346612 < baseStart_7346612 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346625 : List Nat := [1, 2, 7, 1, 1, 2, 1, 8]
def baseStart_7346625 : Nat := 118140960795 + 7346625 * 2 ^ 59
def prefixEnd_7346625 : Nat := 4983230072969 + 3 ^ 40 * 7346625 * 2
def baseEnd_7346625 : Nat := 139716659753237927022259

theorem tailTrace_7346625 : CollatzResearch.WordTrace tailWord_7346625 prefixEnd_7346625 139716659753237927022259 := by
  unfold tailWord_7346625
  simp only [CollatzResearch.WordTrace]
  refine ⟨267953427009439803503049329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178635618006293202335366219 267953427009439803503049329)
  ·
    refine ⟨200965070257079852627286997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267953427009439803503049329 200965070257079852627286997)
    ·
      refine ⟨4710118834150309045952039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 200965070257079852627286997 4710118834150309045952039)
      ·
        refine ⟨7065178251225463568928059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710118834150309045952039 7065178251225463568928059)
        ·
          refine ⟨10597767376838195353392089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065178251225463568928059 10597767376838195353392089)
          ·
            refine ⟨7948325532628646515044067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597767376838195353392089 7948325532628646515044067)
            ·
              refine ⟨11922488298942969772566101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948325532628646515044067 11922488298942969772566101)
              ·
                refine ⟨139716659753237927022259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11922488298942969772566101 139716659753237927022259)
                ·
                  rfl

theorem cell23_7346625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 8].length) (baseStart_7346625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346625 prefixEnd_7346625 := by exact prefixLift 7346625
  have htrace : WordTrace (prefixWord ++ tailWord_7346625) baseStart_7346625 baseEnd_7346625 := by
    simpa [prefixWord, tailWord_7346625, baseEnd_7346625] using wordTrace_append hprefix tailTrace_7346625
  have hstable : (prefixWord ++ tailWord_7346625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346625).length < 2 ^ (prefixWord ++ tailWord_7346625).sum := by decide
  have hdescent : baseEnd_7346625 < baseStart_7346625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346634 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 2, 6]
def baseStart_7346634 : Nat := 118140960795 + 7346634 * 2 ^ 59
def prefixEnd_7346634 : Nat := 4983230072969 + 3 ^ 40 * 7346634 * 2
def baseEnd_7346634 : Nat := 1257451478221104831462817

theorem tailTrace_7346634 : CollatzResearch.WordTrace tailWord_7346634 prefixEnd_7346634 1257451478221104831462817 := by
  unfold tailWord_7346634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66988438816601799510031739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178635836844271465360084637 66988438816601799510031739)
  ·
    refine ⟨100482658224902699265047609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66988438816601799510031739 100482658224902699265047609)
    ·
      refine ⟨75361993668677024448785707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100482658224902699265047609 75361993668677024448785707)
      ·
        refine ⟨113042990503015536673178561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75361993668677024448785707 113042990503015536673178561)
        ·
          refine ⟨84782242877261652504883921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113042990503015536673178561 84782242877261652504883921)
          ·
            refine ⟨63586682157946239378662941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84782242877261652504883921 63586682157946239378662941)
            ·
              refine ⟨23845005809229839766998603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63586682157946239378662941 23845005809229839766998603)
              ·
                refine ⟨35767508713844759650497905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23845005809229839766998603 35767508713844759650497905)
                ·
                  refine ⟨26825631535383569737873429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35767508713844759650497905 26825631535383569737873429)
                  ·
                    refine ⟨1257451478221104831462817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26825631535383569737873429 1257451478221104831462817)
                    ·
                      rfl

theorem cell23_7346634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_7346634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346634 prefixEnd_7346634 := by exact prefixLift 7346634
  have htrace : WordTrace (prefixWord ++ tailWord_7346634) baseStart_7346634 baseEnd_7346634 := by
    simpa [prefixWord, tailWord_7346634, baseEnd_7346634] using wordTrace_append hprefix tailTrace_7346634
  have hstable : (prefixWord ++ tailWord_7346634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346634).length < 2 ^ (prefixWord ++ tailWord_7346634).sum := by decide
  have hdescent : baseEnd_7346634 < baseStart_7346634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346681 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 5]
def baseStart_7346681 : Nat := 118140960795 + 7346681 * 2 ^ 59
def prefixEnd_7346681 : Nat := 4983230072969 + 3 ^ 40 * 7346681 * 2
def baseEnd_7346681 : Nat := 419153174250452867833415

theorem tailTrace_7346681 : CollatzResearch.WordTrace tailWord_7346681 prefixEnd_7346681 419153174250452867833415 := by
  unfold tailWord_7346681
  simp only [CollatzResearch.WordTrace]
  refine ⟨267955469497236925067087897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178636979664824616711391931 267955469497236925067087897)
  ·
    refine ⟨200966602122927693800315923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267955469497236925067087897 200966602122927693800315923)
    ·
      refine ⟨301449903184391540700473885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200966602122927693800315923 301449903184391540700473885)
      ·
        refine ⟨113043713694146827762677707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301449903184391540700473885 113043713694146827762677707)
        ·
          refine ⟨169565570541220241644016561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113043713694146827762677707 169565570541220241644016561)
          ·
            refine ⟨127174177905915181233012421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169565570541220241644016561 127174177905915181233012421)
            ·
              refine ⟨23845158357359096481189829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127174177905915181233012421 23845158357359096481189829)
              ·
                refine ⟨4470967192004830590223093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23845158357359096481189829 4470967192004830590223093)
                ·
                  refine ⟨419153174250452867833415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4470967192004830590223093 419153174250452867833415)
                  ·
                    rfl

theorem cell23_7346681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 5].length) (baseStart_7346681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346681 prefixEnd_7346681 := by exact prefixLift 7346681
  have htrace : WordTrace (prefixWord ++ tailWord_7346681) baseStart_7346681 baseEnd_7346681 := by
    simpa [prefixWord, tailWord_7346681, baseEnd_7346681] using wordTrace_append hprefix tailTrace_7346681
  have hstable : (prefixWord ++ tailWord_7346681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346681).length < 2 ^ (prefixWord ++ tailWord_7346681).sum := by decide
  have hdescent : baseEnd_7346681 < baseStart_7346681 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346728 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 2, 5]
def baseStart_7346728 : Nat := 118140960795 + 7346728 * 2 ^ 59
def prefixEnd_7346728 : Nat := 4983230072969 + 3 ^ 40 * 7346728 * 2
def baseEnd_7346728 : Nat := 1257467567281612375537673

theorem tailTrace_7346728 : CollatzResearch.WordTrace tailWord_7346728 prefixEnd_7346728 1257467567281612375537673 := by
  unfold tailWord_7346728
  simp only [CollatzResearch.WordTrace]
  refine ⟨133978591864033326047024419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178638122485377768062699225 133978591864033326047024419)
  ·
    refine ⟨200967887796049989070536629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133978591864033326047024419 200967887796049989070536629)
    ·
      refine ⟨18840739480879686475362809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200967887796049989070536629 18840739480879686475362809)
      ·
        refine ⟨14130554610659764856522107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18840739480879686475362809 14130554610659764856522107)
        ·
          refine ⟨21195831915989647284783161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14130554610659764856522107 21195831915989647284783161)
          ·
            refine ⟨15896873936992235463587371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21195831915989647284783161 15896873936992235463587371)
            ·
              refine ⟨23845310905488353195381057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15896873936992235463587371 23845310905488353195381057)
              ·
                refine ⟨17883983179116264896535793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23845310905488353195381057 17883983179116264896535793)
                ·
                  refine ⟨13412987384337198672401845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17883983179116264896535793 13412987384337198672401845)
                  ·
                    refine ⟨1257467567281612375537673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13412987384337198672401845 1257467567281612375537673)
                    ·
                      rfl

theorem cell23_7346728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_7346728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346728 prefixEnd_7346728 := by exact prefixLift 7346728
  have htrace : WordTrace (prefixWord ++ tailWord_7346728) baseStart_7346728 baseEnd_7346728 := by
    simpa [prefixWord, tailWord_7346728, baseEnd_7346728] using wordTrace_append hprefix tailTrace_7346728
  have hstable : (prefixWord ++ tailWord_7346728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346728).length < 2 ^ (prefixWord ++ tailWord_7346728).sum := by decide
  have hdescent : baseEnd_7346728 < baseStart_7346728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346731 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 4, 4, 2]
def baseStart_7346731 : Nat := 118140960795 + 7346731 * 2 ^ 59
def prefixEnd_7346731 : Nat := 4983230072969 + 3 ^ 40 * 7346731 * 2
def baseEnd_7346731 : Nat := 3772404242286800614875505

theorem tailTrace_7346731 : CollatzResearch.WordTrace tailWord_7346731 prefixEnd_7346731 3772404242286800614875505 := by
  unfold tailWord_7346731
  simp only [CollatzResearch.WordTrace]
  refine ⟨267957293147055783606408047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178638195431370522404272031 267957293147055783606408047)
  ·
    refine ⟨401935939720583675409612071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267957293147055783606408047 401935939720583675409612071)
    ·
      refine ⟨602903909580875513114418107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401935939720583675409612071 602903909580875513114418107)
      ·
        refine ⟨904355864371313269671627161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602903909580875513114418107 904355864371313269671627161)
        ·
          refine ⟨678266898278484952253720371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904355864371313269671627161 678266898278484952253720371)
          ·
            refine ⟨1017400347417727428380580557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678266898278484952253720371 1017400347417727428380580557)
            ·
              refine ⟨381525130281647785642717709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1017400347417727428380580557 381525130281647785642717709)
              ·
                refine ⟨143071923855617919616019141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381525130281647785642717709 143071923855617919616019141)
                ·
                  refine ⟨26825985722928359928003589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143071923855617919616019141 26825985722928359928003589)
                  ·
                    refine ⟨5029872323049067486500673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26825985722928359928003589 5029872323049067486500673)
                    ·
                      refine ⟨3772404242286800614875505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5029872323049067486500673 3772404242286800614875505)
                      ·
                        rfl

theorem cell23_7346731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 4, 4, 2].length) (baseStart_7346731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346731 prefixEnd_7346731 := by exact prefixLift 7346731
  have htrace : WordTrace (prefixWord ++ tailWord_7346731) baseStart_7346731 baseEnd_7346731 := by
    simpa [prefixWord, tailWord_7346731, baseEnd_7346731] using wordTrace_append hprefix tailTrace_7346731
  have hstable : (prefixWord ++ tailWord_7346731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346731).length < 2 ^ (prefixWord ++ tailWord_7346731).sum := by decide
  have hdescent : baseEnd_7346731 < baseStart_7346731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346751 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3]
def baseStart_7346751 : Nat := 118140960795 + 7346751 * 2 ^ 59
def prefixEnd_7346751 : Nat := 4983230072969 + 3 ^ 40 * 7346751 * 2
def baseEnd_7346751 : Nat := 3772414511899890536625413

theorem tailTrace_7346751 : CollatzResearch.WordTrace tailWord_7346751 prefixEnd_7346751 3772414511899890536625413 := by
  unfold tailWord_7346751
  simp only [CollatzResearch.WordTrace]
  refine ⟨267958022606983327022136107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178638681737988884681424071 267958022606983327022136107)
  ·
    refine ⟨401937033910474990533204161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267958022606983327022136107 401937033910474990533204161)
    ·
      refine ⟨301452775432856242899903121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401937033910474990533204161 301452775432856242899903121)
      ·
        refine ⟨226089581574642182174927341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301452775432856242899903121 226089581574642182174927341)
        ·
          refine ⟨84783593090490818315597753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226089581574642182174927341 84783593090490818315597753)
          ·
            refine ⟨63587694817868113736698315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84783593090490818315597753 63587694817868113736698315)
            ·
              refine ⟨95381542226802170605047473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63587694817868113736698315 95381542226802170605047473)
              ·
                refine ⟨71536156670101627953785605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95381542226802170605047473 71536156670101627953785605)
                ·
                  refine ⟨13413029375644055241334801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71536156670101627953785605 13413029375644055241334801)
                  ·
                    refine ⟨10059772031733041431001101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13413029375644055241334801 10059772031733041431001101)
                    ·
                      refine ⟨3772414511899890536625413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059772031733041431001101 3772414511899890536625413)
                      ·
                        rfl

theorem cell23_7346751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 3].length) (baseStart_7346751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346751 prefixEnd_7346751 := by exact prefixLift 7346751
  have htrace : WordTrace (prefixWord ++ tailWord_7346751) baseStart_7346751 baseEnd_7346751 := by
    simpa [prefixWord, tailWord_7346751, baseEnd_7346751] using wordTrace_append hprefix tailTrace_7346751
  have hstable : (prefixWord ++ tailWord_7346751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346751).length < 2 ^ (prefixWord ++ tailWord_7346751).sum := by decide
  have hdescent : baseEnd_7346751 < baseStart_7346751 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346765 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7346765 : Nat := 118140960795 + 7346765 * 2 ^ 59
def prefixEnd_7346765 : Nat := 4983230072969 + 3 ^ 40 * 7346765 * 2
def baseEnd_7346765 : Nat := 3772421700629053481850349

theorem tailTrace_7346765 : CollatzResearch.WordTrace tailWord_7346765 prefixEnd_7346765 3772421700629053481850349 := by
  unfold tailWord_7346765
  simp only [CollatzResearch.WordTrace]
  refine ⟨267958533228932607413145749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178639022152621738275430499 267958533228932607413145749)
  ·
    refine ⟨12560556245106215972491207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267958533228932607413145749 12560556245106215972491207)
    ·
      refine ⟨18840834367659323958736811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560556245106215972491207 18840834367659323958736811)
      ·
        refine ⟨28261251551488985938105217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18840834367659323958736811 28261251551488985938105217)
        ·
          refine ⟨21195938663616739453578913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28261251551488985938105217 21195938663616739453578913)
          ·
            refine ⟨15896953997712554590184185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21195938663616739453578913 15896953997712554590184185)
            ·
              refine ⟨11922715498284415942638139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15896953997712554590184185 11922715498284415942638139)
              ·
                refine ⟨17884073247426623913957209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11922715498284415942638139 17884073247426623913957209)
                ·
                  refine ⟨13413054935569967935467907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17884073247426623913957209 13413054935569967935467907)
                  ·
                    refine ⟨20119582403354951903201861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13413054935569967935467907 20119582403354951903201861)
                    ·
                      refine ⟨3772421700629053481850349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20119582403354951903201861 3772421700629053481850349)
                      ·
                        rfl

theorem cell23_7346765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7346765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346765 prefixEnd_7346765 := by exact prefixLift 7346765
  have htrace : WordTrace (prefixWord ++ tailWord_7346765) baseStart_7346765 baseEnd_7346765 := by
    simpa [prefixWord, tailWord_7346765, baseEnd_7346765] using wordTrace_append hprefix tailTrace_7346765
  have hstable : (prefixWord ++ tailWord_7346765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346765).length < 2 ^ (prefixWord ++ tailWord_7346765).sum := by decide
  have hdescent : baseEnd_7346765 < baseStart_7346765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346792 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 1, 4]
def baseStart_7346792 : Nat := 118140960795 + 7346792 * 2 ^ 59
def prefixEnd_7346792 : Nat := 4983230072969 + 3 ^ 40 * 7346792 * 2
def baseEnd_7346792 : Nat := 1257478521535574958737575

theorem tailTrace_7346792 : CollatzResearch.WordTrace tailWord_7346792 prefixEnd_7346792 1257478521535574958737575 := by
  unfold tailWord_7346792
  simp only [CollatzResearch.WordTrace]
  refine ⟨133979758999917395512189315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178639678666556527349585753 133979758999917395512189315)
  ·
    refine ⟨200969638499876093268283973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133979758999917395512189315 200969638499876093268283973)
    ·
      refine ⟨37681807218726767487803245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200969638499876093268283973 37681807218726767487803245)
      ·
        refine ⟨14130677707022537807926217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37681807218726767487803245 14130677707022537807926217)
        ·
          refine ⟨10598008280266903355944663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14130677707022537807926217 10598008280266903355944663)
          ·
            refine ⟨15897012420400355033916995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10598008280266903355944663 15897012420400355033916995)
            ·
              refine ⟨23845518630600532550875493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15897012420400355033916995 23845518630600532550875493)
              ·
                refine ⟨4471034743237599853289155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23845518630600532550875493 4471034743237599853289155)
                ·
                  refine ⟨6706552114856399779933733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471034743237599853289155 6706552114856399779933733)
                  ·
                    refine ⟨1257478521535574958737575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706552114856399779933733 1257478521535574958737575)
                    ·
                      rfl

theorem cell23_7346792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_7346792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346792 prefixEnd_7346792 := by exact prefixLift 7346792
  have htrace : WordTrace (prefixWord ++ tailWord_7346792) baseStart_7346792 baseEnd_7346792 := by
    simpa [prefixWord, tailWord_7346792, baseEnd_7346792] using wordTrace_append hprefix tailTrace_7346792
  have hstable : (prefixWord ++ tailWord_7346792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346792).length < 2 ^ (prefixWord ++ tailWord_7346792).sum := by decide
  have hdescent : baseEnd_7346792 < baseStart_7346792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346831 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 6, 4]
def baseStart_7346831 : Nat := 118140960795 + 7346831 * 2 ^ 59
def prefixEnd_7346831 : Nat := 4983230072969 + 3 ^ 40 * 7346831 * 2
def baseEnd_7346831 : Nat := 1257485196784083407875015

theorem tailTrace_7346831 : CollatzResearch.WordTrace tailWord_7346831 prefixEnd_7346831 1257485196784083407875015 := by
  unfold tailWord_7346831
  simp only [CollatzResearch.WordTrace]
  refine ⟨267960940446693500685048347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178640626964462333790032231 267960940446693500685048347)
  ·
    refine ⟨401941410670040251027572521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267960940446693500685048347 401941410670040251027572521)
    ·
      refine ⟨301456058002530188270679391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401941410670040251027572521 301456058002530188270679391)
      ·
        refine ⟨452184087003795282406019087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301456058002530188270679391 452184087003795282406019087)
        ·
          refine ⟨678276130505692923609028631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452184087003795282406019087 678276130505692923609028631)
          ·
            refine ⟨1017414195758539385413542947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678276130505692923609028631 1017414195758539385413542947)
            ·
              refine ⟨1526121293637809078120314421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017414195758539385413542947 1526121293637809078120314421)
              ·
                refine ⟨143073871278544601073779477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1526121293637809078120314421 143073871278544601073779477)
                ·
                  refine ⟨6706587716181778175333413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143073871278544601073779477 6706587716181778175333413)
                  ·
                    refine ⟨1257485196784083407875015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706587716181778175333413 1257485196784083407875015)
                    ·
                      rfl

theorem cell23_7346831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 4].length) (baseStart_7346831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346831 prefixEnd_7346831 := by exact prefixLift 7346831
  have htrace : WordTrace (prefixWord ++ tailWord_7346831) baseStart_7346831 baseEnd_7346831 := by
    simpa [prefixWord, tailWord_7346831, baseEnd_7346831] using wordTrace_append hprefix tailTrace_7346831
  have hstable : (prefixWord ++ tailWord_7346831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346831).length < 2 ^ (prefixWord ++ tailWord_7346831).sum := by decide
  have hdescent : baseEnd_7346831 < baseStart_7346831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346841 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 5]
def baseStart_7346841 : Nat := 118140960795 + 7346841 * 2 ^ 59
def prefixEnd_7346841 : Nat := 4983230072969 + 3 ^ 40 * 7346841 * 2
def baseEnd_7346841 : Nat := 3772460725158795184499999

theorem tailTrace_7346841 : CollatzResearch.WordTrace tailWord_7346841 prefixEnd_7346841 3772460725158795184499999 := by
  unfold tailWord_7346841
  simp only [CollatzResearch.WordTrace]
  refine ⟨267961305176657272392912377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178640870117771514928608251 267961305176657272392912377)
  ·
    refine ⟨200970978882492954294684283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267961305176657272392912377 200970978882492954294684283)
    ·
      refine ⟨301456468323739431442026425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200970978882492954294684283 301456468323739431442026425)
      ·
        refine ⟨226092351242804573581519819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301456468323739431442026425 226092351242804573581519819)
        ·
          refine ⟨339138526864206860372279729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226092351242804573581519819 339138526864206860372279729)
          ·
            refine ⟨254353895148155145279209797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339138526864206860372279729 254353895148155145279209797)
            ·
              refine ⟨47691355340279089739851837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254353895148155145279209797 47691355340279089739851837)
              ·
                refine ⟨17884258252604658652444439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47691355340279089739851837 17884258252604658652444439)
                ·
                  refine ⟨26826387378906987978666659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17884258252604658652444439 26826387378906987978666659)
                  ·
                    refine ⟨40239581068360481967999989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26826387378906987978666659 40239581068360481967999989)
                    ·
                      refine ⟨3772460725158795184499999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40239581068360481967999989 3772460725158795184499999)
                      ·
                        rfl

theorem cell23_7346841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_7346841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346841 prefixEnd_7346841 := by exact prefixLift 7346841
  have htrace : WordTrace (prefixWord ++ tailWord_7346841) baseStart_7346841 baseEnd_7346841 := by
    simpa [prefixWord, tailWord_7346841, baseEnd_7346841] using wordTrace_append hprefix tailTrace_7346841
  have hstable : (prefixWord ++ tailWord_7346841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346841).length < 2 ^ (prefixWord ++ tailWord_7346841).sum := by decide
  have hdescent : baseEnd_7346841 < baseStart_7346841 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346905 : List Nat := [1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 3]
def baseStart_7346905 : Nat := 118140960795 + 7346905 * 2 ^ 59
def prefixEnd_7346905 : Nat := 4983230072969 + 3 ^ 40 * 7346905 * 2
def baseEnd_7346905 : Nat := 3772493587920682934099705

theorem tailTrace_7346905 : CollatzResearch.WordTrace tailWord_7346905 prefixEnd_7346905 3772493587920682934099705 := by
  unfold tailWord_7346905
  simp only [CollatzResearch.WordTrace]
  refine ⟨267963639448425411323242169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178642426298950274215494779 267963639448425411323242169)
  ·
    refine ⟨200972729586319058492431627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267963639448425411323242169 200972729586319058492431627)
    ·
      refine ⟨301459094379478587738647441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200972729586319058492431627 301459094379478587738647441)
      ·
        refine ⟨226094320784608940803985581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301459094379478587738647441 226094320784608940803985581)
        ·
          refine ⟨84785370294228352801494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226094320784608940803985581 84785370294228352801494593)
          ·
            refine ⟨63589027720671264601120945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84785370294228352801494593 63589027720671264601120945)
            ·
              refine ⟨47691770790503448450840709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63589027720671264601120945 47691770790503448450840709)
              ·
                refine ⟨8942207023219396584532633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47691770790503448450840709 8942207023219396584532633)
                ·
                  refine ⟨6706655267414547438399475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8942207023219396584532633 6706655267414547438399475)
                  ·
                    refine ⟨10059982901121821157599213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706655267414547438399475 10059982901121821157599213)
                    ·
                      refine ⟨3772493587920682934099705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10059982901121821157599213 3772493587920682934099705)
                      ·
                        rfl

theorem cell23_7346905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_7346905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346905 prefixEnd_7346905 := by exact prefixLift 7346905
  have htrace : WordTrace (prefixWord ++ tailWord_7346905) baseStart_7346905 baseEnd_7346905 := by
    simpa [prefixWord, tailWord_7346905, baseEnd_7346905] using wordTrace_append hprefix tailTrace_7346905
  have hstable : (prefixWord ++ tailWord_7346905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346905).length < 2 ^ (prefixWord ++ tailWord_7346905).sum := by decide
  have hdescent : baseEnd_7346905 < baseStart_7346905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346921 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 2, 6]
def baseStart_7346921 : Nat := 118140960795 + 7346921 * 2 ^ 59
def prefixEnd_7346921 : Nat := 4983230072969 + 3 ^ 40 * 7346921 * 2
def baseEnd_7346921 : Nat := 1257500601203718290499877

theorem tailTrace_7346921 : CollatzResearch.WordTrace tailWord_7346921 prefixEnd_7346921 1257500601203718290499877 := by
  unfold tailWord_7346921
  simp only [CollatzResearch.WordTrace]
  refine ⟨267964223016367446055824617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178642815344244964037216411 267964223016367446055824617)
  ·
    refine ⟨200973167262275584541868463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267964223016367446055824617 200973167262275584541868463)
    ·
      refine ⟨301459750893413376812802695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200973167262275584541868463 301459750893413376812802695)
      ·
        refine ⟨452189626340120065219204043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301459750893413376812802695 452189626340120065219204043)
        ·
          refine ⟨678284439510180097828806065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452189626340120065219204043 678284439510180097828806065)
          ·
            refine ⟨508713329632635073371604549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 678284439510180097828806065 508713329632635073371604549)
            ·
              refine ⟨95383749306119076257175853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508713329632635073371604549 95383749306119076257175853)
              ·
                refine ⟨35768905989794653596440945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95383749306119076257175853 35768905989794653596440945)
                ·
                  refine ⟨26826679492345990197330709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35768905989794653596440945 26826679492345990197330709)
                  ·
                    refine ⟨1257500601203718290499877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26826679492345990197330709 1257500601203718290499877)
                    ·
                      rfl

theorem cell23_7346921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 6].length) (baseStart_7346921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346921 prefixEnd_7346921 := by exact prefixLift 7346921
  have htrace : WordTrace (prefixWord ++ tailWord_7346921) baseStart_7346921 baseEnd_7346921 := by
    simpa [prefixWord, tailWord_7346921, baseEnd_7346921] using wordTrace_append hprefix tailTrace_7346921
  have hstable : (prefixWord ++ tailWord_7346921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346921).length < 2 ^ (prefixWord ++ tailWord_7346921).sum := by decide
  have hdescent : baseEnd_7346921 < baseStart_7346921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346948 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_7346948 : Nat := 118140960795 + 7346948 * 2 ^ 59
def prefixEnd_7346948 : Nat := 4983230072969 + 3 ^ 40 * 7346948 * 2
def baseEnd_7346948 : Nat := 3772515667588826265862007

theorem tailTrace_7346948 : CollatzResearch.WordTrace tailWord_7346948 prefixEnd_7346948 3772515667588826265862007 := by
  unfold tailWord_7346948
  simp only [CollatzResearch.WordTrace]
  refine ⟨133982603893634814833528749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178643471858179753111371665 133982603893634814833528749)
  ·
    refine ⟨50243476460113055562573281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133982603893634814833528749 50243476460113055562573281)
    ·
      refine ⟨37682607345084791671929961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50243476460113055562573281 37682607345084791671929961)
      ·
        refine ⟨28261955508813593753947471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37682607345084791671929961 28261955508813593753947471)
        ·
          refine ⟨42392933263220390630921207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28261955508813593753947471 42392933263220390630921207)
          ·
            refine ⟨63589399894830585946381811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42392933263220390630921207 63589399894830585946381811)
            ·
              refine ⟨95384099842245878919572717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63589399894830585946381811 95384099842245878919572717)
              ·
                refine ⟨35769037440842204594839769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95384099842245878919572717 35769037440842204594839769)
                ·
                  refine ⟨26826778080631653446129827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35769037440842204594839769 26826778080631653446129827)
                  ·
                    refine ⟨40240167120947480169194741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26826778080631653446129827 40240167120947480169194741)
                    ·
                      refine ⟨3772515667588826265862007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40240167120947480169194741 3772515667588826265862007)
                      ·
                        rfl

theorem cell23_7346948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_7346948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346948 prefixEnd_7346948 := by exact prefixLift 7346948
  have htrace : WordTrace (prefixWord ++ tailWord_7346948) baseStart_7346948 baseEnd_7346948 := by
    simpa [prefixWord, tailWord_7346948, baseEnd_7346948] using wordTrace_append hprefix tailTrace_7346948
  have hstable : (prefixWord ++ tailWord_7346948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346948).length < 2 ^ (prefixWord ++ tailWord_7346948).sum := by decide
  have hdescent : baseEnd_7346948 < baseStart_7346948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346958 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7346958 : Nat := 118140960795 + 7346958 * 2 ^ 59
def prefixEnd_7346958 : Nat := 4983230072969 + 3 ^ 40 * 7346958 * 2
def baseEnd_7346958 : Nat := 3772520802395371226736961

theorem tailTrace_7346958 : CollatzResearch.WordTrace tailWord_7346958 prefixEnd_7346958 3772520802395371226736961 := by
  unfold tailWord_7346958
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495696564654175171865191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178643715011488934249947685 33495696564654175171865191)
  ·
    refine ⟨50243544846981262757797787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33495696564654175171865191 50243544846981262757797787)
    ·
      refine ⟨75365317270471894136696681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50243544846981262757797787 75365317270471894136696681)
      ·
        refine ⟨56523987952853920602522511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75365317270471894136696681 56523987952853920602522511)
        ·
          refine ⟨84785981929280880903783767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56523987952853920602522511 84785981929280880903783767)
          ·
            refine ⟨127178972893921321355675651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84785981929280880903783767 127178972893921321355675651)
            ·
              refine ⟨190768459340881982033513477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127178972893921321355675651 190768459340881982033513477)
              ·
                refine ⟨35769086126415371631283777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190768459340881982033513477 35769086126415371631283777)
                ·
                  refine ⟨26826814594811528723462833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35769086126415371631283777 26826814594811528723462833)
                  ·
                    refine ⟨20120110946108646542597125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26826814594811528723462833 20120110946108646542597125)
                    ·
                      refine ⟨3772520802395371226736961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20120110946108646542597125 3772520802395371226736961)
                      ·
                        rfl

theorem cell23_7346958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7346958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346958 prefixEnd_7346958 := by exact prefixLift 7346958
  have htrace : WordTrace (prefixWord ++ tailWord_7346958) baseStart_7346958 baseEnd_7346958 := by
    simpa [prefixWord, tailWord_7346958, baseEnd_7346958] using wordTrace_append hprefix tailTrace_7346958
  have hstable : (prefixWord ++ tailWord_7346958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346958).length < 2 ^ (prefixWord ++ tailWord_7346958).sum := by decide
  have hdescent : baseEnd_7346958 < baseStart_7346958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7346961 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 7]
def baseStart_7346961 : Nat := 118140960795 + 7346961 * 2 ^ 59
def prefixEnd_7346961 : Nat := 4983230072969 + 3 ^ 40 * 7346961 * 2
def baseEnd_7346961 : Nat := 3772522342837334714999447

theorem tailTrace_7346961 : CollatzResearch.WordTrace tailWord_7346961 prefixEnd_7346961 3772522342837334714999447 := by
  unfold tailWord_7346961
  simp only [CollatzResearch.WordTrace]
  refine ⟨267965681936222532887280737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178643787957481688591520491 267965681936222532887280737)
  ·
    refine ⟨200974261452166899665460553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267965681936222532887280737 200974261452166899665460553)
    ·
      refine ⟨150730696089125174749095415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200974261452166899665460553 150730696089125174749095415)
      ·
        refine ⟨226096044133687762123643123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150730696089125174749095415 226096044133687762123643123)
        ·
          refine ⟨339144066200531643185464685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226096044133687762123643123 339144066200531643185464685)
          ·
            refine ⟨127179024825199366194549257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 339144066200531643185464685 127179024825199366194549257)
            ·
              refine ⟨95384268618899524645911943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127179024825199366194549257 95384268618899524645911943)
              ·
                refine ⟨143076402928349286968867915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95384268618899524645911943 143076402928349286968867915)
                ·
                  refine ⟨214614604392523930453301873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143076402928349286968867915 214614604392523930453301873)
                  ·
                    refine ⟨160960953294392947839976405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214614604392523930453301873 160960953294392947839976405)
                    ·
                      refine ⟨3772522342837334714999447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160960953294392947839976405 3772522342837334714999447)
                      ·
                        rfl

theorem cell23_7346961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 7].length) (baseStart_7346961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7346961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7346961 prefixEnd_7346961 := by exact prefixLift 7346961
  have htrace : WordTrace (prefixWord ++ tailWord_7346961) baseStart_7346961 baseEnd_7346961 := by
    simpa [prefixWord, tailWord_7346961, baseEnd_7346961] using wordTrace_append hprefix tailTrace_7346961
  have hstable : (prefixWord ++ tailWord_7346961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7346961).length < 2 ^ (prefixWord ++ tailWord_7346961).sum := by decide
  have hdescent : baseEnd_7346961 < baseStart_7346961 := by decide
  rcases family_descends (prefixWord ++ tailWord_7346961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347002 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 5]
def baseStart_7347002 : Nat := 118140960795 + 7347002 * 2 ^ 59
def prefixEnd_7347002 : Nat := 4983230072969 + 3 ^ 40 * 7347002 * 2
def baseEnd_7347002 : Nat := 419171488393796561620751

theorem tailTrace_7347002 : CollatzResearch.WordTrace tailWord_7347002 prefixEnd_7347002 419171488393796561620751 := by
  unfold tailWord_7347002
  simp only [CollatzResearch.WordTrace]
  refine ⟨66991794332268499222380815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178644784886049331259682173 66991794332268499222380815)
  ·
    refine ⟨100487691498402748833571223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66991794332268499222380815 100487691498402748833571223)
    ·
      refine ⟨150731537247604123250356835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100487691498402748833571223 150731537247604123250356835)
      ·
        refine ⟨226097305871406184875535253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150731537247604123250356835 226097305871406184875535253)
        ·
          refine ⟨10598311212722164916040715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226097305871406184875535253 10598311212722164916040715)
          ·
            refine ⟨15897466819083247374061073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10598311212722164916040715 15897466819083247374061073)
            ·
              refine ⟨11923100114312435530545805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15897466819083247374061073 11923100114312435530545805)
              ·
                refine ⟨4471162542867163323954677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11923100114312435530545805 4471162542867163323954677)
                ·
                  refine ⟨419171488393796561620751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4471162542867163323954677 419171488393796561620751)
                  ·
                    rfl

theorem cell23_7347002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 5].length) (baseStart_7347002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347002 prefixEnd_7347002 := by exact prefixLift 7347002
  have htrace : WordTrace (prefixWord ++ tailWord_7347002) baseStart_7347002 baseEnd_7347002 := by
    simpa [prefixWord, tailWord_7347002, baseEnd_7347002] using wordTrace_append hprefix tailTrace_7347002
  have hstable : (prefixWord ++ tailWord_7347002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347002).length < 2 ^ (prefixWord ++ tailWord_7347002).sum := by decide
  have hdescent : baseEnd_7347002 < baseStart_7347002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347045 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 3, 4]
def baseStart_7347045 : Nat := 118140960795 + 7347045 * 2 ^ 59
def prefixEnd_7347045 : Nat := 4983230072969 + 3 ^ 40 * 7347045 * 2
def baseEnd_7347045 : Nat := 1257521825070770795449687

theorem tailTrace_7347045 : CollatzResearch.WordTrace tailWord_7347045 prefixEnd_7347045 1257521825070770795449687 := by
  unfold tailWord_7347045
  simp only [CollatzResearch.WordTrace]
  refine ⟨267968745667918215233338589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178645830445278810155559059 267968745667918215233338589)
  ·
    refine ⟨100488279625469330712501971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267968745667918215233338589 100488279625469330712501971)
    ·
      refine ⟨150732419438203996068752957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100488279625469330712501971 150732419438203996068752957)
      ·
        refine ⟨56524657289326498525782359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150732419438203996068752957 56524657289326498525782359)
        ·
          refine ⟨84786985933989747788673539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56524657289326498525782359 84786985933989747788673539)
          ·
            refine ⟨127180478900984621683010309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84786985933989747788673539 127180478900984621683010309)
            ·
              refine ⟨23846339793934616565564433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127180478900984621683010309 23846339793934616565564433)
              ·
                refine ⟨17884754845450962424173325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23846339793934616565564433 17884754845450962424173325)
                ·
                  refine ⟨6706783067044110909064997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17884754845450962424173325 6706783067044110909064997)
                  ·
                    refine ⟨1257521825070770795449687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706783067044110909064997 1257521825070770795449687)
                    ·
                      rfl

theorem cell23_7347045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_7347045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347045 prefixEnd_7347045 := by exact prefixLift 7347045
  have htrace : WordTrace (prefixWord ++ tailWord_7347045) baseStart_7347045 baseEnd_7347045 := by
    simpa [prefixWord, tailWord_7347045, baseEnd_7347045] using wordTrace_append hprefix tailTrace_7347045
  have hstable : (prefixWord ++ tailWord_7347045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347045).length < 2 ^ (prefixWord ++ tailWord_7347045).sum := by decide
  have hdescent : baseEnd_7347045 < baseStart_7347045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347058 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 8]
def baseStart_7347058 : Nat := 118140960795 + 7347058 * 2 ^ 59
def prefixEnd_7347058 : Nat := 4983230072969 + 3 ^ 40 * 7347058 * 2
def baseEnd_7347058 : Nat := 419174683384535648387389

theorem tailTrace_7347058 : CollatzResearch.WordTrace tailWord_7347058 prefixEnd_7347058 419174683384535648387389 := by
  unfold tailWord_7347058
  simp only [CollatzResearch.WordTrace]
  refine ⟨66992304954217779613390457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178646146544580745635707885 66992304954217779613390457)
  ·
    refine ⟨50244228715663334710042843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66992304954217779613390457 50244228715663334710042843)
    ·
      refine ⟨75366343073495002065064265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50244228715663334710042843 75366343073495002065064265)
      ·
        refine ⟨56524757305121251548798199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75366343073495002065064265 56524757305121251548798199)
        ·
          refine ⟨84787135957681877323197299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56524757305121251548798199 84787135957681877323197299)
          ·
            refine ⟨127180703936522815984795949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84787135957681877323197299 127180703936522815984795949)
            ·
              refine ⟨47692763976196055994298481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127180703936522815984795949 47692763976196055994298481)
              ·
                refine ⟨35769572982147041995723861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47692763976196055994298481 35769572982147041995723861)
                ·
                  refine ⟨419174683384535648387389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35769572982147041995723861 419174683384535648387389)
                  ·
                    rfl

theorem cell23_7347058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 8].length) (baseStart_7347058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347058 prefixEnd_7347058 := by exact prefixLift 7347058
  have htrace : WordTrace (prefixWord ++ tailWord_7347058) baseStart_7347058 baseEnd_7347058 := by
    simpa [prefixWord, tailWord_7347058, baseEnd_7347058] using wordTrace_append hprefix tailTrace_7347058
  have hstable : (prefixWord ++ tailWord_7347058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347058).length < 2 ^ (prefixWord ++ tailWord_7347058).sum := by decide
  have hdescent : baseEnd_7347058 < baseStart_7347058 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347136 : List Nat := [2, 1, 1, 2, 3, 3, 4, 2, 1, 1, 3]
def baseStart_7347136 : Nat := 118140960795 + 7347136 * 2 ^ 59
def prefixEnd_7347136 : Nat := 4983230072969 + 3 ^ 40 * 7347136 * 2
def baseEnd_7347136 : Nat := 3772612201951871530311143

theorem tailTrace_7347136 : CollatzResearch.WordTrace tailWord_7347136 prefixEnd_7347136 3772612201951871530311143 := by
  unfold tailWord_7347136
  simp only [CollatzResearch.WordTrace]
  refine ⟨133986032355294268887450631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178648043140392358516600841 133986032355294268887450631)
  ·
    refine ⟨200979048532941403331175947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133986032355294268887450631 200979048532941403331175947)
    ·
      refine ⟨301468572799412104996763921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200979048532941403331175947 301468572799412104996763921)
      ·
        refine ⟨226101429599559078747572941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301468572799412104996763921 226101429599559078747572941)
        ·
          refine ⟨84788036099834654530339853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226101429599559078747572941 84788036099834654530339853)
          ·
            refine ⟨31795513537437995448877445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84788036099834654530339853 31795513537437995448877445)
            ·
              refine ⟨5961658788269624146664521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31795513537437995448877445 5961658788269624146664521)
              ·
                refine ⟨4471244091202218109998391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5961658788269624146664521 4471244091202218109998391)
                ·
                  refine ⟨6706866136803327164997587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471244091202218109998391 6706866136803327164997587)
                  ·
                    refine ⟨10060299205204990747496381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6706866136803327164997587 10060299205204990747496381)
                    ·
                      refine ⟨3772612201951871530311143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060299205204990747496381 3772612201951871530311143)
                      ·
                        rfl

theorem cell23_7347136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_7347136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347136 prefixEnd_7347136 := by exact prefixLift 7347136
  have htrace : WordTrace (prefixWord ++ tailWord_7347136) baseStart_7347136 baseEnd_7347136 := by
    simpa [prefixWord, tailWord_7347136, baseEnd_7347136] using wordTrace_append hprefix tailTrace_7347136
  have hstable : (prefixWord ++ tailWord_7347136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347136).length < 2 ^ (prefixWord ++ tailWord_7347136).sum := by decide
  have hdescent : baseEnd_7347136 < baseStart_7347136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347162 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3]
def baseStart_7347162 : Nat := 118140960795 + 7347162 * 2 ^ 59
def prefixEnd_7347162 : Nat := 4983230072969 + 3 ^ 40 * 7347162 * 2
def baseEnd_7347162 : Nat := 3772625552448888428586023

theorem tailTrace_7347162 : CollatzResearch.WordTrace tailWord_7347162 prefixEnd_7347162 3772625552448888428586023 := by
  unfold tailWord_7347162
  simp only [CollatzResearch.WordTrace]
  refine ⟨66993253252123586053836935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178648675338996229476898493 66993253252123586053836935)
  ·
    refine ⟨100489879878185379080755403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66993253252123586053836935 100489879878185379080755403)
    ·
      refine ⟨150734819817278068621133105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100489879878185379080755403 150734819817278068621133105)
      ·
        refine ⟨113051114862958551465849829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150734819817278068621133105 113051114862958551465849829)
        ·
          refine ⟨21197084036804728399846843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113051114862958551465849829 21197084036804728399846843)
          ·
            refine ⟨31795626055207092599770265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21197084036804728399846843 31795626055207092599770265)
            ·
              refine ⟨23846719541405319449827699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31795626055207092599770265 23846719541405319449827699)
              ·
                refine ⟨35770079312107979174741549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23846719541405319449827699 35770079312107979174741549)
                ·
                  refine ⟨13413779742040492190528081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35770079312107979174741549 13413779742040492190528081)
                  ·
                    refine ⟨10060334806530369142896061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13413779742040492190528081 10060334806530369142896061)
                    ·
                      refine ⟨3772625552448888428586023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060334806530369142896061 3772625552448888428586023)
                      ·
                        rfl

theorem cell23_7347162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_7347162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347162 prefixEnd_7347162 := by exact prefixLift 7347162
  have htrace : WordTrace (prefixWord ++ tailWord_7347162) baseStart_7347162 baseEnd_7347162 := by
    simpa [prefixWord, tailWord_7347162, baseEnd_7347162] using wordTrace_append hprefix tailTrace_7347162
  have hstable : (prefixWord ++ tailWord_7347162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347162).length < 2 ^ (prefixWord ++ tailWord_7347162).sum := by decide
  have hdescent : baseEnd_7347162 < baseStart_7347162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347173 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 1, 5]
def baseStart_7347173 : Nat := 118140960795 + 7347173 * 2 ^ 59
def prefixEnd_7347173 : Nat := 4983230072969 + 3 ^ 40 * 7347173 * 2
def baseEnd_7347173 : Nat := 1257543733578695961849491

theorem tailTrace_7347173 : CollatzResearch.WordTrace tailWord_7347173 prefixEnd_7347173 1257543733578695961849491 := by
  unfold tailWord_7347173
  simp only [CollatzResearch.WordTrace]
  refine ⟨267973414211454493093998173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178648942807636328729332115 267973414211454493093998173)
  ·
    refine ⟨100490030329295434910249315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267973414211454493093998173 100490030329295434910249315)
    ·
      refine ⟨150735045493943152365373973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100490030329295434910249315 150735045493943152365373973)
      ·
        refine ⟨7065705257528585267126905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 150735045493943152365373973 7065705257528585267126905)
        ·
          refine ⟨5299278943146438950345179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065705257528585267126905 5299278943146438950345179)
          ·
            refine ⟨7948918414719658425517769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299278943146438950345179 7948918414719658425517769)
            ·
              refine ⟨5961688811039743819138327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7948918414719658425517769 5961688811039743819138327)
              ·
                refine ⟨8942533216559615728707491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961688811039743819138327 8942533216559615728707491)
                ·
                  refine ⟨13413799824839423593061237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8942533216559615728707491 13413799824839423593061237)
                  ·
                    refine ⟨1257543733578695961849491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13413799824839423593061237 1257543733578695961849491)
                    ·
                      rfl

theorem cell23_7347173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_7347173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347173 prefixEnd_7347173 := by exact prefixLift 7347173
  have htrace : WordTrace (prefixWord ++ tailWord_7347173) baseStart_7347173 baseEnd_7347173 := by
    simpa [prefixWord, tailWord_7347173, baseEnd_7347173] using wordTrace_append hprefix tailTrace_7347173
  have hstable : (prefixWord ++ tailWord_7347173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347173).length < 2 ^ (prefixWord ++ tailWord_7347173).sum := by decide
  have hdescent : baseEnd_7347173 < baseStart_7347173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347176 : List Nat := [2, 1, 4, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_7347176 : Nat := 118140960795 + 7347176 * 2 ^ 59
def prefixEnd_7347176 : Nat := 4983230072969 + 3 ^ 40 * 7347176 * 2
def baseEnd_7347176 : Nat := 3772632741178051373810959

theorem tailTrace_7347176 : CollatzResearch.WordTrace tailWord_7347176 prefixEnd_7347176 3772632741178051373810959 := by
  unfold tailWord_7347176
  simp only [CollatzResearch.WordTrace]
  refine ⟨133986761815221812303178691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178649015753629083070904921 133986761815221812303178691)
  ·
    refine ⟨200980142722832718454768037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133986761815221812303178691 200980142722832718454768037)
    ·
      refine ⟨37683776760531134710269007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200980142722832718454768037 37683776760531134710269007)
      ·
        refine ⟨56525665140796702065403511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37683776760531134710269007 56525665140796702065403511)
        ·
          refine ⟨84788497711195053098105267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56525665140796702065403511 84788497711195053098105267)
          ·
            refine ⟨127182746566792579647157901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84788497711195053098105267 127182746566792579647157901)
            ·
              refine ⟨47693529962547217367684213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127182746566792579647157901 47693529962547217367684213)
              ·
                refine ⟨4471268433988801628220395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47693529962547217367684213 4471268433988801628220395)
                ·
                  refine ⟨6706902650983202442330593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471268433988801628220395 6706902650983202442330593)
                  ·
                    refine ⟨5030176988237401831747945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706902650983202442330593 5030176988237401831747945)
                    ·
                      refine ⟨3772632741178051373810959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030176988237401831747945 3772632741178051373810959)
                      ·
                        rfl

theorem cell23_7347176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_7347176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347176 prefixEnd_7347176 := by exact prefixLift 7347176
  have htrace : WordTrace (prefixWord ++ tailWord_7347176) baseStart_7347176 baseEnd_7347176 := by
    simpa [prefixWord, tailWord_7347176, baseEnd_7347176] using wordTrace_append hprefix tailTrace_7347176
  have hstable : (prefixWord ++ tailWord_7347176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347176).length < 2 ^ (prefixWord ++ tailWord_7347176).sum := by decide
  have hdescent : baseEnd_7347176 < baseStart_7347176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347235 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5]
def baseStart_7347235 : Nat := 118140960795 + 7347235 * 2 ^ 59
def prefixEnd_7347235 : Nat := 4983230072969 + 3 ^ 40 * 7347235 * 2
def baseEnd_7347235 : Nat := 3772663036536666642973187

theorem tailTrace_7347235 : CollatzResearch.WordTrace tailWord_7347235 prefixEnd_7347235 3772663036536666642973187 := by
  unfold tailWord_7347235
  simp only [CollatzResearch.WordTrace]
  refine ⟨267975675537229877682755159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178650450358153251788503439 267975675537229877682755159)
  ·
    refine ⟨401963513305844816524132739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267975675537229877682755159 401963513305844816524132739)
    ·
      refine ⟨602945269958767224786199109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401963513305844816524132739 602945269958767224786199109)
      ·
        refine ⟨113052238117268854647412333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602945269958767224786199109 113052238117268854647412333)
        ·
          refine ⟨42394589293975820492779625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113052238117268854647412333 42394589293975820492779625)
          ·
            refine ⟨31795941970481865369584719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42394589293975820492779625 31795941970481865369584719)
            ·
              refine ⟨47693912955722798054377079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31795941970481865369584719 47693912955722798054377079)
              ·
                refine ⟨71540869433584197081565619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47693912955722798054377079 71540869433584197081565619)
                ·
                  refine ⟨107311304150376295622348429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71540869433584197081565619 107311304150376295622348429)
                  ·
                    refine ⟨40241739056391110858380661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107311304150376295622348429 40241739056391110858380661)
                    ·
                      refine ⟨3772663036536666642973187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40241739056391110858380661 3772663036536666642973187)
                      ·
                        rfl

theorem cell23_7347235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_7347235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347235 prefixEnd_7347235 := by exact prefixLift 7347235
  have htrace : WordTrace (prefixWord ++ tailWord_7347235) baseStart_7347235 baseEnd_7347235 := by
    simpa [prefixWord, tailWord_7347235, baseEnd_7347235] using wordTrace_append hprefix tailTrace_7347235
  have hstable : (prefixWord ++ tailWord_7347235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347235).length < 2 ^ (prefixWord ++ tailWord_7347235).sum := by decide
  have hdescent : baseEnd_7347235 < baseStart_7347235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347236 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7347236 : Nat := 118140960795 + 7347236 * 2 ^ 59
def prefixEnd_7347236 : Nat := 4983230072969 + 3 ^ 40 * 7347236 * 2
def baseEnd_7347236 : Nat := 3772663550017321139060683

theorem tailTrace_7347236 : CollatzResearch.WordTrace tailWord_7347236 prefixEnd_7347236 3772663550017321139060683 := by
  unfold tailWord_7347236
  simp only [CollatzResearch.WordTrace]
  refine ⟨133987856005113127426770781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178650474673484169902361041 133987856005113127426770781)
  ·
    refine ⟨50245446001917422785039043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133987856005113127426770781 50245446001917422785039043)
    ·
      refine ⟨75368169002876134177558565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50245446001917422785039043 75368169002876134177558565)
      ·
        refine ⟨14131531688039275158292231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75368169002876134177558565 14131531688039275158292231)
        ·
          refine ⟨21197297532058912737438347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14131531688039275158292231 21197297532058912737438347)
          ·
            refine ⟨31795946298088369106157521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21197297532058912737438347 31795946298088369106157521)
            ·
              refine ⟨23846959723566276829618141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31795946298088369106157521 23846959723566276829618141)
              ·
                refine ⟨8942609896337353811106803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23846959723566276829618141 8942609896337353811106803)
                ·
                  refine ⟨13413914844506030716660205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8942609896337353811106803 13413914844506030716660205)
                  ·
                    refine ⟨5030218066689761518747577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13413914844506030716660205 5030218066689761518747577)
                    ·
                      refine ⟨3772663550017321139060683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030218066689761518747577 3772663550017321139060683)
                      ·
                        rfl

theorem cell23_7347236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7347236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347236 prefixEnd_7347236 := by exact prefixLift 7347236
  have htrace : WordTrace (prefixWord ++ tailWord_7347236) baseStart_7347236 baseEnd_7347236 := by
    simpa [prefixWord, tailWord_7347236, baseEnd_7347236] using wordTrace_append hprefix tailTrace_7347236
  have hstable : (prefixWord ++ tailWord_7347236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347236).length < 2 ^ (prefixWord ++ tailWord_7347236).sum := by decide
  have hdescent : baseEnd_7347236 < baseStart_7347236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347249 : List Nat := [1, 2, 2, 3, 1, 2, 1, 3, 4, 2, 2]
def baseStart_7347249 : Nat := 118140960795 + 7347249 * 2 ^ 59
def prefixEnd_7347249 : Nat := 4983230072969 + 3 ^ 40 * 7347249 * 2
def baseEnd_7347249 : Nat := 3772670225265829588198123

theorem tailTrace_7347249 : CollatzResearch.WordTrace tailWord_7347249 prefixEnd_7347249 3772670225265829588198123 := by
  unfold tailWord_7347249
  simp only [CollatzResearch.WordTrace]
  refine ⟨267976186159179158073764801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178650790772786105382509867 267976186159179158073764801)
  ·
    refine ⟨200982139619384368555323601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267976186159179158073764801 200982139619384368555323601)
    ·
      refine ⟨150736604714538276416492701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200982139619384368555323601 150736604714538276416492701)
      ·
        refine ⟨56526226767951853656184763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150736604714538276416492701 56526226767951853656184763)
        ·
          refine ⟨84789340151927780484277145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56526226767951853656184763 84789340151927780484277145)
          ·
            refine ⟨63592005113945835363207859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84789340151927780484277145 63592005113945835363207859)
            ·
              refine ⟨95388007670918753044811789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63592005113945835363207859 95388007670918753044811789)
              ·
                refine ⟨35770502876594532391804421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95388007670918753044811789 35770502876594532391804421)
                ·
                  refine ⟨6706969289361474823463329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35770502876594532391804421 6706969289361474823463329)
                  ·
                    refine ⟨5030226967021106117597497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6706969289361474823463329 5030226967021106117597497)
                    ·
                      refine ⟨3772670225265829588198123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030226967021106117597497 3772670225265829588198123)
                      ·
                        rfl

theorem cell23_7347249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_7347249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347249 prefixEnd_7347249 := by exact prefixLift 7347249
  have htrace : WordTrace (prefixWord ++ tailWord_7347249) baseStart_7347249 baseEnd_7347249 := by
    simpa [prefixWord, tailWord_7347249, baseEnd_7347249] using wordTrace_append hprefix tailTrace_7347249
  have hstable : (prefixWord ++ tailWord_7347249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347249).length < 2 ^ (prefixWord ++ tailWord_7347249).sum := by decide
  have hdescent : baseEnd_7347249 < baseStart_7347249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347270 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2]
def baseStart_7347270 : Nat := 118140960795 + 7347270 * 2 ^ 59
def prefixEnd_7347270 : Nat := 4983230072969 + 3 ^ 40 * 7347270 * 2
def baseEnd_7347270 : Nat := 3772681008359574006035527

theorem tailTrace_7347270 : CollatzResearch.WordTrace tailWord_7347270 prefixEnd_7347270 3772681008359574006035527 := by
  unfold tailWord_7347270
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374279752878221208133727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178651301394735385773519509 8374279752878221208133727)
  ·
    refine ⟨12561419629317331812200591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374279752878221208133727 12561419629317331812200591)
    ·
      refine ⟨18842129443975997718300887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12561419629317331812200591 18842129443975997718300887)
      ·
        refine ⟨28263194165963996577451331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18842129443975997718300887 28263194165963996577451331)
        ·
          refine ⟨42394791248945994866176997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28263194165963996577451331 42394791248945994866176997)
          ·
            refine ⟨7949023359177374037408187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42394791248945994866176997 7949023359177374037408187)
            ·
              refine ⟨11923535038766061056112281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949023359177374037408187 11923535038766061056112281)
              ·
                refine ⟨8942651279074545792084211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11923535038766061056112281 8942651279074545792084211)
                ·
                  refine ⟨13413976918611818688126317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8942651279074545792084211 13413976918611818688126317)
                  ·
                    refine ⟨5030241344479432008047369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13413976918611818688126317 5030241344479432008047369)
                    ·
                      refine ⟨3772681008359574006035527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030241344479432008047369 3772681008359574006035527)
                      ·
                        rfl

theorem cell23_7347270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_7347270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347270 prefixEnd_7347270 := by exact prefixLift 7347270
  have htrace : WordTrace (prefixWord ++ tailWord_7347270) baseStart_7347270 baseEnd_7347270 := by
    simpa [prefixWord, tailWord_7347270, baseEnd_7347270] using wordTrace_append hprefix tailTrace_7347270
  have hstable : (prefixWord ++ tailWord_7347270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347270).length < 2 ^ (prefixWord ++ tailWord_7347270).sum := by decide
  have hdescent : baseEnd_7347270 < baseStart_7347270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347295 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7347295 : Nat := 118140960795 + 7347295 * 2 ^ 59
def prefixEnd_7347295 : Nat := 4983230072969 + 3 ^ 40 * 7347295 * 2
def baseEnd_7347295 : Nat := 3772693845375936408222911

theorem tailTrace_7347295 : CollatzResearch.WordTrace tailWord_7347295 prefixEnd_7347295 3772693845375936408222911 := by
  unfold tailWord_7347295
  simp only [CollatzResearch.WordTrace]
  refine ⟨267977863917012507929939339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178651909278008338619959559 267977863917012507929939339)
  ·
    refine ⟨401966795875518761894909009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267977863917012507929939339 401966795875518761894909009)
    ·
      refine ⟨301475096906639071421181757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401966795875518761894909009 301475096906639071421181757)
      ·
        refine ⟨113053161339989651782943159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301475096906639071421181757 113053161339989651782943159)
        ·
          refine ⟨169579742009984477674414739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113053161339989651782943159 169579742009984477674414739)
          ·
            refine ⟨254369613014976716511622109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169579742009984477674414739 254369613014976716511622109)
            ·
              refine ⟨95388604880616268691858291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254369613014976716511622109 95388604880616268691858291)
              ·
                refine ⟨143082907320924403037787437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95388604880616268691858291 143082907320924403037787437)
                ·
                  refine ⟨53656090245346651139170289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143082907320924403037787437 53656090245346651139170289)
                  ·
                    refine ⟨40242067684009988354377717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53656090245346651139170289 40242067684009988354377717)
                    ·
                      refine ⟨3772693845375936408222911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40242067684009988354377717 3772693845375936408222911)
                      ·
                        rfl

theorem cell23_7347295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7347295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347295 prefixEnd_7347295 := by exact prefixLift 7347295
  have htrace : WordTrace (prefixWord ++ tailWord_7347295) baseStart_7347295 baseEnd_7347295 := by
    simpa [prefixWord, tailWord_7347295, baseEnd_7347295] using wordTrace_append hprefix tailTrace_7347295
  have hstable : (prefixWord ++ tailWord_7347295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347295).length < 2 ^ (prefixWord ++ tailWord_7347295).sum := by decide
  have hdescent : baseEnd_7347295 < baseStart_7347295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347306 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 5]
def baseStart_7347306 : Nat := 118140960795 + 7347306 * 2 ^ 59
def prefixEnd_7347306 : Nat := 4983230072969 + 3 ^ 40 * 7347306 * 2
def baseEnd_7347306 : Nat := 419188832629237318353929

theorem tailTrace_7347306 : CollatzResearch.WordTrace tailWord_7347306 prefixEnd_7347306 419188832629237318353929 := by
  unfold tailWord_7347306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66994566279993164202147443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178652176746648437872393181 66994566279993164202147443)
  ·
    refine ⟨100491849419989746303221165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66994566279993164202147443 100491849419989746303221165)
    ·
      refine ⟨37684443532496154863707937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100491849419989746303221165 37684443532496154863707937)
      ·
        refine ⟨28263332649372116147780953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37684443532496154863707937 28263332649372116147780953)
        ·
          refine ⟨21197499487029087110835715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28263332649372116147780953 21197499487029087110835715)
          ·
            refine ⟨31796249230543630666253573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21197499487029087110835715 31796249230543630666253573)
            ·
              refine ⟨5961796730726930749922545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31796249230543630666253573 5961796730726930749922545)
              ·
                refine ⟨4471347548045198062441909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5961796730726930749922545 4471347548045198062441909)
                ·
                  refine ⟨419188832629237318353929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4471347548045198062441909 419188832629237318353929)
                  ·
                    rfl

theorem cell23_7347306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 5].length) (baseStart_7347306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347306 prefixEnd_7347306 := by exact prefixLift 7347306
  have htrace : WordTrace (prefixWord ++ tailWord_7347306) baseStart_7347306 baseEnd_7347306 := by
    simpa [prefixWord, tailWord_7347306, baseEnd_7347306] using wordTrace_append hprefix tailTrace_7347306
  have hstable : (prefixWord ++ tailWord_7347306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347306).length < 2 ^ (prefixWord ++ tailWord_7347306).sum := by decide
  have hdescent : baseEnd_7347306 < baseStart_7347306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347309 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7347309 : Nat := 118140960795 + 7347309 * 2 ^ 59
def prefixEnd_7347309 : Nat := 4983230072969 + 3 ^ 40 * 7347309 * 2
def baseEnd_7347309 : Nat := 3772701034105099353447847

theorem tailTrace_7347309 : CollatzResearch.WordTrace tailWord_7347309 prefixEnd_7347309 3772701034105099353447847 := by
  unfold tailWord_7347309
  simp only [CollatzResearch.WordTrace]
  refine ⟨267978374538961788320948981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178652249692641192213965987 267978374538961788320948981)
  ·
    refine ⟨25122972613027667655088967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267978374538961788320948981 25122972613027667655088967)
    ·
      refine ⟨37684458919541501482633451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25122972613027667655088967 37684458919541501482633451)
      ·
        refine ⟨56526688379312252223950177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37684458919541501482633451 56526688379312252223950177)
        ·
          refine ⟨42395016284484189167962633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56526688379312252223950177 42395016284484189167962633)
          ·
            refine ⟨31796262213363141875971975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42395016284484189167962633 31796262213363141875971975)
            ·
              refine ⟨47694393320044712813957963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31796262213363141875971975 47694393320044712813957963)
              ·
                refine ⟨71541589980067069220936945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47694393320044712813957963 71541589980067069220936945)
                ·
                  refine ⟨53656192485050301915702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71541589980067069220936945 53656192485050301915702709)
                  ·
                    refine ⟨5030268045473465804597129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53656192485050301915702709 5030268045473465804597129)
                    ·
                      refine ⟨3772701034105099353447847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030268045473465804597129 3772701034105099353447847)
                      ·
                        rfl

theorem cell23_7347309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7347309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347309 prefixEnd_7347309 := by exact prefixLift 7347309
  have htrace : WordTrace (prefixWord ++ tailWord_7347309) baseStart_7347309 baseEnd_7347309 := by
    simpa [prefixWord, tailWord_7347309, baseEnd_7347309] using wordTrace_append hprefix tailTrace_7347309
  have hstable : (prefixWord ++ tailWord_7347309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347309).length < 2 ^ (prefixWord ++ tailWord_7347309).sum := by decide
  have hdescent : baseEnd_7347309 < baseStart_7347309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347336 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 2, 5]
def baseStart_7347336 : Nat := 118140960795 + 7347336 * 2 ^ 59
def prefixEnd_7347336 : Nat := 4983230072969 + 3 ^ 40 * 7347336 * 2
def baseEnd_7347336 : Nat := 1257571632694256915936741

theorem tailTrace_7347336 : CollatzResearch.WordTrace tailWord_7347336 prefixEnd_7347336 1257571632694256915936741 := by
  unfold tailWord_7347336
  simp only [CollatzResearch.WordTrace]
  refine ⟨133989679654931985966090931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178652906206575981288121241 133989679654931985966090931)
  ·
    refine ⟨200984519482397978949136397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133989679654931985966090931 200984519482397978949136397)
    ·
      refine ⟨75369194805899242105926149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200984519482397978949136397 75369194805899242105926149)
      ·
        refine ⟨14131724026106107894861153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75369194805899242105926149 14131724026106107894861153)
        ·
          refine ⟨10598793019579580921145865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14131724026106107894861153 10598793019579580921145865)
          ·
            refine ⟨7949094764684685690859399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10598793019579580921145865 7949094764684685690859399)
            ·
              refine ⟨11923642147027028536289099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949094764684685690859399 11923642147027028536289099)
              ·
                refine ⟨17885463220540542804433649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11923642147027028536289099 17885463220540542804433649)
                ·
                  refine ⟨13414097415405407103325237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17885463220540542804433649 13414097415405407103325237)
                  ·
                    refine ⟨1257571632694256915936741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13414097415405407103325237 1257571632694256915936741)
                    ·
                      rfl

theorem cell23_7347336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_7347336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347336 prefixEnd_7347336 := by exact prefixLift 7347336
  have htrace : WordTrace (prefixWord ++ tailWord_7347336) baseStart_7347336 baseEnd_7347336 := by
    simpa [prefixWord, tailWord_7347336, baseEnd_7347336] using wordTrace_append hprefix tailTrace_7347336
  have hstable : (prefixWord ++ tailWord_7347336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347336).length < 2 ^ (prefixWord ++ tailWord_7347336).sum := by decide
  have hdescent : baseEnd_7347336 < baseStart_7347336 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347352 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_7347352 : Nat := 118140960795 + 7347352 * 2 ^ 59
def prefixEnd_7347352 : Nat := 4983230072969 + 3 ^ 40 * 7347352 * 2
def baseEnd_7347352 : Nat := 3772723113773242685210149

theorem tailTrace_7347352 : CollatzResearch.WordTrace tailWord_7347352 prefixEnd_7347352 3772723113773242685210149 := by
  unfold tailWord_7347352
  simp only [CollatzResearch.WordTrace]
  refine ⟨133989971438903003332382155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178653295251870671109842873 133989971438903003332382155)
  ·
    refine ⟨200984957158354504998573233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133989971438903003332382155 200984957158354504998573233)
    ·
      refine ⟨150738717868765878748929925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200984957158354504998573233 150738717868765878748929925)
      ·
        refine ⟨28263509600393602265424361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150738717868765878748929925 28263509600393602265424361)
        ·
          refine ⟨21197632200295201699068271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28263509600393602265424361 21197632200295201699068271)
          ·
            refine ⟨31796448300442802548602407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21197632200295201699068271 31796448300442802548602407)
            ·
              refine ⟨47694672450664203822903611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31796448300442802548602407 47694672450664203822903611)
              ·
                refine ⟨71542008675996305734355417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47694672450664203822903611 71542008675996305734355417)
                ·
                  refine ⟨53656506506997229300766563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71542008675996305734355417 53656506506997229300766563)
                  ·
                    refine ⟨80484759760495843951149845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53656506506997229300766563 80484759760495843951149845)
                    ·
                      refine ⟨3772723113773242685210149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80484759760495843951149845 3772723113773242685210149)
                      ·
                        rfl

theorem cell23_7347352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_7347352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347352 prefixEnd_7347352 := by exact prefixLift 7347352
  have htrace : WordTrace (prefixWord ++ tailWord_7347352) baseStart_7347352 baseEnd_7347352 := by
    simpa [prefixWord, tailWord_7347352, baseEnd_7347352] using wordTrace_append hprefix tailTrace_7347352
  have hstable : (prefixWord ++ tailWord_7347352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347352).length < 2 ^ (prefixWord ++ tailWord_7347352).sum := by decide
  have hdescent : baseEnd_7347352 < baseStart_7347352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347399 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 6, 3, 2]
def baseStart_7347399 : Nat := 118140960795 + 7347399 * 2 ^ 59
def prefixEnd_7347399 : Nat := 4983230072969 + 3 ^ 40 * 7347399 * 2
def baseEnd_7347399 : Nat := 3772747247364004001322433

theorem tailTrace_7347399 : CollatzResearch.WordTrace tailWord_7347399 prefixEnd_7347399 3772747247364004001322433 := by
  unfold tailWord_7347399
  simp only [CollatzResearch.WordTrace]
  refine ⟨267981657108635733691725251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178654438072423822461150167 267981657108635733691725251)
  ·
    refine ⟨401972485662953600537587877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267981657108635733691725251 401972485662953600537587877)
    ·
      refine ⟨75369841061803800100797727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401972485662953600537587877 75369841061803800100797727)
      ·
        refine ⟨113054761592705700151196591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75369841061803800100797727 113054761592705700151196591)
        ·
          refine ⟨169582142389058550226794887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113054761592705700151196591 169582142389058550226794887)
          ·
            refine ⟨254373213583587825340192331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169582142389058550226794887 254373213583587825340192331)
            ·
              refine ⟨381559820375381738010288497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254373213583587825340192331 381559820375381738010288497)
              ·
                refine ⟨286169865281536303507716373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381559820375381738010288497 286169865281536303507716373)
                ·
                  refine ⟨13414212435072014226924205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 286169865281536303507716373 13414212435072014226924205)
                  ·
                    refine ⟨5030329663152005335096577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13414212435072014226924205 5030329663152005335096577)
                    ·
                      refine ⟨3772747247364004001322433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030329663152005335096577 3772747247364004001322433)
                      ·
                        rfl

theorem cell23_7347399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 6, 3, 2].length) (baseStart_7347399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347399 prefixEnd_7347399 := by exact prefixLift 7347399
  have htrace : WordTrace (prefixWord ++ tailWord_7347399) baseStart_7347399 baseEnd_7347399 := by
    simpa [prefixWord, tailWord_7347399, baseEnd_7347399] using wordTrace_append hprefix tailTrace_7347399
  have hstable : (prefixWord ++ tailWord_7347399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347399).length < 2 ^ (prefixWord ++ tailWord_7347399).sum := by decide
  have hdescent : baseEnd_7347399 < baseStart_7347399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347449 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 3]
def baseStart_7347449 : Nat := 118140960795 + 7347449 * 2 ^ 59
def prefixEnd_7347449 : Nat := 4983230072969 + 3 ^ 40 * 7347449 * 2
def baseEnd_7347449 : Nat := 3772772921396728805697203

theorem tailTrace_7347449 : CollatzResearch.WordTrace tailWord_7347449 prefixEnd_7347449 3772772921396728805697203 := by
  unfold tailWord_7347449
  simp only [CollatzResearch.WordTrace]
  refine ⟨267983480758454592231045401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178655653838969728154030267 267983480758454592231045401)
  ·
    refine ⟨200987610568840944173284051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267983480758454592231045401 200987610568840944173284051)
    ·
      refine ⟨301481415853261416259926077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200987610568840944173284051 301481415853261416259926077)
      ·
        refine ⟨113055530944973031097472279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301481415853261416259926077 113055530944973031097472279)
        ·
          refine ⟨169583296417459546646208419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113055530944973031097472279 169583296417459546646208419)
          ·
            refine ⟨254374944626189319969312629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169583296417459546646208419 254374944626189319969312629)
            ·
              refine ⟨23847651058705248747123059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254374944626189319969312629 23847651058705248747123059)
              ·
                refine ⟨35771476588057873120684589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23847651058705248747123059 35771476588057873120684589)
                ·
                  refine ⟨13414303720521702420256721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35771476588057873120684589 13414303720521702420256721)
                  ·
                    refine ⟨10060727790391276815192541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13414303720521702420256721 10060727790391276815192541)
                    ·
                      refine ⟨3772772921396728805697203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060727790391276815192541 3772772921396728805697203)
                      ·
                        rfl

theorem cell23_7347449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_7347449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347449 prefixEnd_7347449 := by exact prefixLift 7347449
  have htrace : WordTrace (prefixWord ++ tailWord_7347449) baseStart_7347449 baseEnd_7347449 := by
    simpa [prefixWord, tailWord_7347449, baseEnd_7347449] using wordTrace_append hprefix tailTrace_7347449
  have hstable : (prefixWord ++ tailWord_7347449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347449).length < 2 ^ (prefixWord ++ tailWord_7347449).sum := by decide
  have hdescent : baseEnd_7347449 < baseStart_7347449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347459 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4]
def baseStart_7347459 : Nat := 118140960795 + 7347459 * 2 ^ 59
def prefixEnd_7347459 : Nat := 4983230072969 + 3 ^ 40 * 7347459 * 2
def baseEnd_7347459 : Nat := 3772778056203273766572157

theorem tailTrace_7347459 : CollatzResearch.WordTrace tailWord_7347459 prefixEnd_7347459 3772778056203273766572157 := by
  unfold tailWord_7347459
  simp only [CollatzResearch.WordTrace]
  refine ⟨267983845488418363938909431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178655896992278909292606287 267983845488418363938909431)
  ·
    refine ⟨401975768232627545908364147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267983845488418363938909431 401975768232627545908364147)
    ·
      refine ⟨602963652348941318862546221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401975768232627545908364147 602963652348941318862546221)
      ·
        refine ⟨226111369630852994573454833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602963652348941318862546221 226111369630852994573454833)
        ·
          refine ⟨169583527223139745930091125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226111369630852994573454833 169583527223139745930091125)
          ·
            refine ⟨15898455677169351180946043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169583527223139745930091125 15898455677169351180946043)
            ·
              refine ⟨23847683515754026771419065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15898455677169351180946043 23847683515754026771419065)
              ·
                refine ⟨17885762636815520078564299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23847683515754026771419065 17885762636815520078564299)
                ·
                  refine ⟨26828643955223280117846449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17885762636815520078564299 26828643955223280117846449)
                  ·
                    refine ⟨20121482966417460088384837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26828643955223280117846449 20121482966417460088384837)
                    ·
                      refine ⟨3772778056203273766572157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20121482966417460088384837 3772778056203273766572157)
                      ·
                        rfl

theorem cell23_7347459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_7347459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347459 prefixEnd_7347459 := by exact prefixLift 7347459
  have htrace : WordTrace (prefixWord ++ tailWord_7347459) baseStart_7347459 baseEnd_7347459 := by
    simpa [prefixWord, tailWord_7347459, baseEnd_7347459] using wordTrace_append hprefix tailTrace_7347459
  have hstable : (prefixWord ++ tailWord_7347459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347459).length < 2 ^ (prefixWord ++ tailWord_7347459).sum := by decide
  have hdescent : baseEnd_7347459 < baseStart_7347459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347479 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3]
def baseStart_7347479 : Nat := 118140960795 + 7347479 * 2 ^ 59
def prefixEnd_7347479 : Nat := 4983230072969 + 3 ^ 40 * 7347479 * 2
def baseEnd_7347479 : Nat := 3772788325816363688322065

theorem tailTrace_7347479 : CollatzResearch.WordTrace tailWord_7347479 prefixEnd_7347479 3772788325816363688322065 := by
  unfold tailWord_7347479
  simp only [CollatzResearch.WordTrace]
  refine ⟨267984574948345907354637491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178656383298897271569758327 267984574948345907354637491)
  ·
    refine ⟨401976862422518861031956237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267984574948345907354637491 401976862422518861031956237)
    ·
      refine ⟨150741323408444572886983589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401976862422518861031956237 150741323408444572886983589)
      ·
        refine ⟨28263998139083357416309423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150741323408444572886983589 28263998139083357416309423)
        ·
          refine ⟨42395997208625036124464135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28263998139083357416309423 42395997208625036124464135)
          ·
            refine ⟨63593995812937554186696203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42395997208625036124464135 63593995812937554186696203)
            ·
              refine ⟨95390993719406331280044305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63593995812937554186696203 95390993719406331280044305)
              ·
                refine ⟨71543245289554748460033229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95390993719406331280044305 71543245289554748460033229)
                ·
                  refine ⟨26828716983583030672512461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71543245289554748460033229 26828716983583030672512461)
                  ·
                    refine ⟨10060768868843636502192173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26828716983583030672512461 10060768868843636502192173)
                    ·
                      refine ⟨3772788325816363688322065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060768868843636502192173 3772788325816363688322065)
                      ·
                        rfl

theorem cell23_7347479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_7347479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347479 prefixEnd_7347479 := by exact prefixLift 7347479
  have htrace : WordTrace (prefixWord ++ tailWord_7347479) baseStart_7347479 baseEnd_7347479 := by
    simpa [prefixWord, tailWord_7347479, baseEnd_7347479] using wordTrace_append hprefix tailTrace_7347479
  have hstable : (prefixWord ++ tailWord_7347479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347479).length < 2 ^ (prefixWord ++ tailWord_7347479).sum := by decide
  have hdescent : baseEnd_7347479 < baseStart_7347479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347480 : List Nat := [2, 1, 2, 3, 1, 4, 1, 4, 1, 2, 2]
def baseStart_7347480 : Nat := 118140960795 + 7347480 * 2 ^ 59
def prefixEnd_7347480 : Nat := 4983230072969 + 3 ^ 40 * 7347480 * 2
def baseEnd_7347480 : Nat := 3772788839297018184409561

theorem tailTrace_7347480 : CollatzResearch.WordTrace tailWord_7347480 prefixEnd_7347480 3772788839297018184409561 := by
  unfold tailWord_7347480
  simp only [CollatzResearch.WordTrace]
  refine ⟨133992305710671142262711947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178656407614228189683615929 133992305710671142262711947)
  ·
    refine ⟨200988458566006713394067921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133992305710671142262711947 200988458566006713394067921)
    ·
      refine ⟨150741343924505035045550941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200988458566006713394067921 150741343924505035045550941)
      ·
        refine ⟨56528003971689388142081603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150741343924505035045550941 56528003971689388142081603)
        ·
          refine ⟨84792005957534082213122405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56528003971689388142081603 84792005957534082213122405)
          ·
            refine ⟨15898501117037640414960451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84792005957534082213122405 15898501117037640414960451)
            ·
              refine ⟨23847751675556460622440677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15898501117037640414960451 23847751675556460622440677)
              ·
                refine ⟨4471453439166836366707627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23847751675556460622440677 4471453439166836366707627)
                ·
                  refine ⟨6707180158750254550061441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471453439166836366707627 6707180158750254550061441)
                  ·
                    refine ⟨5030385119062690912546081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6707180158750254550061441 5030385119062690912546081)
                    ·
                      refine ⟨3772788839297018184409561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030385119062690912546081 3772788839297018184409561)
                      ·
                        rfl

theorem cell23_7347480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_7347480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347480 prefixEnd_7347480 := by exact prefixLift 7347480
  have htrace : WordTrace (prefixWord ++ tailWord_7347480) baseStart_7347480 baseEnd_7347480 := by
    simpa [prefixWord, tailWord_7347480, baseEnd_7347480] using wordTrace_append hprefix tailTrace_7347480
  have hstable : (prefixWord ++ tailWord_7347480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347480).length < 2 ^ (prefixWord ++ tailWord_7347480).sum := by decide
  have hdescent : baseEnd_7347480 < baseStart_7347480 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347496 : List Nat := [2, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_7347496 : Nat := 118140960795 + 7347496 * 2 ^ 59
def prefixEnd_7347496 : Nat := 4983230072969 + 3 ^ 40 * 7347496 * 2
def baseEnd_7347496 : Nat := 3772797054987490121809487

theorem tailTrace_7347496 : CollatzResearch.WordTrace tailWord_7347496 prefixEnd_7347496 3772797054987490121809487 := by
  unfold tailWord_7347496
  simp only [CollatzResearch.WordTrace]
  refine ⟨133992597494642159629003171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178656796659522879505337561 133992597494642159629003171)
  ·
    refine ⟨200988896241963239443504757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133992597494642159629003171 200988896241963239443504757)
    ·
      refine ⟨18842709022684053697828571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200988896241963239443504757 18842709022684053697828571)
      ·
        refine ⟨28264063534026080546742857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18842709022684053697828571 28264063534026080546742857)
        ·
          refine ⟨21198047650519560410057143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264063534026080546742857 21198047650519560410057143)
          ·
            refine ⟨31797071475779340615085715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21198047650519560410057143 31797071475779340615085715)
            ·
              refine ⟨47695607213669010922628573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31797071475779340615085715 47695607213669010922628573)
              ·
                refine ⟨17885852705125879095985715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47695607213669010922628573 17885852705125879095985715)
                ·
                  refine ⟨26828779057688818643978573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17885852705125879095985715 26828779057688818643978573)
                  ·
                    refine ⟨10060792146633306991491965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26828779057688818643978573 10060792146633306991491965)
                    ·
                      refine ⟨3772797054987490121809487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060792146633306991491965 3772797054987490121809487)
                      ·
                        rfl

theorem cell23_7347496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_7347496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347496 prefixEnd_7347496 := by exact prefixLift 7347496
  have htrace : WordTrace (prefixWord ++ tailWord_7347496) baseStart_7347496 baseEnd_7347496 := by
    simpa [prefixWord, tailWord_7347496, baseEnd_7347496] using wordTrace_append hprefix tailTrace_7347496
  have hstable : (prefixWord ++ tailWord_7347496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347496).length < 2 ^ (prefixWord ++ tailWord_7347496).sum := by decide
  have hdescent : baseEnd_7347496 < baseStart_7347496 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347512 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 8]
def baseStart_7347512 : Nat := 118140960795 + 7347512 * 2 ^ 59
def prefixEnd_7347512 : Nat := 4983230072969 + 3 ^ 40 * 7347512 * 2
def baseEnd_7347512 : Nat := 1257601756892654019736471

theorem tailTrace_7347512 : CollatzResearch.WordTrace tailWord_7347512 prefixEnd_7347512 1257601756892654019736471 := by
  unfold tailWord_7347512
  simp only [CollatzResearch.WordTrace]
  refine ⟨133992889278613176995294395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178657185704817569327059193 133992889278613176995294395)
  ·
    refine ⟨200989333917919765492941593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133992889278613176995294395 200989333917919765492941593)
    ·
      refine ⟨150742000438439824119706195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200989333917919765492941593 150742000438439824119706195)
      ·
        refine ⟨226113000657659736179559293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150742000438439824119706195 226113000657659736179559293)
        ·
          refine ⟨84792375246622401067334735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226113000657659736179559293 84792375246622401067334735)
          ·
            refine ⟨127188562869933601601002103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84792375246622401067334735 127188562869933601601002103)
            ·
              refine ⟨190782844304900402401503155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127188562869933601601002103 190782844304900402401503155)
              ·
                refine ⟨286174266457350603602254733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190782844304900402401503155 286174266457350603602254733)
                ·
                  refine ⟨107315349921506476350845525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286174266457350603602254733 107315349921506476350845525)
                  ·
                    refine ⟨1257601756892654019736471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107315349921506476350845525 1257601756892654019736471)
                    ·
                      rfl

theorem cell23_7347512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_7347512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347512 prefixEnd_7347512 := by exact prefixLift 7347512
  have htrace : WordTrace (prefixWord ++ tailWord_7347512) baseStart_7347512 baseEnd_7347512 := by
    simpa [prefixWord, tailWord_7347512, baseEnd_7347512] using wordTrace_append hprefix tailTrace_7347512
  have hstable : (prefixWord ++ tailWord_7347512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347512).length < 2 ^ (prefixWord ++ tailWord_7347512).sum := by decide
  have hdescent : baseEnd_7347512 < baseStart_7347512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347517 : List Nat := [1, 4, 1, 5, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7347517 : Nat := 118140960795 + 7347517 * 2 ^ 59
def prefixEnd_7347517 : Nat := 4983230072969 + 3 ^ 40 * 7347517 * 2
def baseEnd_7347517 : Nat := 3772807838081234539646891

theorem tailTrace_7347517 : CollatzResearch.WordTrace tailWord_7347517 prefixEnd_7347517 3772807838081234539646891 := by
  unfold tailWord_7347517
  simp only [CollatzResearch.WordTrace]
  refine ⟨267985960922208239844520805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178657307281472159896347203 267985960922208239844520805)
  ·
    refine ⟨50247367672914044970847651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267985960922208239844520805 50247367672914044970847651)
    ·
      refine ⟨75371051509371067456271477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50247367672914044970847651 75371051509371067456271477)
      ·
        refine ⟨7066036079003537574025451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75371051509371067456271477 7066036079003537574025451)
        ·
          refine ⟨10599054118505306361038177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7066036079003537574025451 10599054118505306361038177)
          ·
            refine ⟨7949290588878979770778633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10599054118505306361038177 7949290588878979770778633)
            ·
              refine ⟨5961967941659234828083975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7949290588878979770778633 5961967941659234828083975)
              ·
                refine ⟨8942951912488852242125963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961967941659234828083975 8942951912488852242125963)
                ·
                  refine ⟨13414427868733278363188945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8942951912488852242125963 13414427868733278363188945)
                  ·
                    refine ⟨10060820901549958772391709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13414427868733278363188945 10060820901549958772391709)
                    ·
                      refine ⟨3772807838081234539646891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060820901549958772391709 3772807838081234539646891)
                      ·
                        rfl

theorem cell23_7347517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7347517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347517 prefixEnd_7347517 := by exact prefixLift 7347517
  have htrace : WordTrace (prefixWord ++ tailWord_7347517) baseStart_7347517 baseEnd_7347517 := by
    simpa [prefixWord, tailWord_7347517, baseEnd_7347517] using wordTrace_append hprefix tailTrace_7347517
  have hstable : (prefixWord ++ tailWord_7347517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347517).length < 2 ^ (prefixWord ++ tailWord_7347517).sum := by decide
  have hdescent : baseEnd_7347517 < baseStart_7347517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347553 : List Nat := [1, 2, 3, 1, 1, 1, 1, 7, 2, 2, 2]
def baseStart_7347553 : Nat := 118140960795 + 7347553 * 2 ^ 59
def prefixEnd_7347553 : Nat := 4983230072969 + 3 ^ 40 * 7347553 * 2
def baseEnd_7347553 : Nat := 3772826323384796398796725

theorem tailTrace_7347553 : CollatzResearch.WordTrace tailWord_7347553 prefixEnd_7347553 3772826323384796398796725 := by
  unfold tailWord_7347553
  simp only [CollatzResearch.WordTrace]
  refine ⟨267987273950077817992831313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178658182633385211995220875 267987273950077817992831313)
  ·
    refine ⟨200990455462558363494623485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267987273950077817992831313 200990455462558363494623485)
    ·
      refine ⟨75371420798459386310483807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200990455462558363494623485 75371420798459386310483807)
      ·
        refine ⟨113057131197689079465725711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75371420798459386310483807 113057131197689079465725711)
        ·
          refine ⟨169585696796533619198588567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113057131197689079465725711 169585696796533619198588567)
          ·
            refine ⟨254378545194800428797882851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169585696796533619198588567 254378545194800428797882851)
            ·
              refine ⟨381567817792200643196824277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254378545194800428797882851 381567817792200643196824277)
              ·
                refine ⟨8942995729504702574925569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 381567817792200643196824277 8942995729504702574925569)
                ·
                  refine ⟨6707246797128526931194177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8942995729504702574925569 6707246797128526931194177)
                  ·
                    refine ⟨5030435097846395198395633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6707246797128526931194177 5030435097846395198395633)
                    ·
                      refine ⟨3772826323384796398796725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030435097846395198395633 3772826323384796398796725)
                      ·
                        rfl

theorem cell23_7347553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_7347553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347553 prefixEnd_7347553 := by exact prefixLift 7347553
  have htrace : WordTrace (prefixWord ++ tailWord_7347553) baseStart_7347553 baseEnd_7347553 := by
    simpa [prefixWord, tailWord_7347553, baseEnd_7347553] using wordTrace_append hprefix tailTrace_7347553
  have hstable : (prefixWord ++ tailWord_7347553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347553).length < 2 ^ (prefixWord ++ tailWord_7347553).sum := by decide
  have hdescent : baseEnd_7347553 < baseStart_7347553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347569 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 3]
def baseStart_7347569 : Nat := 118140960795 + 7347569 * 2 ^ 59
def prefixEnd_7347569 : Nat := 4983230072969 + 3 ^ 40 * 7347569 * 2
def baseEnd_7347569 : Nat := 3772834539075268336196651

theorem tailTrace_7347569 : CollatzResearch.WordTrace tailWord_7347569 prefixEnd_7347569 3772834539075268336196651 := by
  unfold tailWord_7347569
  simp only [CollatzResearch.WordTrace]
  refine ⟨267987857518019852725413761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178658571678679901816942507 267987857518019852725413761)
  ·
    refine ⟨200990893138514889544060321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267987857518019852725413761 200990893138514889544060321)
    ·
      refine ⟨150743169853886167158045241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200990893138514889544060321 150743169853886167158045241)
      ·
        refine ⟨113057377390414625368533931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150743169853886167158045241 113057377390414625368533931)
        ·
          refine ⟨169586066085621938052800897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113057377390414625368533931 169586066085621938052800897)
          ·
            refine ⟨127189549564216453539600673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169586066085621938052800897 127189549564216453539600673)
            ·
              refine ⟨95392162173162340154700505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127189549564216453539600673 95392162173162340154700505)
              ·
                refine ⟨71544121629871755116025379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95392162173162340154700505 71544121629871755116025379)
                ·
                  refine ⟨107316182444807632674038069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71544121629871755116025379 107316182444807632674038069)
                  ·
                    refine ⟨10060892104200715563191069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107316182444807632674038069 10060892104200715563191069)
                    ·
                      refine ⟨3772834539075268336196651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060892104200715563191069 3772834539075268336196651)
                      ·
                        rfl

theorem cell23_7347569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 3].length) (baseStart_7347569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347569 prefixEnd_7347569 := by exact prefixLift 7347569
  have htrace : WordTrace (prefixWord ++ tailWord_7347569) baseStart_7347569 baseEnd_7347569 := by
    simpa [prefixWord, tailWord_7347569, baseEnd_7347569] using wordTrace_append hprefix tailTrace_7347569
  have hstable : (prefixWord ++ tailWord_7347569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347569).length < 2 ^ (prefixWord ++ tailWord_7347569).sum := by decide
  have hdescent : baseEnd_7347569 < baseStart_7347569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347589 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 4, 5]
def baseStart_7347589 : Nat := 118140960795 + 7347589 * 2 ^ 59
def prefixEnd_7347589 : Nat := 4983230072969 + 3 ^ 40 * 7347589 * 2
def baseEnd_7347589 : Nat := 1257614936229452752648853

theorem tailTrace_7347589 : CollatzResearch.WordTrace tailWord_7347589 prefixEnd_7347589 1257614936229452752648853 := by
  unfold tailWord_7347589
  simp only [CollatzResearch.WordTrace]
  refine ⟨267988586977947396141141821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178659057985298264094094547 267988586977947396141141821)
  ·
    refine ⟨100495720116730273552928183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267988586977947396141141821 100495720116730273552928183)
    ·
      refine ⟨150743580175095410329392275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100495720116730273552928183 150743580175095410329392275)
      ·
        refine ⟨226115370262643115494088413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150743580175095410329392275 226115370262643115494088413)
        ·
          refine ⟨84793263848491168310283155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226115370262643115494088413 84793263848491168310283155)
          ·
            refine ⟨127189895772736752465424733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84793263848491168310283155 127189895772736752465424733)
            ·
              refine ⟨47696210914776282174534275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127189895772736752465424733 47696210914776282174534275)
              ·
                refine ⟨71544316372164423261801413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47696210914776282174534275 71544316372164423261801413)
                ·
                  refine ⟨13414559319780829361587765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71544316372164423261801413 13414559319780829361587765)
                  ·
                    refine ⟨1257614936229452752648853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13414559319780829361587765 1257614936229452752648853)
                    ·
                      rfl

theorem cell23_7347589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_7347589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347589 prefixEnd_7347589 := by exact prefixLift 7347589
  have htrace : WordTrace (prefixWord ++ tailWord_7347589) baseStart_7347589 baseEnd_7347589 := by
    simpa [prefixWord, tailWord_7347589, baseEnd_7347589] using wordTrace_append hprefix tailTrace_7347589
  have hstable : (prefixWord ++ tailWord_7347589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347589).length < 2 ^ (prefixWord ++ tailWord_7347589).sum := by decide
  have hdescent : baseEnd_7347589 < baseStart_7347589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347593 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 7]
def baseStart_7347593 : Nat := 118140960795 + 7347593 * 2 ^ 59
def prefixEnd_7347593 : Nat := 4983230072969 + 3 ^ 40 * 7347593 * 2
def baseEnd_7347593 : Nat := 419205206956775138032949

theorem tailTrace_7347593 : CollatzResearch.WordTrace tailWord_7347593 prefixEnd_7347593 419205206956775138032949 := by
  unfold tailWord_7347593
  simp only [CollatzResearch.WordTrace]
  refine ⟨267988732869932904824287433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178659155246621936549524955 267988732869932904824287433)
  ·
    refine ⟨200991549652449678618215575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267988732869932904824287433 200991549652449678618215575)
    ·
      refine ⟨301487324478674517927323363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200991549652449678618215575 301487324478674517927323363)
      ·
        refine ⟨452230986718011776890985045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301487324478674517927323363 452230986718011776890985045)
        ·
          refine ⟨5299581875601700510441231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 452230986718011776890985045 5299581875601700510441231)
          ·
            refine ⟨7949372813402550765661847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299581875601700510441231 7949372813402550765661847)
            ·
              refine ⟨11924059220103826148492771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949372813402550765661847 11924059220103826148492771)
              ·
                refine ⟨17886088830155739222739157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11924059220103826148492771 17886088830155739222739157)
                ·
                  refine ⟨419205206956775138032949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17886088830155739222739157 419205206956775138032949)
                  ·
                    rfl

theorem cell23_7347593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 7].length) (baseStart_7347593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347593 prefixEnd_7347593 := by exact prefixLift 7347593
  have htrace : WordTrace (prefixWord ++ tailWord_7347593) baseStart_7347593 baseEnd_7347593 := by
    simpa [prefixWord, tailWord_7347593, baseEnd_7347593] using wordTrace_append hprefix tailTrace_7347593
  have hstable : (prefixWord ++ tailWord_7347593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347593).length < 2 ^ (prefixWord ++ tailWord_7347593).sum := by decide
  have hdescent : baseEnd_7347593 < baseStart_7347593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347596 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_7347596 : Nat := 118140960795 + 7347596 * 2 ^ 59
def prefixEnd_7347596 : Nat := 4983230072969 + 3 ^ 40 * 7347596 * 2
def baseEnd_7347596 : Nat := 3772848403052939730559027

theorem tailTrace_7347596 : CollatzResearch.WordTrace tailWord_7347596 prefixEnd_7347596 3772848403052939730559027 := by
  unfold tailWord_7347596
  simp only [CollatzResearch.WordTrace]
  refine ⟨133994421144461018168323321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178659228192614690891097761 133994421144461018168323321)
  ·
    refine ⟨100495815858345763626242491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133994421144461018168323321 100495815858345763626242491)
    ·
      refine ⟨150743723787518645439363737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100495815858345763626242491 150743723787518645439363737)
      ·
        refine ⟨113057792840638984079522803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150743723787518645439363737 113057792840638984079522803)
        ·
          refine ⟨169586689260958476119284205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113057792840638984079522803 169586689260958476119284205)
          ·
            refine ⟨63595008472859428544731577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169586689260958476119284205 63595008472859428544731577)
            ·
              refine ⟨47696256354644571408548683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63595008472859428544731577 47696256354644571408548683)
              ·
                refine ⟨71544384531966857112823025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47696256354644571408548683 71544384531966857112823025)
                ·
                  refine ⟨53658288398975142834617269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71544384531966857112823025 53658288398975142834617269)
                  ·
                    refine ⟨5030464537403919640745369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53658288398975142834617269 5030464537403919640745369)
                    ·
                      refine ⟨3772848403052939730559027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030464537403919640745369 3772848403052939730559027)
                      ·
                        rfl

theorem cell23_7347596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_7347596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347596 prefixEnd_7347596 := by exact prefixLift 7347596
  have htrace : WordTrace (prefixWord ++ tailWord_7347596) baseStart_7347596 baseEnd_7347596 := by
    simpa [prefixWord, tailWord_7347596, baseEnd_7347596] using wordTrace_append hprefix tailTrace_7347596
  have hstable : (prefixWord ++ tailWord_7347596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347596).length < 2 ^ (prefixWord ++ tailWord_7347596).sum := by decide
  have hdescent : baseEnd_7347596 < baseStart_7347596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347604 : List Nat := [2, 4, 2, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7347604 : Nat := 118140960795 + 7347604 * 2 ^ 59
def prefixEnd_7347604 : Nat := 4983230072969 + 3 ^ 40 * 7347604 * 2
def baseEnd_7347604 : Nat := 3772852510898175699258991

theorem tailTrace_7347604 : CollatzResearch.WordTrace tailWord_7347604 prefixEnd_7347604 3772852510898175699258991 := by
  unfold tailWord_7347604
  simp only [CollatzResearch.WordTrace]
  refine ⟨133994567036446526851468933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178659422715262035801958577 133994567036446526851468933)
  ·
    refine ⟨25123981319333723784650425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133994567036446526851468933 25123981319333723784650425)
    ·
      refine ⟨18842985989500292838487819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25123981319333723784650425 18842985989500292838487819)
      ·
        refine ⟨28264478984250439257731729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18842985989500292838487819 28264478984250439257731729)
        ·
          refine ⟨21198359238187829443298797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264478984250439257731729 21198359238187829443298797)
          ·
            refine ⟨7949384714320436041237049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21198359238187829443298797 7949384714320436041237049)
            ·
              refine ⟨5962038535740327030927787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7949384714320436041237049 5962038535740327030927787)
              ·
                refine ⟨8943057803610490546391681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962038535740327030927787 8943057803610490546391681)
                ·
                  refine ⟨6707293352707867909793761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8943057803610490546391681 6707293352707867909793761)
                  ·
                    refine ⟨5030470014530900932345321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6707293352707867909793761 5030470014530900932345321)
                    ·
                      refine ⟨3772852510898175699258991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030470014530900932345321 3772852510898175699258991)
                      ·
                        rfl

theorem cell23_7347604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7347604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347604 prefixEnd_7347604 := by exact prefixLift 7347604
  have htrace : WordTrace (prefixWord ++ tailWord_7347604) baseStart_7347604 baseEnd_7347604 := by
    simpa [prefixWord, tailWord_7347604, baseEnd_7347604] using wordTrace_append hprefix tailTrace_7347604
  have hstable : (prefixWord ++ tailWord_7347604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347604).length < 2 ^ (prefixWord ++ tailWord_7347604).sum := by decide
  have hdescent : baseEnd_7347604 < baseStart_7347604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347639 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6]
def baseStart_7347639 : Nat := 118140960795 + 7347639 * 2 ^ 59
def prefixEnd_7347639 : Nat := 4983230072969 + 3 ^ 40 * 7347639 * 2
def baseEnd_7347639 : Nat := 3772870482721083062321329

theorem tailTrace_7347639 : CollatzResearch.WordTrace tailWord_7347639 prefixEnd_7347639 3772870482721083062321329 := by
  unfold tailWord_7347639
  simp only [CollatzResearch.WordTrace]
  refine ⟨267990410627766254680461971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178660273751844169786974647 267990410627766254680461971)
  ·
    refine ⟨401985615941649382020692957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267990410627766254680461971 401985615941649382020692957)
    ·
      refine ⟨150744605978118518257759859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401985615941649382020692957 150744605978118518257759859)
      ·
        refine ⟨226116908967177777386639789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150744605978118518257759859 226116908967177777386639789)
        ·
          refine ⟨84793840862691666519989921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226116908967177777386639789 84793840862691666519989921)
          ·
            refine ⟨63595380647018749889992441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84793840862691666519989921 63595380647018749889992441)
            ·
              refine ⟨47696535485264062417494331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63595380647018749889992441 47696535485264062417494331)
              ·
                refine ⟨71544803227896093626241497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47696535485264062417494331 71544803227896093626241497)
                ·
                  refine ⟨53658602420922070219681123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71544803227896093626241497 53658602420922070219681123)
                  ·
                    refine ⟨80487903631383105329521685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53658602420922070219681123 80487903631383105329521685)
                    ·
                      refine ⟨3772870482721083062321329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80487903631383105329521685 3772870482721083062321329)
                      ·
                        rfl

theorem cell23_7347639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_7347639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347639 prefixEnd_7347639 := by exact prefixLift 7347639
  have htrace : WordTrace (prefixWord ++ tailWord_7347639) baseStart_7347639 baseEnd_7347639 := by
    simpa [prefixWord, tailWord_7347639, baseEnd_7347639] using wordTrace_append hprefix tailTrace_7347639
  have hstable : (prefixWord ++ tailWord_7347639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347639).length < 2 ^ (prefixWord ++ tailWord_7347639).sum := by decide
  have hdescent : baseEnd_7347639 < baseStart_7347639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347646 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3]
def baseStart_7347646 : Nat := 118140960795 + 7347646 * 2 ^ 59
def prefixEnd_7347646 : Nat := 4983230072969 + 3 ^ 40 * 7347646 * 2
def baseEnd_7347646 : Nat := 3772874077085664534933797

theorem tailTrace_7347646 : CollatzResearch.WordTrace tailWord_7347646 prefixEnd_7347646 3772874077085664534933797 := by
  unfold tailWord_7347646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33498833242342611859495849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178660443959160596583977861 33498833242342611859495849)
  ·
    refine ⟨25124124931756958894621887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33498833242342611859495849 25124124931756958894621887)
    ·
      refine ⟨37686187397635438341932831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25124124931756958894621887 37686187397635438341932831)
      ·
        refine ⟨56529281096453157512899247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37686187397635438341932831 56529281096453157512899247)
        ·
          refine ⟨84793921644679736269348871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56529281096453157512899247 84793921644679736269348871)
          ·
            refine ⟨127190882467019604404023307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84793921644679736269348871 127190882467019604404023307)
            ·
              refine ⟨190786323700529406606034961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127190882467019604404023307 190786323700529406606034961)
              ·
                refine ⟨143089742775397054954526221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190786323700529406606034961 143089742775397054954526221)
                ·
                  refine ⟨53658653540773895607947333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143089742775397054954526221 53658653540773895607947333)
                  ·
                    refine ⟨10060997538895105426490125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53658653540773895607947333 10060997538895105426490125)
                    ·
                      refine ⟨3772874077085664534933797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10060997538895105426490125 3772874077085664534933797)
                      ·
                        rfl

theorem cell23_7347646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_7347646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347646 prefixEnd_7347646 := by exact prefixLift 7347646
  have htrace : WordTrace (prefixWord ++ tailWord_7347646) baseStart_7347646 baseEnd_7347646 := by
    simpa [prefixWord, tailWord_7347646, baseEnd_7347646] using wordTrace_append hprefix tailTrace_7347646
  have hstable : (prefixWord ++ tailWord_7347646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347646).length < 2 ^ (prefixWord ++ tailWord_7347646).sum := by decide
  have hdescent : baseEnd_7347646 < baseStart_7347646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347670 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_7347670 : Nat := 118140960795 + 7347670 * 2 ^ 59
def prefixEnd_7347670 : Nat := 4983230072969 + 3 ^ 40 * 7347670 * 2
def baseEnd_7347670 : Nat := 1257628800207124147011229

theorem tailTrace_7347670 : CollatzResearch.WordTrace tailWord_7347670 prefixEnd_7347670 1257628800207124147011229 := by
  unfold tailWord_7347670
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749471330665871685927529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178661027527102631316560309 16749471330665871685927529)
  ·
    refine ⟨12562103497999403764445647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16749471330665871685927529 12562103497999403764445647)
    ·
      refine ⟨18843155246999105646668471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12562103497999403764445647 18843155246999105646668471)
      ·
        refine ⟨28264732870498658470002707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18843155246999105646668471 28264732870498658470002707)
        ·
          refine ⟨42397099305747987705004061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28264732870498658470002707 42397099305747987705004061)
          ·
            refine ⟨15898912239655495389376523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42397099305747987705004061 15898912239655495389376523)
            ·
              refine ⟨23848368359483243084064785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15898912239655495389376523 23848368359483243084064785)
              ·
                refine ⟨17886276269612432313048589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23848368359483243084064785 17886276269612432313048589)
                ·
                  refine ⟨6707353601104662117393221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17886276269612432313048589 6707353601104662117393221)
                  ·
                    refine ⟨1257628800207124147011229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707353601104662117393221 1257628800207124147011229)
                    ·
                      rfl

theorem cell23_7347670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_7347670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347670 prefixEnd_7347670 := by exact prefixLift 7347670
  have htrace : WordTrace (prefixWord ++ tailWord_7347670) baseStart_7347670 baseEnd_7347670 := by
    simpa [prefixWord, tailWord_7347670, baseEnd_7347670] using wordTrace_append hprefix tailTrace_7347670
  have hstable : (prefixWord ++ tailWord_7347670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347670).length < 2 ^ (prefixWord ++ tailWord_7347670).sum := by decide
  have hdescent : baseEnd_7347670 < baseStart_7347670 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347733 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_7347733 : Nat := 118140960795 + 7347733 * 2 ^ 59
def prefixEnd_7347733 : Nat := 4983230072969 + 3 ^ 40 * 7347733 * 2
def baseEnd_7347733 : Nat := 3772918749902605694545897

theorem tailTrace_7347733 : CollatzResearch.WordTrace tailWord_7347733 prefixEnd_7347733 3772918749902605694545897 := by
  unfold tailWord_7347733
  simp only [CollatzResearch.WordTrace]
  refine ⟨267993839089425708734383853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178662559392950472489589235 267993839089425708734383853)
  ·
    refine ⟨100497689658534640775393945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267993839089425708734383853 100497689658534640775393945)
    ·
      refine ⟨75373267243900980581545459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100497689658534640775393945 75373267243900980581545459)
      ·
        refine ⟨113059900865851470872318189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75373267243900980581545459 113059900865851470872318189)
        ·
          refine ⟨42397462824694301577119321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113059900865851470872318189 42397462824694301577119321)
          ·
            refine ⟨31798097118520726182839491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42397462824694301577119321 31798097118520726182839491)
            ·
              refine ⟨47697145677781089274259237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31798097118520726182839491 47697145677781089274259237)
              ·
                refine ⟨8943214814583954238923607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47697145677781089274259237 8943214814583954238923607)
                ·
                  refine ⟨13414822221875931358385411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8943214814583954238923607 13414822221875931358385411)
                  ·
                    refine ⟨20122233332813897037578117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13414822221875931358385411 20122233332813897037578117)
                    ·
                      refine ⟨3772918749902605694545897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20122233332813897037578117 3772918749902605694545897)
                      ·
                        rfl

theorem cell23_7347733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_7347733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347733 prefixEnd_7347733 := by exact prefixLift 7347733
  have htrace : WordTrace (prefixWord ++ tailWord_7347733) baseStart_7347733 baseEnd_7347733 := by
    simpa [prefixWord, tailWord_7347733, baseEnd_7347733] using wordTrace_append hprefix tailTrace_7347733
  have hstable : (prefixWord ++ tailWord_7347733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347733).length < 2 ^ (prefixWord ++ tailWord_7347733).sum := by decide
  have hdescent : baseEnd_7347733 < baseStart_7347733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347744 : List Nat := [2, 1, 1, 6, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7347744 : Nat := 118140960795 + 7347744 * 2 ^ 59
def prefixEnd_7347744 : Nat := 4983230072969 + 3 ^ 40 * 7347744 * 2
def baseEnd_7347744 : Nat := 3772924398189805151508347

theorem tailTrace_7347744 : CollatzResearch.WordTrace tailWord_7347744 prefixEnd_7347744 3772924398189805151508347 := by
  unfold tailWord_7347744
  simp only [CollatzResearch.WordTrace]
  refine ⟨133997120146192928806517143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178662826861590571742022857 133997120146192928806517143)
  ·
    refine ⟨200995680219289393209775715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133997120146192928806517143 200995680219289393209775715)
    ·
      refine ⟨301493520328934089814663573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200995680219289393209775715 301493520328934089814663573)
      ·
        refine ⟨14132508765418785460062355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301493520328934089814663573 14132508765418785460062355)
        ·
          refine ⟨21198763148128178190093533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14132508765418785460062355 21198763148128178190093533)
          ·
            refine ⟨7949536180548066821285075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21198763148128178190093533 7949536180548066821285075)
            ·
              refine ⟨11924304270822100231927613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949536180548066821285075 11924304270822100231927613)
              ·
                refine ⟨4471614101558287586972855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11924304270822100231927613 4471614101558287586972855)
                ·
                  refine ⟨6707421152337431380459283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471614101558287586972855 6707421152337431380459283)
                  ·
                    refine ⟨10061131728506147070688925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6707421152337431380459283 10061131728506147070688925)
                    ·
                      refine ⟨3772924398189805151508347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10061131728506147070688925 3772924398189805151508347)
                      ·
                        rfl

theorem cell23_7347744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7347744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347744 prefixEnd_7347744 := by exact prefixLift 7347744
  have htrace : WordTrace (prefixWord ++ tailWord_7347744) baseStart_7347744 baseEnd_7347744 := by
    simpa [prefixWord, tailWord_7347744, baseEnd_7347744] using wordTrace_append hprefix tailTrace_7347744
  have hstable : (prefixWord ++ tailWord_7347744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347744).length < 2 ^ (prefixWord ++ tailWord_7347744).sum := by decide
  have hdescent : baseEnd_7347744 < baseStart_7347744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347767 : List Nat := [1, 1, 3, 1, 2, 6, 1, 1, 3, 2, 2]
def baseStart_7347767 : Nat := 118140960795 + 7347767 * 2 ^ 59
def prefixEnd_7347767 : Nat := 4983230072969 + 3 ^ 40 * 7347767 * 2
def baseEnd_7347767 : Nat := 3772936208244858561520741

theorem tailTrace_7347767 : CollatzResearch.WordTrace tailWord_7347767 prefixEnd_7347767 3772936208244858561520741 := by
  unfold tailWord_7347767
  simp only [CollatzResearch.WordTrace]
  refine ⟨267995079171302532541121555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178663386114201688360747703 267995079171302532541121555)
  ·
    refine ⟨401992618756953798811682333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267995079171302532541121555 401992618756953798811682333)
    ·
      refine ⟨150747232033857674554380875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401992618756953798811682333 150747232033857674554380875)
      ·
        refine ⟨226120848050786511831571313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150747232033857674554380875 226120848050786511831571313)
        ·
          refine ⟨169590636038089883873678485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226120848050786511831571313 169590636038089883873678485)
          ·
            refine ⟨7949561064285463306578679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169590636038089883873678485 7949561064285463306578679)
            ·
              refine ⟨11924341596428194959868019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949561064285463306578679 11924341596428194959868019)
              ·
                refine ⟨17886512394642292439802029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11924341596428194959868019 17886512394642292439802029)
                ·
                  refine ⟨6707442147990859664925761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17886512394642292439802029 6707442147990859664925761)
                  ·
                    refine ⟨5030581610993144748694321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6707442147990859664925761 5030581610993144748694321)
                    ·
                      refine ⟨3772936208244858561520741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030581610993144748694321 3772936208244858561520741)
                      ·
                        rfl

theorem cell23_7347767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 1, 1, 3, 2, 2].length) (baseStart_7347767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347767 prefixEnd_7347767 := by exact prefixLift 7347767
  have htrace : WordTrace (prefixWord ++ tailWord_7347767) baseStart_7347767 baseEnd_7347767 := by
    simpa [prefixWord, tailWord_7347767, baseEnd_7347767] using wordTrace_append hprefix tailTrace_7347767
  have hstable : (prefixWord ++ tailWord_7347767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347767).length < 2 ^ (prefixWord ++ tailWord_7347767).sum := by decide
  have hdescent : baseEnd_7347767 < baseStart_7347767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347773 : List Nat := [1, 4, 1, 3, 3, 1, 2, 8]
def baseStart_7347773 : Nat := 118140960795 + 7347773 * 2 ^ 59
def prefixEnd_7347773 : Nat := 4983230072969 + 3 ^ 40 * 7347773 * 2
def baseEnd_7347773 : Nat := 139738492189955019927619

theorem tailTrace_7347773 : CollatzResearch.WordTrace tailWord_7347773 prefixEnd_7347773 139738492189955019927619 := by
  unfold tailWord_7347773
  simp only [CollatzResearch.WordTrace]
  refine ⟨267995298009280795565839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178663532006187197043893315 267995298009280795565839973)
  ·
    refine ⟨50249118376740149168594995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267995298009280795565839973 50249118376740149168594995)
    ·
      refine ⟨75373677565110223752892493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50249118376740149168594995 75373677565110223752892493)
      ·
        refine ⟨28265129086916333907334685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75373677565110223752892493 28265129086916333907334685)
        ·
          refine ⟨10599423407593625215250507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28265129086916333907334685 10599423407593625215250507)
          ·
            refine ⟨15899135111390437822875761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599423407593625215250507 15899135111390437822875761)
            ·
              refine ⟨11924351333542828367156821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15899135111390437822875761 11924351333542828367156821)
              ·
                refine ⟨139738492189955019927619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11924351333542828367156821 139738492189955019927619)
                ·
                  rfl

theorem cell23_7347773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 8].length) (baseStart_7347773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347773 prefixEnd_7347773 := by exact prefixLift 7347773
  have htrace : WordTrace (prefixWord ++ tailWord_7347773) baseStart_7347773 baseEnd_7347773 := by
    simpa [prefixWord, tailWord_7347773, baseEnd_7347773] using wordTrace_append hprefix tailTrace_7347773
  have hstable : (prefixWord ++ tailWord_7347773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347773).length < 2 ^ (prefixWord ++ tailWord_7347773).sum := by decide
  have hdescent : baseEnd_7347773 < baseStart_7347773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347823 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 5, 4, 2]
def baseStart_7347823 : Nat := 118140960795 + 7347823 * 2 ^ 59
def prefixEnd_7347823 : Nat := 4983230072969 + 3 ^ 40 * 7347823 * 2
def baseEnd_7347823 : Nat := 3772964963161510342420483

theorem tailTrace_7347823 : CollatzResearch.WordTrace tailWord_7347823 prefixEnd_7347823 3772964963161510342420483 := by
  unfold tailWord_7347823
  simp only [CollatzResearch.WordTrace]
  refine ⟨267997121659099654105160123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178664747772733102736773415 267997121659099654105160123)
  ·
    refine ⟨401995682488649481157740185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267997121659099654105160123 401995682488649481157740185)
    ·
      refine ⟨301496761866487110868305139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401995682488649481157740185 301496761866487110868305139)
      ·
        refine ⟨452245142799730666302457709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301496761866487110868305139 452245142799730666302457709)
        ·
          refine ⟨169591928549898999863421641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452245142799730666302457709 169591928549898999863421641)
          ·
            refine ⟨127193946412424249897566231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169591928549898999863421641 127193946412424249897566231)
            ·
              refine ⟨190790919618636374846349347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127193946412424249897566231 190790919618636374846349347)
              ·
                refine ⟨286186379427954562269524021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190790919618636374846349347 286186379427954562269524021)
                ·
                  refine ⟨26829973071370740212767877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286186379427954562269524021 26829973071370740212767877)
                  ·
                    refine ⟨5030619950882013789893977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26829973071370740212767877 5030619950882013789893977)
                    ·
                      refine ⟨3772964963161510342420483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030619950882013789893977 3772964963161510342420483)
                      ·
                        rfl

theorem cell23_7347823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 5, 4, 2].length) (baseStart_7347823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347823 prefixEnd_7347823 := by exact prefixLift 7347823
  have htrace : WordTrace (prefixWord ++ tailWord_7347823) baseStart_7347823 baseEnd_7347823 := by
    simpa [prefixWord, tailWord_7347823, baseEnd_7347823] using wordTrace_append hprefix tailTrace_7347823
  have hstable : (prefixWord ++ tailWord_7347823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347823).length < 2 ^ (prefixWord ++ tailWord_7347823).sum := by decide
  have hdescent : baseEnd_7347823 < baseStart_7347823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347840 : List Nat := [2, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2]
def baseStart_7347840 : Nat := 118140960795 + 7347840 * 2 ^ 59
def prefixEnd_7347840 : Nat := 4983230072969 + 3 ^ 40 * 7347840 * 2
def baseEnd_7347840 : Nat := 3772973692332636775907905

theorem tailTrace_7347840 : CollatzResearch.WordTrace tailWord_7347840 prefixEnd_7347840 3772973692332636775907905 := by
  unfold tailWord_7347840
  simp only [CollatzResearch.WordTrace]
  refine ⟨133998870850019033004264487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178665161133358710672352649 133998870850019033004264487)
  ·
    refine ⟨200998306275028549506396731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133998870850019033004264487 200998306275028549506396731)
    ·
      refine ⟨301497459412542824259595097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200998306275028549506396731 301497459412542824259595097)
      ·
        refine ⟨226123094559407118194696323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301497459412542824259595097 226123094559407118194696323)
        ·
          refine ⟨339184641839110677292044485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226123094559407118194696323 339184641839110677292044485)
          ·
            refine ⟨63597120344833251992258341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339184641839110677292044485 63597120344833251992258341)
            ·
              refine ⟨11924460064656234748548439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63597120344833251992258341 11924460064656234748548439)
              ·
                refine ⟨17886690096984352122822659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11924460064656234748548439 17886690096984352122822659)
                ·
                  refine ⟨26830035145476528184233989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17886690096984352122822659 26830035145476528184233989)
                  ·
                    refine ⟨5030631589776849034543873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26830035145476528184233989 5030631589776849034543873)
                    ·
                      refine ⟨3772973692332636775907905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030631589776849034543873 3772973692332636775907905)
                      ·
                        rfl

theorem cell23_7347840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_7347840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347840 prefixEnd_7347840 := by exact prefixLift 7347840
  have htrace : WordTrace (prefixWord ++ tailWord_7347840) baseStart_7347840 baseEnd_7347840 := by
    simpa [prefixWord, tailWord_7347840, baseEnd_7347840] using wordTrace_append hprefix tailTrace_7347840
  have hstable : (prefixWord ++ tailWord_7347840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347840).length < 2 ^ (prefixWord ++ tailWord_7347840).sum := by decide
  have hdescent : baseEnd_7347840 < baseStart_7347840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347870 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_7347870 : Nat := 118140960795 + 7347870 * 2 ^ 59
def prefixEnd_7347870 : Nat := 4983230072969 + 3 ^ 40 * 7347870 * 2
def baseEnd_7347870 : Nat := 3772989096752271658532767

theorem tailTrace_7347870 : CollatzResearch.WordTrace tailWord_7347870 prefixEnd_7347870 3772989096752271658532767 := by
  unfold tailWord_7347870
  simp only [CollatzResearch.WordTrace]
  refine ⟨33499854486241172641515133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178665890593286254088080709 33499854486241172641515133)
  ·
    refine ⟨12562445432340439740568175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33499854486241172641515133 12562445432340439740568175)
    ·
      refine ⟨18843668148510659610852263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12562445432340439740568175 18843668148510659610852263)
      ·
        refine ⟨28265502222765989416278395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18843668148510659610852263 28265502222765989416278395)
        ·
          refine ⟨42398253334148984124417593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28265502222765989416278395 42398253334148984124417593)
          ·
            refine ⟨31798690000611738093313195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42398253334148984124417593 31798690000611738093313195)
            ·
              refine ⟨47698035000917607139969793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31798690000611738093313195 47698035000917607139969793)
              ·
                refine ⟨35773526250688205354977345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47698035000917607139969793 35773526250688205354977345)
                ·
                  refine ⟨26830144688016154016233009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35773526250688205354977345 26830144688016154016233009)
                  ·
                    refine ⟨20122608516012115512174757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26830144688016154016233009 20122608516012115512174757)
                    ·
                      refine ⟨3772989096752271658532767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20122608516012115512174757 3772989096752271658532767)
                      ·
                        rfl

theorem cell23_7347870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_7347870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347870 prefixEnd_7347870 := by exact prefixLift 7347870
  have htrace : WordTrace (prefixWord ++ tailWord_7347870) baseStart_7347870 baseEnd_7347870 := by
    simpa [prefixWord, tailWord_7347870, baseEnd_7347870] using wordTrace_append hprefix tailTrace_7347870
  have hstable : (prefixWord ++ tailWord_7347870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347870).length < 2 ^ (prefixWord ++ tailWord_7347870).sum := by decide
  have hdescent : baseEnd_7347870 < baseStart_7347870 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347914 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 5]
def baseStart_7347914 : Nat := 118140960795 + 7347914 * 2 ^ 59
def prefixEnd_7347914 : Nat := 4983230072969 + 3 ^ 40 * 7347914 * 2
def baseEnd_7347914 : Nat := 419223521100118831820285

theorem tailTrace_7347914 : CollatzResearch.WordTrace tailWord_7347914 prefixEnd_7347914 419223521100118831820285 := by
  unfold tailWord_7347914
  simp only [CollatzResearch.WordTrace]
  refine ⟨67000110175442494161680699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178666960467846651097815197 67000110175442494161680699)
  ·
    refine ⟨100500165263163741242521049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67000110175442494161680699 100500165263163741242521049)
    ·
      refine ⟨75375123947372805931890787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100500165263163741242521049 75375123947372805931890787)
      ·
        refine ⟨113062685921059208897836181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75375123947372805931890787 113062685921059208897836181)
        ·
          refine ⟨5299813402549650417086071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113062685921059208897836181 5299813402549650417086071)
          ·
            refine ⟨7949720103824475625629107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299813402549650417086071 7949720103824475625629107)
            ·
              refine ⟨11924580155736713438443661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949720103824475625629107 11924580155736713438443661)
              ·
                refine ⟨4471717558401267539416373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11924580155736713438443661 4471717558401267539416373)
                ·
                  refine ⟨419223521100118831820285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4471717558401267539416373 419223521100118831820285)
                  ·
                    rfl

theorem cell23_7347914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 5].length) (baseStart_7347914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347914 prefixEnd_7347914 := by exact prefixLift 7347914
  have htrace : WordTrace (prefixWord ++ tailWord_7347914) baseStart_7347914 baseEnd_7347914 := by
    simpa [prefixWord, tailWord_7347914, baseEnd_7347914] using wordTrace_append hprefix tailTrace_7347914
  have hstable : (prefixWord ++ tailWord_7347914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347914).length < 2 ^ (prefixWord ++ tailWord_7347914).sum := by decide
  have hdescent : baseEnd_7347914 < baseStart_7347914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347930 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4]
def baseStart_7347930 : Nat := 118140960795 + 7347930 * 2 ^ 59
def prefixEnd_7347930 : Nat := 4983230072969 + 3 ^ 40 * 7347930 * 2
def baseEnd_7347930 : Nat := 3773019905591541423782491

theorem tailTrace_7347930 : CollatzResearch.WordTrace tailWord_7347930 prefixEnd_7347930 3773019905591541423782491 := by
  unfold tailWord_7347930
  simp only [CollatzResearch.WordTrace]
  refine ⟨67000256067428002844826311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178667349513141340919536829 67000256067428002844826311)
  ·
    refine ⟨100500384101142004267239467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67000256067428002844826311 100500384101142004267239467)
    ·
      refine ⟨150750576151713006400859201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100500384101142004267239467 150750576151713006400859201)
      ·
        refine ⟨113062932113784754800644401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150750576151713006400859201 113062932113784754800644401)
        ·
          refine ⟨84797199085338566100483301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113062932113784754800644401 84797199085338566100483301)
          ·
            refine ⟨15899474828500981143840619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84797199085338566100483301 15899474828500981143840619)
            ·
              refine ⟨23849212242751471715760929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15899474828500981143840619 23849212242751471715760929)
              ·
                refine ⟨17886909182063603786820697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23849212242751471715760929 17886909182063603786820697)
                ·
                  refine ⟨13415181886547702840115523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17886909182063603786820697 13415181886547702840115523)
                  ·
                    refine ⟨20122772829821554260173285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13415181886547702840115523 20122772829821554260173285)
                    ·
                      refine ⟨3773019905591541423782491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20122772829821554260173285 3773019905591541423782491)
                      ·
                        rfl

theorem cell23_7347930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_7347930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347930 prefixEnd_7347930 := by exact prefixLift 7347930
  have htrace : WordTrace (prefixWord ++ tailWord_7347930) baseStart_7347930 baseEnd_7347930 := by
    simpa [prefixWord, tailWord_7347930, baseEnd_7347930] using wordTrace_append hprefix tailTrace_7347930
  have hstable : (prefixWord ++ tailWord_7347930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347930).length < 2 ^ (prefixWord ++ tailWord_7347930).sum := by decide
  have hdescent : baseEnd_7347930 < baseStart_7347930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347950 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_7347950 : Nat := 118140960795 + 7347950 * 2 ^ 59
def prefixEnd_7347950 : Nat := 4983230072969 + 3 ^ 40 * 7347950 * 2
def baseEnd_7347950 : Nat := 3773030175204631345532399

theorem tailTrace_7347950 : CollatzResearch.WordTrace tailWord_7347950 prefixEnd_7347950 3773030175204631345532399 := by
  unfold tailWord_7347950
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500219216204944349379163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178667835819759703196688869 33500219216204944349379163)
  ·
    refine ⟨50250328824307416524068745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33500219216204944349379163 50250328824307416524068745)
    ·
      refine ⟨37687746618230562393051559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50250328824307416524068745 37687746618230562393051559)
      ·
        refine ⟨56531619927345843589577339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37687746618230562393051559 56531619927345843589577339)
        ·
          refine ⟨84797429891018765384366009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56531619927345843589577339 84797429891018765384366009)
          ·
            refine ⟨63598072418264074038274507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84797429891018765384366009 63598072418264074038274507)
            ·
              refine ⟨95397108627396111057411761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63598072418264074038274507 95397108627396111057411761)
              ·
                refine ⟨71547831470547083293058821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95397108627396111057411761 71547831470547083293058821)
                ·
                  refine ⟨13415218400727578117448529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71547831470547083293058821 13415218400727578117448529)
                  ·
                    refine ⟨10061413800545683588086397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13415218400727578117448529 10061413800545683588086397)
                    ·
                      refine ⟨3773030175204631345532399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10061413800545683588086397 3773030175204631345532399)
                      ·
                        rfl

theorem cell23_7347950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_7347950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347950 prefixEnd_7347950 := by exact prefixLift 7347950
  have htrace : WordTrace (prefixWord ++ tailWord_7347950) baseStart_7347950 baseEnd_7347950 := by
    simpa [prefixWord, tailWord_7347950, baseEnd_7347950] using wordTrace_append hprefix tailTrace_7347950
  have hstable : (prefixWord ++ tailWord_7347950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347950).length < 2 ^ (prefixWord ++ tailWord_7347950).sum := by decide
  have hdescent : baseEnd_7347950 < baseStart_7347950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7347991 : List Nat := [1, 1, 3, 4, 2, 3, 2, 2, 1, 4]
def baseStart_7347991 : Nat := 118140960795 + 7347991 * 2 ^ 59
def prefixEnd_7347991 : Nat := 4983230072969 + 3 ^ 40 * 7347991 * 2
def baseEnd_7347991 : Nat := 1257683742637155228373237

theorem tailTrace_7347991 : CollatzResearch.WordTrace tailWord_7347991 prefixEnd_7347991 1257683742637155228373237 := by
  unfold tailWord_7347991
  simp only [CollatzResearch.WordTrace]
  refine ⟨268003249122491018797275827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178668832748327345864850551 268003249122491018797275827)
  ·
    refine ⟨402004873683736528195913741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268003249122491018797275827 402004873683736528195913741)
    ·
      refine ⟨150751827631401198073467653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402004873683736528195913741 150751827631401198073467653)
      ·
        refine ⟨28265967680887724638775185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150751827631401198073467653 28265967680887724638775185)
        ·
          refine ⟨21199475760665793479081389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28265967680887724638775185 21199475760665793479081389)
          ·
            refine ⟨7949803410249672554655521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21199475760665793479081389 7949803410249672554655521)
            ·
              refine ⟨5962352557687254415991641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7949803410249672554655521 5962352557687254415991641)
              ·
                refine ⟨4471764418265440811993731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962352557687254415991641 4471764418265440811993731)
                ·
                  refine ⟨6707646627398161217990597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471764418265440811993731 6707646627398161217990597)
                  ·
                    refine ⟨1257683742637155228373237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707646627398161217990597 1257683742637155228373237)
                    ·
                      rfl

theorem cell23_7347991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 2, 2, 1, 4].length) (baseStart_7347991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7347991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7347991 prefixEnd_7347991 := by exact prefixLift 7347991
  have htrace : WordTrace (prefixWord ++ tailWord_7347991) baseStart_7347991 baseEnd_7347991 := by
    simpa [prefixWord, tailWord_7347991, baseEnd_7347991] using wordTrace_append hprefix tailTrace_7347991
  have hstable : (prefixWord ++ tailWord_7347991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7347991).length < 2 ^ (prefixWord ++ tailWord_7347991).sum := by decide
  have hdescent : baseEnd_7347991 < baseStart_7347991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7347991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348023 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5]
def baseStart_7348023 : Nat := 118140960795 + 7348023 * 2 ^ 59
def prefixEnd_7348023 : Nat := 4983230072969 + 3 ^ 40 * 7348023 * 2
def baseEnd_7348023 : Nat := 3773067659292409559919563

theorem tailTrace_7348023 : CollatzResearch.WordTrace tailWord_7348023 prefixEnd_7348023 3773067659292409559919563 := by
  unfold tailWord_7348023
  simp only [CollatzResearch.WordTrace]
  refine ⟨268004416258375088262440723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178669610838916725508293815 268004416258375088262440723)
  ·
    refine ⟨402006624387562632393661085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268004416258375088262440723 402006624387562632393661085)
    ·
      refine ⟨150752484145335987147622907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402006624387562632393661085 150752484145335987147622907)
      ·
        refine ⟨226128726218003980721434361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150752484145335987147622907 226128726218003980721434361)
        ·
          refine ⟨169596544663502985541075771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226128726218003980721434361 169596544663502985541075771)
          ·
            refine ⟨254394816995254478311613657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169596544663502985541075771 254394816995254478311613657)
            ·
              refine ⟨190796112746440858733710243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254394816995254478311613657 190796112746440858733710243)
              ·
                refine ⟨286194169119661288100565365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190796112746440858733710243 286194169119661288100565365)
                ·
                  refine ⟨26830703354968245759428003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 286194169119661288100565365 26830703354968245759428003)
                  ·
                    refine ⟨40246055032452368639142005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26830703354968245759428003 40246055032452368639142005)
                    ·
                      refine ⟨3773067659292409559919563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40246055032452368639142005 3773067659292409559919563)
                      ·
                        rfl

theorem cell23_7348023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_7348023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348023 prefixEnd_7348023 := by exact prefixLift 7348023
  have htrace : WordTrace (prefixWord ++ tailWord_7348023) baseStart_7348023 baseEnd_7348023 := by
    simpa [prefixWord, tailWord_7348023, baseEnd_7348023] using wordTrace_append hprefix tailTrace_7348023
  have hstable : (prefixWord ++ tailWord_7348023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348023).length < 2 ^ (prefixWord ++ tailWord_7348023).sum := by decide
  have hdescent : baseEnd_7348023 < baseStart_7348023 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348024 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2]
def baseStart_7348024 : Nat := 118140960795 + 7348024 * 2 ^ 59
def prefixEnd_7348024 : Nat := 4983230072969 + 3 ^ 40 * 7348024 * 2
def baseEnd_7348024 : Nat := 3773068172773064056007059

theorem tailTrace_7348024 : CollatzResearch.WordTrace tailWord_7348024 prefixEnd_7348024 3773068172773064056007059 := by
  unfold tailWord_7348024
  simp only [CollatzResearch.WordTrace]
  refine ⟨134002226365685732716613563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178669635154247643622151417 134002226365685732716613563)
  ·
    refine ⟨201003339548528599074920345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134002226365685732716613563 201003339548528599074920345)
    ·
      refine ⟨150752504661396449306190259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201003339548528599074920345 150752504661396449306190259)
      ·
        refine ⟨226128756992094673959285389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150752504661396449306190259 226128756992094673959285389)
        ·
          refine ⟨84798283872035502734732021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226128756992094673959285389 84798283872035502734732021)
          ·
            refine ⟨7949839113003328381381127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84798283872035502734732021 7949839113003328381381127)
            ·
              refine ⟨11924758669504992572071691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7949839113003328381381127 11924758669504992572071691)
              ·
                refine ⟨17887138004257488858107537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11924758669504992572071691 17887138004257488858107537)
                ·
                  refine ⟨13415353503193116643580653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17887138004257488858107537 13415353503193116643580653)
                  ·
                    refine ⟨5030757563697418741342745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13415353503193116643580653 5030757563697418741342745)
                    ·
                      refine ⟨3773068172773064056007059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030757563697418741342745 3773068172773064056007059)
                      ·
                        rfl

theorem cell23_7348024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 2, 3, 2].length) (baseStart_7348024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348024 prefixEnd_7348024 := by exact prefixLift 7348024
  have htrace : WordTrace (prefixWord ++ tailWord_7348024) baseStart_7348024 baseEnd_7348024 := by
    simpa [prefixWord, tailWord_7348024, baseEnd_7348024] using wordTrace_append hprefix tailTrace_7348024
  have hstable : (prefixWord ++ tailWord_7348024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348024).length < 2 ^ (prefixWord ++ tailWord_7348024).sum := by decide
  have hdescent : baseEnd_7348024 < baseStart_7348024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348031 : List Nat := [1, 1, 2, 2, 6, 1, 2, 3, 1, 1, 3]
def baseStart_7348031 : Nat := 118140960795 + 7348031 * 2 ^ 59
def prefixEnd_7348031 : Nat := 4983230072969 + 3 ^ 40 * 7348031 * 2
def baseEnd_7348031 : Nat := 3773071767137645528619527

theorem tailTrace_7348031 : CollatzResearch.WordTrace tailWord_7348031 prefixEnd_7348031 3773071767137645528619527 := by
  unfold tailWord_7348031
  simp only [CollatzResearch.WordTrace]
  refine ⟨268004708042346105628731947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178669805361564070419154631 268004708042346105628731947)
  ·
    refine ⟨402007062063519158443097921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268004708042346105628731947 402007062063519158443097921)
    ·
      refine ⟨301505296547639368832323441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402007062063519158443097921 301505296547639368832323441)
      ·
        refine ⟨226128972410729526624242581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301505296547639368832323441 226128972410729526624242581)
        ·
          refine ⟨10599795581752946560511371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226128972410729526624242581 10599795581752946560511371)
          ·
            refine ⟨15899693372629419840767057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10599795581752946560511371 15899693372629419840767057)
            ·
              refine ⟨11924770029472064880575293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15899693372629419840767057 11924770029472064880575293)
              ·
                refine ⟨4471788761052024330215735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11924770029472064880575293 4471788761052024330215735)
                ·
                  refine ⟨6707683141578036495323603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471788761052024330215735 6707683141578036495323603)
                  ·
                    refine ⟨10061524712367054742985405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6707683141578036495323603 10061524712367054742985405)
                    ·
                      refine ⟨3773071767137645528619527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10061524712367054742985405 3773071767137645528619527)
                      ·
                        rfl

theorem cell23_7348031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 3, 1, 1, 3].length) (baseStart_7348031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348031 prefixEnd_7348031 := by exact prefixLift 7348031
  have htrace : WordTrace (prefixWord ++ tailWord_7348031) baseStart_7348031 baseEnd_7348031 := by
    simpa [prefixWord, tailWord_7348031, baseEnd_7348031] using wordTrace_append hprefix tailTrace_7348031
  have hstable : (prefixWord ++ tailWord_7348031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348031).length < 2 ^ (prefixWord ++ tailWord_7348031).sum := by decide
  have hdescent : baseEnd_7348031 < baseStart_7348031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348037 : List Nat := [1, 3, 1, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_7348037 : Nat := 118140960795 + 7348037 * 2 ^ 59
def prefixEnd_7348037 : Nat := 4983230072969 + 3 ^ 40 * 7348037 * 2
def baseEnd_7348037 : Nat := 3773074848021572505144499

theorem tailTrace_7348037 : CollatzResearch.WordTrace tailWord_7348037 prefixEnd_7348037 3773074848021572505144499 := by
  unfold tailWord_7348037
  simp only [CollatzResearch.WordTrace]
  refine ⟨268004926880324368653450365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178669951253549579102300243 268004926880324368653450365)
  ·
    refine ⟨100501847580121638245043887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268004926880324368653450365 100501847580121638245043887)
    ·
      refine ⟨150752771370182457367565831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100501847580121638245043887 150752771370182457367565831)
      ·
        refine ⟨226129157055273686051348747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150752771370182457367565831 226129157055273686051348747)
        ·
          refine ⟨339193735582910529077023121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226129157055273686051348747 339193735582910529077023121)
          ·
            refine ⟨254395301687182896807767341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339193735582910529077023121 254395301687182896807767341)
            ·
              refine ⟨95398238132693586302912753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254395301687182896807767341 95398238132693586302912753)
              ·
                refine ⟨71548678599520189727184565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95398238132693586302912753 71548678599520189727184565)
                ·
                  refine ⟨6707688618705017786923553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71548678599520189727184565 6707688618705017786923553)
                  ·
                    refine ⟨5030766464028763340192665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6707688618705017786923553 5030766464028763340192665)
                    ·
                      refine ⟨3773074848021572505144499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5030766464028763340192665 3773074848021572505144499)
                      ·
                        rfl

theorem cell23_7348037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_7348037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348037 prefixEnd_7348037 := by exact prefixLift 7348037
  have htrace : WordTrace (prefixWord ++ tailWord_7348037) baseStart_7348037 baseEnd_7348037 := by
    simpa [prefixWord, tailWord_7348037, baseEnd_7348037] using wordTrace_append hprefix tailTrace_7348037
  have hstable : (prefixWord ++ tailWord_7348037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348037).length < 2 ^ (prefixWord ++ tailWord_7348037).sum := by decide
  have hdescent : baseEnd_7348037 < baseStart_7348037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348064 : List Nat := [2, 1, 1, 3, 3, 3, 3, 1, 2, 4]
def baseStart_7348064 : Nat := 118140960795 + 7348064 * 2 ^ 59
def prefixEnd_7348064 : Nat := 4983230072969 + 3 ^ 40 * 7348064 * 2
def baseEnd_7348064 : Nat := 1257696237333081299835625

theorem tailTrace_7348064 : CollatzResearch.WordTrace tailWord_7348064 prefixEnd_7348064 1257696237333081299835625 := by
  unfold tailWord_7348064
  simp only [CollatzResearch.WordTrace]
  refine ⟨134002955825613276132341623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178670607767484368176455497 134002955825613276132341623)
  ·
    refine ⟨201004433738419914198512435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134002955825613276132341623 201004433738419914198512435)
    ·
      refine ⟨301506650607629871297768653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201004433738419914198512435 301506650607629871297768653)
      ·
        refine ⟨113064993977861201736663245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301506650607629871297768653 113064993977861201736663245)
        ·
          refine ⟨42399372741697950651248717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113064993977861201736663245 42399372741697950651248717)
          ·
            refine ⟨15899764778136731494218269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42399372741697950651248717 15899764778136731494218269)
            ·
              refine ⟨5962411791801274310331851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15899764778136731494218269 5962411791801274310331851)
              ·
                refine ⟨8943617687701911465497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962411791801274310331851 8943617687701911465497777)
                ·
                  refine ⟨6707713265776433599123333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8943617687701911465497777 6707713265776433599123333)
                  ·
                    refine ⟨1257696237333081299835625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707713265776433599123333 1257696237333081299835625)
                    ·
                      rfl

theorem cell23_7348064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 3, 1, 2, 4].length) (baseStart_7348064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348064 prefixEnd_7348064 := by exact prefixLift 7348064
  have htrace : WordTrace (prefixWord ++ tailWord_7348064) baseStart_7348064 baseEnd_7348064 := by
    simpa [prefixWord, tailWord_7348064, baseEnd_7348064] using wordTrace_append hprefix tailTrace_7348064
  have hstable : (prefixWord ++ tailWord_7348064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348064).length < 2 ^ (prefixWord ++ tailWord_7348064).sum := by decide
  have hdescent : baseEnd_7348064 < baseStart_7348064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348073 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 2, 7]
def baseStart_7348073 : Nat := 118140960795 + 7348073 * 2 ^ 59
def prefixEnd_7348073 : Nat := 4983230072969 + 3 ^ 40 * 7348073 * 2
def baseEnd_7348073 : Nat := 1257697777775044788098111

theorem tailTrace_7348073 : CollatzResearch.WordTrace tailWord_7348073 prefixEnd_7348073 1257697777775044788098111 := by
  unfold tailWord_7348073
  simp only [CollatzResearch.WordTrace]
  refine ⟨268006239908193946801760873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178670826605462631201173915 268006239908193946801760873)
  ·
    refine ⟨201004679931145460101320655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268006239908193946801760873 201004679931145460101320655)
    ·
      refine ⟨301507019896718190151980983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201004679931145460101320655 301507019896718190151980983)
      ·
        refine ⟨452260529845077285227971475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301507019896718190151980983 452260529845077285227971475)
        ·
          refine ⟨678390794767615927841957213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452260529845077285227971475 678390794767615927841957213)
          ·
            refine ⟨254396548037855972940733955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678390794767615927841957213 254396548037855972940733955)
            ·
              refine ⟨381594822056783959411100933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254396548037855972940733955 381594822056783959411100933)
              ·
                refine ⟨71549029135646992389581425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381594822056783959411100933 71549029135646992389581425)
                ·
                  refine ⟨53661771851735244292186069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71549029135646992389581425 53661771851735244292186069)
                  ·
                    refine ⟨1257697777775044788098111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53661771851735244292186069 1257697777775044788098111)
                    ·
                      rfl

theorem cell23_7348073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 7].length) (baseStart_7348073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348073 prefixEnd_7348073 := by exact prefixLift 7348073
  have htrace : WordTrace (prefixWord ++ tailWord_7348073) baseStart_7348073 baseEnd_7348073 := by
    simpa [prefixWord, tailWord_7348073, baseEnd_7348073] using wordTrace_append hprefix tailTrace_7348073
  have hstable : (prefixWord ++ tailWord_7348073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348073).length < 2 ^ (prefixWord ++ tailWord_7348073).sum := by decide
  have hdescent : baseEnd_7348073 < baseStart_7348073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348123 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12]
def baseStart_7348123 : Nat := 118140960795 + 7348123 * 2 ^ 59
def prefixEnd_7348123 : Nat := 4983230072969 + 3 ^ 40 * 7348123 * 2
def baseEnd_7348123 : Nat := 3773119007357859168669103

theorem tailTrace_7348123 : CollatzResearch.WordTrace tailWord_7348123 prefixEnd_7348123 3773119007357859168669103 := by
  unfold tailWord_7348123
  simp only [CollatzResearch.WordTrace]
  refine ⟨268008063558012805341081023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178672042372008536894054015 268008063558012805341081023)
  ·
    refine ⟨402012095337019208011621535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268008063558012805341081023 402012095337019208011621535)
    ·
      refine ⟨603018143005528812017432303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402012095337019208011621535 603018143005528812017432303)
      ·
        refine ⟨904527214508293218026148455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603018143005528812017432303 904527214508293218026148455)
        ·
          refine ⟨1356790821762439827039222683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904527214508293218026148455 1356790821762439827039222683)
          ·
            refine ⟨2035186232643659740558834025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356790821762439827039222683 2035186232643659740558834025)
            ·
              refine ⟨1526389674482744805419125519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035186232643659740558834025 1526389674482744805419125519)
              ·
                refine ⟨2289584511724117208128688279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526389674482744805419125519 2289584511724117208128688279)
                ·
                  refine ⟨3434376767586175812193032419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289584511724117208128688279 3434376767586175812193032419)
                  ·
                    refine ⟨5151565151379263718289548629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3434376767586175812193032419 5151565151379263718289548629)
                    ·
                      refine ⟨3773119007357859168669103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 12 5151565151379263718289548629 3773119007357859168669103)
                      ·
                        rfl

theorem cell23_7348123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 12].length) (baseStart_7348123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348123 prefixEnd_7348123 := by exact prefixLift 7348123
  have htrace : WordTrace (prefixWord ++ tailWord_7348123) baseStart_7348123 baseEnd_7348123 := by
    simpa [prefixWord, tailWord_7348123, baseEnd_7348123] using wordTrace_append hprefix tailTrace_7348123
  have hstable : (prefixWord ++ tailWord_7348123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348123).length < 2 ^ (prefixWord ++ tailWord_7348123).sum := by decide
  have hdescent : baseEnd_7348123 < baseStart_7348123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348261 : List Nat := [1, 3, 1, 2, 2, 3, 3, 3, 1, 4]
def baseStart_7348261 : Nat := 118140960795 + 7348261 * 2 ^ 59
def prefixEnd_7348261 : Nat := 4983230072969 + 3 ^ 40 * 7348261 * 2
def baseEnd_7348261 : Nat := 1257729955896059876247823

theorem tailTrace_7348261 : CollatzResearch.WordTrace tailWord_7348261 prefixEnd_7348261 1257729955896059876247823 := by
  unfold tailWord_7348261
  simp only [CollatzResearch.WordTrace]
  refine ⟨268013096831512854909604637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178675397887675236606403091 268013096831512854909604637)
  ·
    refine ⟨100504911311817320591101739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268013096831512854909604637 100504911311817320591101739)
    ·
      refine ⟨150757366967725980886652609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100504911311817320591101739 150757366967725980886652609)
      ·
        refine ⟨113068025225794485664989457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150757366967725980886652609 113068025225794485664989457)
        ·
          refine ⟨84801018919345864248742093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113068025225794485664989457 84801018919345864248742093)
          ·
            refine ⟨31800382094754699093278285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84801018919345864248742093 31800382094754699093278285)
            ·
              refine ⟨11925143285533012159979357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31800382094754699093278285 11925143285533012159979357)
              ·
                refine ⟨4471928732074879559992259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11925143285533012159979357 4471928732074879559992259)
                ·
                  refine ⟨6707893098112319339988389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471928732074879559992259 6707893098112319339988389)
                  ·
                    refine ⟨1257729955896059876247823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707893098112319339988389 1257729955896059876247823)
                    ·
                      rfl

theorem cell23_7348261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_7348261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348261 prefixEnd_7348261 := by exact prefixLift 7348261
  have htrace : WordTrace (prefixWord ++ tailWord_7348261) baseStart_7348261 baseEnd_7348261 := by
    simpa [prefixWord, tailWord_7348261, baseEnd_7348261] using wordTrace_append hprefix tailTrace_7348261
  have hstable : (prefixWord ++ tailWord_7348261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348261).length < 2 ^ (prefixWord ++ tailWord_7348261).sum := by decide
  have hdescent : baseEnd_7348261 < baseStart_7348261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348301 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7348301 : Nat := 118140960795 + 7348301 * 2 ^ 59
def prefixEnd_7348301 : Nat := 4983230072969 + 3 ^ 40 * 7348301 * 2
def baseEnd_7348301 : Nat := 3773210406914359472243285

theorem tailTrace_7348301 : CollatzResearch.WordTrace tailWord_7348301 prefixEnd_7348301 3773210406914359472243285 := by
  unfold tailWord_7348301
  simp only [CollatzResearch.WordTrace]
  refine ⟨268014555751367941741060757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178676370500911961160707171 268014555751367941741060757)
  ·
    refine ⟨12563182300845372269112223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 268014555751367941741060757 12563182300845372269112223)
    ·
      refine ⟨18844773451268058403668335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12563182300845372269112223 18844773451268058403668335)
      ·
        refine ⟨28267160176902087605502503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18844773451268058403668335 28267160176902087605502503)
        ·
          refine ⟨42400740265353131408253755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28267160176902087605502503 42400740265353131408253755)
          ·
            refine ⟨63601110398029697112380633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42400740265353131408253755 63601110398029697112380633)
            ·
              refine ⟨47700832798522272834285475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63601110398029697112380633 47700832798522272834285475)
              ·
                refine ⟨71551249197783409251428213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47700832798522272834285475 71551249197783409251428213)
                ·
                  refine ⟨6707929612292194617321395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71551249197783409251428213 6707929612292194617321395)
                  ·
                    refine ⟨10061894418438291925982093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6707929612292194617321395 10061894418438291925982093)
                    ·
                      refine ⟨3773210406914359472243285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10061894418438291925982093 3773210406914359472243285)
                      ·
                        rfl

theorem cell23_7348301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7348301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348301 prefixEnd_7348301 := by exact prefixLift 7348301
  have htrace : WordTrace (prefixWord ++ tailWord_7348301) baseStart_7348301 baseEnd_7348301 := by
    simpa [prefixWord, tailWord_7348301, baseEnd_7348301] using wordTrace_append hprefix tailTrace_7348301
  have hstable : (prefixWord ++ tailWord_7348301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348301).length < 2 ^ (prefixWord ++ tailWord_7348301).sum := by decide
  have hdescent : baseEnd_7348301 < baseStart_7348301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348324 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 1, 1, 4]
def baseStart_7348324 : Nat := 118140960795 + 7348324 * 2 ^ 59
def prefixEnd_7348324 : Nat := 4983230072969 + 3 ^ 40 * 7348324 * 2
def baseEnd_7348324 : Nat := 3773222216969412882255679

theorem tailTrace_7348324 : CollatzResearch.WordTrace tailWord_7348324 prefixEnd_7348324 3773222216969412882255679 := by
  unfold tailWord_7348324
  simp only [CollatzResearch.WordTrace]
  refine ⟨134007697315142308334574013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178676929753523077779432017 134007697315142308334574013)
  ·
    refine ⟨50252886493178365625465255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134007697315142308334574013 50252886493178365625465255)
    ·
      refine ⟨75379329739767548438197883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50252886493178365625465255 75379329739767548438197883)
      ·
        refine ⟨113068994609651322657296825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75379329739767548438197883 113068994609651322657296825)
        ·
          refine ⟨84801745957238491992972619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113068994609651322657296825 84801745957238491992972619)
          ·
            refine ⟨127202618935857737989458929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84801745957238491992972619 127202618935857737989458929)
            ·
              refine ⟨95401964201893303492094197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127202618935857737989458929 95401964201893303492094197)
              ·
                refine ⟨8943934143927497202383831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95401964201893303492094197 8943934143927497202383831)
                ·
                  refine ⟨13415901215891245803575747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8943934143927497202383831 13415901215891245803575747)
                  ·
                    refine ⟨20123851823836868705363621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13415901215891245803575747 20123851823836868705363621)
                    ·
                      refine ⟨3773222216969412882255679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20123851823836868705363621 3773222216969412882255679)
                      ·
                        rfl

theorem cell23_7348324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_7348324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348324 prefixEnd_7348324 := by exact prefixLift 7348324
  have htrace : WordTrace (prefixWord ++ tailWord_7348324) baseStart_7348324 baseEnd_7348324 := by
    simpa [prefixWord, tailWord_7348324, baseEnd_7348324] using wordTrace_append hprefix tailTrace_7348324
  have hstable : (prefixWord ++ tailWord_7348324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348324).length < 2 ^ (prefixWord ++ tailWord_7348324).sum := by decide
  have hdescent : baseEnd_7348324 < baseStart_7348324 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348335 : List Nat := [1, 1, 2, 1, 3, 6, 2, 2, 1, 1, 3]
def baseStart_7348335 : Nat := 118140960795 + 7348335 * 2 ^ 59
def prefixEnd_7348335 : Nat := 4983230072969 + 3 ^ 40 * 7348335 * 2
def baseEnd_7348335 : Nat := 3773227865256612339218129

theorem tailTrace_7348335 : CollatzResearch.WordTrace tailWord_7348335 prefixEnd_7348335 3773227865256612339218129 := by
  unfold tailWord_7348335
  simp only [CollatzResearch.WordTrace]
  refine ⟨268015795833244765547798459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178677197222163177031865639 268015795833244765547798459)
  ·
    refine ⟨402023693749867148321697689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268015795833244765547798459 402023693749867148321697689)
    ·
      refine ⟨301517770312400361241273267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402023693749867148321697689 301517770312400361241273267)
      ·
        refine ⟨452276655468600541861909901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301517770312400361241273267 452276655468600541861909901)
        ·
          refine ⟨169603745800725203198216213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452276655468600541861909901 169603745800725203198216213)
          ·
            refine ⟨7950175584408993899916385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 169603745800725203198216213 7950175584408993899916385)
            ·
              refine ⟨5962631688306745424937289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7950175584408993899916385 5962631688306745424937289)
              ·
                refine ⟨4471973766230059068702967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962631688306745424937289 4471973766230059068702967)
                ·
                  refine ⟨6707960649345088603054451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471973766230059068702967 6707960649345088603054451)
                  ·
                    refine ⟨10061940974017632904581677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6707960649345088603054451 10061940974017632904581677)
                    ·
                      refine ⟨3773227865256612339218129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10061940974017632904581677 3773227865256612339218129)
                      ·
                        rfl

theorem cell23_7348335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 2, 1, 1, 3].length) (baseStart_7348335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348335 prefixEnd_7348335 := by exact prefixLift 7348335
  have htrace : WordTrace (prefixWord ++ tailWord_7348335) baseStart_7348335 baseEnd_7348335 := by
    simpa [prefixWord, tailWord_7348335, baseEnd_7348335] using wordTrace_append hprefix tailTrace_7348335
  have hstable : (prefixWord ++ tailWord_7348335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348335).length < 2 ^ (prefixWord ++ tailWord_7348335).sum := by decide
  have hdescent : baseEnd_7348335 < baseStart_7348335 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348337 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 4]
def baseStart_7348337 : Nat := 118140960795 + 7348337 * 2 ^ 59
def prefixEnd_7348337 : Nat := 4983230072969 + 3 ^ 40 * 7348337 * 2
def baseEnd_7348337 : Nat := 3773228892217921331393119

theorem tailTrace_7348337 : CollatzResearch.WordTrace tailWord_7348337 prefixEnd_7348337 3773228892217921331393119 := by
  unfold tailWord_7348337
  simp only [CollatzResearch.WordTrace]
  refine ⟨268015868779237519889371265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178677245852825013259580843 268015868779237519889371265)
  ·
    refine ⟨201011901584428139917028449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268015868779237519889371265 201011901584428139917028449)
    ·
      refine ⟨150758926188321104937771337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201011901584428139917028449 150758926188321104937771337)
      ·
        refine ⟨113069194641240828703328503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150758926188321104937771337 113069194641240828703328503)
        ·
          refine ⟨169603791961861243054992755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113069194641240828703328503 169603791961861243054992755)
          ·
            refine ⟨254405687942791864582489133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169603791961861243054992755 254405687942791864582489133)
            ·
              refine ⟨95402132978546949218433425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254405687942791864582489133 95402132978546949218433425)
              ·
                refine ⟨71551599733910211913825069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95402132978546949218433425 71551599733910211913825069)
                ·
                  refine ⟨26831849900216329467684401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71551599733910211913825069 26831849900216329467684401)
                  ·
                    refine ⟨20123887425162247100763301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26831849900216329467684401 20123887425162247100763301)
                    ·
                      refine ⟨3773228892217921331393119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20123887425162247100763301 3773228892217921331393119)
                      ·
                        rfl

theorem cell23_7348337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_7348337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348337 prefixEnd_7348337 := by exact prefixLift 7348337
  have htrace : WordTrace (prefixWord ++ tailWord_7348337) baseStart_7348337 baseEnd_7348337 := by
    simpa [prefixWord, tailWord_7348337, baseEnd_7348337] using wordTrace_append hprefix tailTrace_7348337
  have hstable : (prefixWord ++ tailWord_7348337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348337).length < 2 ^ (prefixWord ++ tailWord_7348337).sum := by decide
  have hdescent : baseEnd_7348337 < baseStart_7348337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348372 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 1, 5]
def baseStart_7348372 : Nat := 118140960795 + 7348372 * 2 ^ 59
def prefixEnd_7348372 : Nat := 4983230072969 + 3 ^ 40 * 7348372 * 2
def baseEnd_7348372 : Nat := 1257748954680276231485153

theorem tailTrace_7348372 : CollatzResearch.WordTrace tailWord_7348372 prefixEnd_7348372 1257748954680276231485153 := by
  unfold tailWord_7348372
  simp only [CollatzResearch.WordTrace]
  refine ⟨134008572667055360433447685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178678096889407147244596913 134008572667055360433447685)
  ·
    refine ⟨25126607375072880081271441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134008572667055360433447685 25126607375072880081271441)
    ·
      refine ⟨18844955531304660060953581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25126607375072880081271441 18844955531304660060953581)
      ·
        refine ⟨7066858324239247522857593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18844955531304660060953581 7066858324239247522857593)
        ·
          refine ⟨5300143743179435642143195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7066858324239247522857593 5300143743179435642143195)
          ·
            refine ⟨7950215614769153463214793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300143743179435642143195 7950215614769153463214793)
            ·
              refine ⟨5962661711076865097411095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7950215614769153463214793 5962661711076865097411095)
              ·
                refine ⟨8943992566615297646116643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962661711076865097411095 8943992566615297646116643)
                ·
                  refine ⟨13415988849922946469174965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8943992566615297646116643 13415988849922946469174965)
                  ·
                    refine ⟨1257748954680276231485153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13415988849922946469174965 1257748954680276231485153)
                    ·
                      rfl

theorem cell23_7348372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_7348372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348372 prefixEnd_7348372 := by exact prefixLift 7348372
  have htrace : WordTrace (prefixWord ++ tailWord_7348372) baseStart_7348372 baseEnd_7348372 := by
    simpa [prefixWord, tailWord_7348372, baseEnd_7348372] using wordTrace_append hprefix tailTrace_7348372
  have hstable : (prefixWord ++ tailWord_7348372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348372).length < 2 ^ (prefixWord ++ tailWord_7348372).sum := by decide
  have hdescent : baseEnd_7348372 < baseStart_7348372 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348375 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 1, 1, 4]
def baseStart_7348375 : Nat := 118140960795 + 7348375 * 2 ^ 59
def prefixEnd_7348375 : Nat := 4983230072969 + 3 ^ 40 * 7348375 * 2
def baseEnd_7348375 : Nat := 3773248404482792182717945

theorem tailTrace_7348375 : CollatzResearch.WordTrace tailWord_7348375 prefixEnd_7348375 3773248404482792182717945 := by
  unfold tailWord_7348375
  simp only [CollatzResearch.WordTrace]
  refine ⟨268017254753099852379254579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178678169835399901586169719 268017254753099852379254579)
  ·
    refine ⟨402025882129649778568881869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268017254753099852379254579 402025882129649778568881869)
    ·
      refine ⟨150759705798618666963330701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402025882129649778568881869 150759705798618666963330701)
      ·
        refine ⟨56534889674482000111249013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150759705798618666963330701 56534889674482000111249013)
        ·
          refine ⟨5300145906982687510429595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56534889674482000111249013 5300145906982687510429595)
          ·
            refine ⟨7950218860474031265644393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300145906982687510429595 7950218860474031265644393)
            ·
              refine ⟨5962664145355523449233295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7950218860474031265644393 5962664145355523449233295)
              ·
                refine ⟨8943996218033285173849943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962664145355523449233295 8943996218033285173849943)
                ·
                  refine ⟨13415994327049927760774915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8943996218033285173849943 13415994327049927760774915)
                  ·
                    refine ⟨20123991490574891641162373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13415994327049927760774915 20123991490574891641162373)
                    ·
                      refine ⟨3773248404482792182717945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20123991490574891641162373 3773248404482792182717945)
                      ·
                        rfl

theorem cell23_7348375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_7348375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348375 prefixEnd_7348375 := by exact prefixLift 7348375
  have htrace : WordTrace (prefixWord ++ tailWord_7348375) baseStart_7348375 baseEnd_7348375 := by
    simpa [prefixWord, tailWord_7348375, baseEnd_7348375] using wordTrace_append hprefix tailTrace_7348375
  have hstable : (prefixWord ++ tailWord_7348375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348375).length < 2 ^ (prefixWord ++ tailWord_7348375).sum := by decide
  have hdescent : baseEnd_7348375 < baseStart_7348375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348378 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3]
def baseStart_7348378 : Nat := 118140960795 + 7348378 * 2 ^ 59
def prefixEnd_7348378 : Nat := 4983230072969 + 3 ^ 40 * 7348378 * 2
def baseEnd_7348378 : Nat := 3773249944924755670980431

theorem tailTrace_7348378 : CollatzResearch.WordTrace tailWord_7348378 prefixEnd_7348378 3773249944924755670980431 := by
  unfold tailWord_7348378
  simp only [CollatzResearch.WordTrace]
  refine ⟨67004341043022245972903447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178678242781392655927742525 67004341043022245972903447)
  ·
    refine ⟨100506511564533368959355171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67004341043022245972903447 100506511564533368959355171)
    ·
      refine ⟨150759767346800053439032757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100506511564533368959355171 150759767346800053439032757)
      ·
        refine ⟨14133728188762505009909321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150759767346800053439032757 14133728188762505009909321)
        ·
          refine ⟨10600296141571878757431991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14133728188762505009909321 10600296141571878757431991)
          ·
            refine ⟨15900444212357818136147987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600296141571878757431991 15900444212357818136147987)
            ·
              refine ⟨23850666318536727204221981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15900444212357818136147987 23850666318536727204221981)
              ·
                refine ⟨8943999869451272701583243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23850666318536727204221981 8943999869451272701583243)
                ·
                  refine ⟨13415999804176909052374865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8943999869451272701583243 13415999804176909052374865)
                  ·
                    refine ⟨10061999853132681789281149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13415999804176909052374865 10061999853132681789281149)
                    ·
                      refine ⟨3773249944924755670980431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10061999853132681789281149 3773249944924755670980431)
                      ·
                        rfl

theorem cell23_7348378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_7348378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348378 prefixEnd_7348378 := by exact prefixLift 7348378
  have htrace : WordTrace (prefixWord ++ tailWord_7348378) baseStart_7348378 baseEnd_7348378 := by
    simpa [prefixWord, tailWord_7348378, baseEnd_7348378] using wordTrace_append hprefix tailTrace_7348378
  have hstable : (prefixWord ++ tailWord_7348378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348378).length < 2 ^ (prefixWord ++ tailWord_7348378).sum := by decide
  have hdescent : baseEnd_7348378 < baseStart_7348378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348405 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7348405 : Nat := 118140960795 + 7348405 * 2 ^ 59
def prefixEnd_7348405 : Nat := 4983230072969 + 3 ^ 40 * 7348405 * 2
def baseEnd_7348405 : Nat := 3773263808902427065342807

theorem tailTrace_7348405 : CollatzResearch.WordTrace tailWord_7348405 prefixEnd_7348405 3773263808902427065342807 := by
  unfold tailWord_7348405
  simp only [CollatzResearch.WordTrace]
  refine ⟨268018348942991167502846669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178678899295327445001897779 268018348942991167502846669)
  ·
    refine ⟨100506880853621687813567501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268018348942991167502846669 100506880853621687813567501)
    ·
      refine ⟨37690080320108132930087813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100506880853621687813567501 37690080320108132930087813)
      ·
        refine ⟨7066890060020274924391465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37690080320108132930087813 7066890060020274924391465)
        ·
          refine ⟨5300167545015206193293599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7066890060020274924391465 5300167545015206193293599)
          ·
            refine ⟨7950251317522809289940399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5300167545015206193293599 7950251317522809289940399)
            ·
              refine ⟨11925376976284213934910599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950251317522809289940399 11925376976284213934910599)
              ·
                refine ⟨17888065464426320902365899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925376976284213934910599 17888065464426320902365899)
                ·
                  refine ⟨26832098196639481353548849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17888065464426320902365899 26832098196639481353548849)
                  ·
                    refine ⟨20124073647479611015161637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26832098196639481353548849 20124073647479611015161637)
                    ·
                      refine ⟨3773263808902427065342807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20124073647479611015161637 3773263808902427065342807)
                      ·
                        rfl

theorem cell23_7348405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7348405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348405 prefixEnd_7348405 := by exact prefixLift 7348405
  have htrace : WordTrace (prefixWord ++ tailWord_7348405) baseStart_7348405 baseEnd_7348405 := by
    simpa [prefixWord, tailWord_7348405, baseEnd_7348405] using wordTrace_append hprefix tailTrace_7348405
  have hstable : (prefixWord ++ tailWord_7348405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348405).length < 2 ^ (prefixWord ++ tailWord_7348405).sum := by decide
  have hdescent : baseEnd_7348405 < baseStart_7348405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348408 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3]
def baseStart_7348408 : Nat := 118140960795 + 7348408 * 2 ^ 59
def prefixEnd_7348408 : Nat := 4983230072969 + 3 ^ 40 * 7348408 * 2
def baseEnd_7348408 : Nat := 3773265349344390553605293

theorem tailTrace_7348408 : CollatzResearch.WordTrace tailWord_7348408 prefixEnd_7348408 3773265349344390553605293 := by
  unfold tailWord_7348408
  simp only [CollatzResearch.WordTrace]
  refine ⟨134009229180990149507602939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178678972241320199343470585 134009229180990149507602939)
  ·
    refine ⟨201013843771485224261404409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134009229180990149507602939 201013843771485224261404409)
    ·
      refine ⟨150760382828613918196053307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201013843771485224261404409 150760382828613918196053307)
      ·
        refine ⟨226140574242920877294079961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150760382828613918196053307 226140574242920877294079961)
        ·
          refine ⟨169605430682190657970559971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226140574242920877294079961 169605430682190657970559971)
          ·
            refine ⟨254408146023285986955839957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169605430682190657970559971 254408146023285986955839957)
            ·
              refine ⟨5962690922420765319277499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 254408146023285986955839957 5962690922420765319277499)
              ·
                refine ⟨8944036383631147978916249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962690922420765319277499 8944036383631147978916249)
                ·
                  refine ⟨6708027287723360984187187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944036383631147978916249 6708027287723360984187187)
                  ·
                    refine ⟨10062040931585041476280781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6708027287723360984187187 10062040931585041476280781)
                    ·
                      refine ⟨3773265349344390553605293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062040931585041476280781 3773265349344390553605293)
                      ·
                        rfl

theorem cell23_7348408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 2, 1, 3].length) (baseStart_7348408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348408 prefixEnd_7348408 := by exact prefixLift 7348408
  have htrace : WordTrace (prefixWord ++ tailWord_7348408) baseStart_7348408 baseEnd_7348408 := by
    simpa [prefixWord, tailWord_7348408, baseEnd_7348408] using wordTrace_append hprefix tailTrace_7348408
  have hstable : (prefixWord ++ tailWord_7348408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348408).length < 2 ^ (prefixWord ++ tailWord_7348408).sum := by decide
  have hdescent : baseEnd_7348408 < baseStart_7348408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348431 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 6, 2, 2]
def baseStart_7348431 : Nat := 118140960795 + 7348431 * 2 ^ 59
def prefixEnd_7348431 : Nat := 4983230072969 + 3 ^ 40 * 7348431 * 2
def baseEnd_7348431 : Nat := 3773277159399443963617687

theorem tailTrace_7348431 : CollatzResearch.WordTrace tailWord_7348431 prefixEnd_7348431 3773277159399443963617687 := by
  unfold tailWord_7348431
  simp only [CollatzResearch.WordTrace]
  refine ⟨268019297240896973943293147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178679531493931315962195431 268019297240896973943293147)
  ·
    refine ⟨402028945861345460914939721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268019297240896973943293147 402028945861345460914939721)
    ·
      refine ⟨301521709396009095686204791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402028945861345460914939721 301521709396009095686204791)
      ·
        refine ⟨452282564094013643529307187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301521709396009095686204791 452282564094013643529307187)
        ·
          refine ⟨678423846141020465293960781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452282564094013643529307187 678423846141020465293960781)
          ·
            refine ⟨254408942302882674485235293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 678423846141020465293960781 254408942302882674485235293)
            ·
              refine ⟨95403353363581002931963235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254408942302882674485235293 95403353363581002931963235)
              ·
                refine ⟨143105030045371504397944853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95403353363581002931963235 143105030045371504397944853)
                ·
                  refine ⟨6708048283376789268653665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143105030045371504397944853 6708048283376789268653665)
                  ·
                    refine ⟨5031036212532591951490249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708048283376789268653665 5031036212532591951490249)
                    ·
                      refine ⟨3773277159399443963617687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031036212532591951490249 3773277159399443963617687)
                      ·
                        rfl

theorem cell23_7348431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 6, 2, 2].length) (baseStart_7348431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348431 prefixEnd_7348431 := by exact prefixLift 7348431
  have htrace : WordTrace (prefixWord ++ tailWord_7348431) baseStart_7348431 baseEnd_7348431 := by
    simpa [prefixWord, tailWord_7348431, baseEnd_7348431] using wordTrace_append hprefix tailTrace_7348431
  have hstable : (prefixWord ++ tailWord_7348431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348431).length < 2 ^ (prefixWord ++ tailWord_7348431).sum := by decide
  have hdescent : baseEnd_7348431 < baseStart_7348431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348434 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7348434 : Nat := 118140960795 + 7348434 * 2 ^ 59
def prefixEnd_7348434 : Nat := 4983230072969 + 3 ^ 40 * 7348434 * 2
def baseEnd_7348434 : Nat := 3773278699841407451880173

theorem tailTrace_7348434 : CollatzResearch.WordTrace tailWord_7348434 prefixEnd_7348434 3773278699841407451880173 := by
  unfold tailWord_7348434
  simp only [CollatzResearch.WordTrace]
  refine ⟨67004851664971526363913089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178679604439924070303768237 67004851664971526363913089)
  ·
    refine ⟨50253638748728644772934817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67004851664971526363913089 50253638748728644772934817)
    ·
      refine ⟨37690229061546483579701113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50253638748728644772934817 37690229061546483579701113)
      ·
        refine ⟨28267671796159862684775835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37690229061546483579701113 28267671796159862684775835)
        ·
          refine ⟨42401507694239794027163753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28267671796159862684775835 42401507694239794027163753)
          ·
            refine ⟨31801130770679845520372815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42401507694239794027163753 31801130770679845520372815)
            ·
              refine ⟨47701696156019768280559223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31801130770679845520372815 47701696156019768280559223)
              ·
                refine ⟨71552544234029652420838835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47701696156019768280559223 71552544234029652420838835)
                ·
                  refine ⟨107328816351044478631258253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71552544234029652420838835 107328816351044478631258253)
                  ·
                    refine ⟨40248306131641679486721845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107328816351044478631258253 40248306131641679486721845)
                    ·
                      refine ⟨3773278699841407451880173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40248306131641679486721845 3773278699841407451880173)
                      ·
                        rfl

theorem cell23_7348434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7348434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348434 prefixEnd_7348434 := by exact prefixLift 7348434
  have htrace : WordTrace (prefixWord ++ tailWord_7348434) baseStart_7348434 baseEnd_7348434 := by
    simpa [prefixWord, tailWord_7348434, baseEnd_7348434] using wordTrace_append hprefix tailTrace_7348434
  have hstable : (prefixWord ++ tailWord_7348434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348434).length < 2 ^ (prefixWord ++ tailWord_7348434).sum := by decide
  have hdescent : baseEnd_7348434 < baseStart_7348434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348447 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7348447 : Nat := 118140960795 + 7348447 * 2 ^ 59
def prefixEnd_7348447 : Nat := 4983230072969 + 3 ^ 40 * 7348447 * 2
def baseEnd_7348447 : Nat := 3773285375089915901017613

theorem tailTrace_7348447 : CollatzResearch.WordTrace tailWord_7348447 prefixEnd_7348447 3773285375089915901017613 := by
  unfold tailWord_7348447
  simp only [CollatzResearch.WordTrace]
  refine ⟨268019880808839008675875595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178679920539226005783917063 268019880808839008675875595)
  ·
    refine ⟨402029821213258513013813393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268019880808839008675875595 402029821213258513013813393)
    ·
      refine ⟨301522365909943884760360045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402029821213258513013813393 301522365909943884760360045)
      ·
        refine ⟨113070887216228956785135017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301522365909943884760360045 113070887216228956785135017)
        ·
          refine ⟨84803165412171717588851263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113070887216228956785135017 84803165412171717588851263)
          ·
            refine ⟨127204748118257576383276895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84803165412171717588851263 127204748118257576383276895)
            ·
              refine ⟨190807122177386364574915343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127204748118257576383276895 190807122177386364574915343)
              ·
                refine ⟨286210683266079546862373015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190807122177386364574915343 286210683266079546862373015)
                ·
                  refine ⟨429316024899119320293559523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286210683266079546862373015 429316024899119320293559523)
                  ·
                    refine ⟨643974037348678980440339285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 429316024899119320293559523 643974037348678980440339285)
                    ·
                      refine ⟨3773285375089915901017613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 643974037348678980440339285 3773285375089915901017613)
                      ·
                        rfl

theorem cell23_7348447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7348447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348447 prefixEnd_7348447 := by exact prefixLift 7348447
  have htrace : WordTrace (prefixWord ++ tailWord_7348447) baseStart_7348447 baseEnd_7348447 := by
    simpa [prefixWord, tailWord_7348447, baseEnd_7348447] using wordTrace_append hprefix tailTrace_7348447
  have hstable : (prefixWord ++ tailWord_7348447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348447).length < 2 ^ (prefixWord ++ tailWord_7348447).sum := by decide
  have hdescent : baseEnd_7348447 < baseStart_7348447 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348448 : List Nat := [2, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2]
def baseStart_7348448 : Nat := 118140960795 + 7348448 * 2 ^ 59
def prefixEnd_7348448 : Nat := 4983230072969 + 3 ^ 40 * 7348448 * 2
def baseEnd_7348448 : Nat := 3773285888570570397105109

theorem tailTrace_7348448 : CollatzResearch.WordTrace tailWord_7348448 prefixEnd_7348448 3773285888570570397105109 := by
  unfold tailWord_7348448
  simp only [CollatzResearch.WordTrace]
  refine ⟨134009958640917692923330999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178679944854556923897774665 134009958640917692923330999)
  ·
    refine ⟨201014937961376539384996499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134009958640917692923330999 201014937961376539384996499)
    ·
      refine ⟨301522406942064809077494749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201014937961376539384996499 301522406942064809077494749)
      ·
        refine ⟨113070902603274303404060531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301522406942064809077494749 113070902603274303404060531)
        ·
          refine ⟨169606353904911455106090797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113070902603274303404060531 169606353904911455106090797)
          ·
            refine ⟨63602382714341795664784049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169606353904911455106090797 63602382714341795664784049)
            ·
              refine ⟨47701787035756346748588037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63602382714341795664784049 47701787035756346748588037)
              ·
                refine ⟨8944085069204315015360257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47701787035756346748588037 8944085069204315015360257)
                ·
                  refine ⟨6708063801903236261520193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944085069204315015360257 6708063801903236261520193)
                  ·
                    refine ⟨5031047851427427196140145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708063801903236261520193 5031047851427427196140145)
                    ·
                      refine ⟨3773285888570570397105109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031047851427427196140145 3773285888570570397105109)
                      ·
                        rfl

theorem cell23_7348448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 4, 2, 2, 2].length) (baseStart_7348448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348448 prefixEnd_7348448 := by exact prefixLift 7348448
  have htrace : WordTrace (prefixWord ++ tailWord_7348448) baseStart_7348448 baseEnd_7348448 := by
    simpa [prefixWord, tailWord_7348448, baseEnd_7348448] using wordTrace_append hprefix tailTrace_7348448
  have hstable : (prefixWord ++ tailWord_7348448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348448).length < 2 ^ (prefixWord ++ tailWord_7348448).sum := by decide
  have hdescent : baseEnd_7348448 < baseStart_7348448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348464 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_7348464 : Nat := 118140960795 + 7348464 * 2 ^ 59
def prefixEnd_7348464 : Nat := 4983230072969 + 3 ^ 40 * 7348464 * 2
def baseEnd_7348464 : Nat := 3773294104261042334505035

theorem tailTrace_7348464 : CollatzResearch.WordTrace tailWord_7348464 prefixEnd_7348464 3773294104261042334505035 := by
  unfold tailWord_7348464
  simp only [CollatzResearch.WordTrace]
  refine ⟨134010250424888710289622223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178680333899851613719496297 134010250424888710289622223)
  ·
    refine ⟨201015375637333065434433335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134010250424888710289622223 201015375637333065434433335)
    ·
      refine ⟨301523063455999598151650003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201015375637333065434433335 301523063455999598151650003)
      ·
        refine ⟨452284595183999397227475005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301523063455999598151650003 452284595183999397227475005)
        ·
          refine ⟨169606723193999773960303127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452284595183999397227475005 169606723193999773960303127)
          ·
            refine ⟨254410084790999660940454691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169606723193999773960303127 254410084790999660940454691)
            ·
              refine ⟨381615127186499491410682037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254410084790999660940454691 381615127186499491410682037)
              ·
                refine ⟨35776418173734327319751441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381615127186499491410682037 35776418173734327319751441)
                ·
                  refine ⟨26832313630300745489813581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35776418173734327319751441 26832313630300745489813581)
                  ·
                    refine ⟨10062117611362779558680093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26832313630300745489813581 10062117611362779558680093)
                    ·
                      refine ⟨3773294104261042334505035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062117611362779558680093 3773294104261042334505035)
                      ·
                        rfl

theorem cell23_7348464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_7348464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348464 prefixEnd_7348464 := by exact prefixLift 7348464
  have htrace : WordTrace (prefixWord ++ tailWord_7348464) baseStart_7348464 baseEnd_7348464 := by
    simpa [prefixWord, tailWord_7348464, baseEnd_7348464] using wordTrace_append hprefix tailTrace_7348464
  have hstable : (prefixWord ++ tailWord_7348464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348464).length < 2 ^ (prefixWord ++ tailWord_7348464).sum := by decide
  have hdescent : baseEnd_7348464 < baseStart_7348464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348465 : List Nat := [1, 2, 2, 2, 2, 1, 6, 1, 2, 2, 2]
def baseStart_7348465 : Nat := 118140960795 + 7348465 * 2 ^ 59
def prefixEnd_7348465 : Nat := 4983230072969 + 3 ^ 40 * 7348465 * 2
def baseEnd_7348465 : Nat := 3773294617741696830592531

theorem tailTrace_7348465 : CollatzResearch.WordTrace tailWord_7348465 prefixEnd_7348465 3773294617741696830592531 := by
  unfold tailWord_7348465
  simp only [CollatzResearch.WordTrace]
  refine ⟨268020537322773797750030849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178680358215182531833353899 268020537322773797750030849)
  ·
    refine ⟨201015402992080348312523137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268020537322773797750030849 201015402992080348312523137)
    ·
      refine ⟨150761552244060261234392353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201015402992080348312523137 150761552244060261234392353)
      ·
        refine ⟨113071164183045195925794265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150761552244060261234392353 113071164183045195925794265)
        ·
          refine ⟨84803373137283896944345699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113071164183045195925794265 84803373137283896944345699)
          ·
            refine ⟨127205059705925845416518549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84803373137283896944345699 127205059705925845416518549)
            ·
              refine ⟨5962737173715274003899307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127205059705925845416518549 5962737173715274003899307)
              ·
                refine ⟨8944105760572911005848961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962737173715274003899307 8944105760572911005848961)
                ·
                  refine ⟨6708079320429683254386721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944105760572911005848961 6708079320429683254386721)
                  ·
                    refine ⟨5031059490322262440790041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708079320429683254386721 5031059490322262440790041)
                    ·
                      refine ⟨3773294617741696830592531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031059490322262440790041 3773294617741696830592531)
                      ·
                        rfl

theorem cell23_7348465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 6, 1, 2, 2, 2].length) (baseStart_7348465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348465 prefixEnd_7348465 := by exact prefixLift 7348465
  have htrace : WordTrace (prefixWord ++ tailWord_7348465) baseStart_7348465 baseEnd_7348465 := by
    simpa [prefixWord, tailWord_7348465, baseEnd_7348465] using wordTrace_append hprefix tailTrace_7348465
  have hstable : (prefixWord ++ tailWord_7348465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348465).length < 2 ^ (prefixWord ++ tailWord_7348465).sum := by decide
  have hdescent : baseEnd_7348465 < baseStart_7348465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348494 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7348494 : Nat := 118140960795 + 7348494 * 2 ^ 59
def prefixEnd_7348494 : Nat := 4983230072969 + 3 ^ 40 * 7348494 * 2
def baseEnd_7348494 : Nat := 3773309508680677217129897

theorem tailTrace_7348494 : CollatzResearch.WordTrace tailWord_7348494 prefixEnd_7348494 3773309508680677217129897 := by
  unfold tailWord_7348494
  simp only [CollatzResearch.WordTrace]
  refine ⟨33502699379958591962854567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178681063359779157135224357 33502699379958591962854567)
  ·
    refine ⟨50254049069937887944281851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33502699379958591962854567 50254049069937887944281851)
    ·
      refine ⟨75381073604906831916422777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50254049069937887944281851 75381073604906831916422777)
      ·
        refine ⟨56535805203680123937317083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75381073604906831916422777 56535805203680123937317083)
        ·
          refine ⟨84803707805520185905975625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56535805203680123937317083 84803707805520185905975625)
          ·
            refine ⟨63602780854140139429481719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84803707805520185905975625 63602780854140139429481719)
            ·
              refine ⟨95404171281210209144222579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63602780854140139429481719 95404171281210209144222579)
              ·
                refine ⟨143106256921815313716333869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95404171281210209144222579 143106256921815313716333869)
                ·
                  refine ⟨53664846345680742643625201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143106256921815313716333869 53664846345680742643625201)
                  ·
                    refine ⟨40248634759260556982718901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53664846345680742643625201 40248634759260556982718901)
                    ·
                      refine ⟨3773309508680677217129897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40248634759260556982718901 3773309508680677217129897)
                      ·
                        rfl

theorem cell23_7348494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7348494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348494 prefixEnd_7348494 := by exact prefixLift 7348494
  have htrace : WordTrace (prefixWord ++ tailWord_7348494) baseStart_7348494 baseEnd_7348494 := by
    simpa [prefixWord, tailWord_7348494, baseEnd_7348494] using wordTrace_append hprefix tailTrace_7348494
  have hstable : (prefixWord ++ tailWord_7348494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348494).length < 2 ^ (prefixWord ++ tailWord_7348494).sum := by decide
  have hdescent : baseEnd_7348494 < baseStart_7348494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348531 : List Nat := [1, 1, 1, 2, 5, 1, 3, 2, 3, 4]
def baseStart_7348531 : Nat := 118140960795 + 7348531 * 2 ^ 59
def prefixEnd_7348531 : Nat := 4983230072969 + 3 ^ 40 * 7348531 * 2
def baseEnd_7348531 : Nat := 1257776169154964524122409

theorem tailTrace_7348531 : CollatzResearch.WordTrace tailWord_7348531 prefixEnd_7348531 1257776169154964524122409 := by
  unfold tailWord_7348531
  simp only [CollatzResearch.WordTrace]
  refine ⟨268022944540534691021933447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178681963027023127347955631 268022944540534691021933447)
  ·
    refine ⟨402034416810802036532900171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268022944540534691021933447 402034416810802036532900171)
    ·
      refine ⟨603051625216203054799350257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402034416810802036532900171 603051625216203054799350257)
      ·
        refine ⟨452288718912152291099512693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603051625216203054799350257 452288718912152291099512693)
        ·
          refine ⟨42402067398014277290579315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 452288718912152291099512693 42402067398014277290579315)
          ·
            refine ⟨63603101097021415935868973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42402067398014277290579315 63603101097021415935868973)
            ·
              refine ⟨23851162911383030975950865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63603101097021415935868973 23851162911383030975950865)
              ·
                refine ⟨17888372183537273231963149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23851162911383030975950865 17888372183537273231963149)
                ·
                  refine ⟨6708139568826477461986181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17888372183537273231963149 6708139568826477461986181)
                  ·
                    refine ⟨1257776169154964524122409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6708139568826477461986181 1257776169154964524122409)
                    ·
                      rfl

theorem cell23_7348531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 4].length) (baseStart_7348531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348531 prefixEnd_7348531 := by exact prefixLift 7348531
  have htrace : WordTrace (prefixWord ++ tailWord_7348531) baseStart_7348531 baseEnd_7348531 := by
    simpa [prefixWord, tailWord_7348531, baseEnd_7348531] using wordTrace_append hprefix tailTrace_7348531
  have hstable : (prefixWord ++ tailWord_7348531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348531).length < 2 ^ (prefixWord ++ tailWord_7348531).sum := by decide
  have hdescent : baseEnd_7348531 < baseStart_7348531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348538 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4]
def baseStart_7348538 : Nat := 118140960795 + 7348538 * 2 ^ 59
def prefixEnd_7348538 : Nat := 4983230072969 + 3 ^ 40 * 7348538 * 2
def baseEnd_7348538 : Nat := 3773332101829475044979695

theorem tailTrace_7348538 : CollatzResearch.WordTrace tailWord_7348538 prefixEnd_7348538 3773332101829475044979695 := by
  unfold tailWord_7348538
  simp only [CollatzResearch.WordTrace]
  refine ⟨67005799962877332804359567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178682133234339554144958845 67005799962877332804359567)
  ·
    refine ⟨100508699944315999206539351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67005799962877332804359567 100508699944315999206539351)
    ·
      refine ⟨150763049916473998809809027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100508699944315999206539351 150763049916473998809809027)
      ·
        refine ⟨226144574874710998214713541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150763049916473998809809027 226144574874710998214713541)
        ·
          refine ⟨42402107789008312165258789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226144574874710998214713541 42402107789008312165258789)
          ·
            refine ⟨7950395210439058530986023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42402107789008312165258789 7950395210439058530986023)
            ·
              refine ⟨11925592815658587796479035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950395210439058530986023 11925592815658587796479035)
              ·
                refine ⟨17888389223487881694718553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925592815658587796479035 17888389223487881694718553)
                ·
                  refine ⟨13416291917615911271038915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17888389223487881694718553 13416291917615911271038915)
                  ·
                    refine ⟨20124437876423866906558373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13416291917615911271038915 20124437876423866906558373)
                    ·
                      refine ⟨3773332101829475044979695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20124437876423866906558373 3773332101829475044979695)
                      ·
                        rfl

theorem cell23_7348538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_7348538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348538 prefixEnd_7348538 := by exact prefixLift 7348538
  have htrace : WordTrace (prefixWord ++ tailWord_7348538) baseStart_7348538 baseEnd_7348538 := by
    simpa [prefixWord, tailWord_7348538, baseEnd_7348538] using wordTrace_append hprefix tailTrace_7348538
  have hstable : (prefixWord ++ tailWord_7348538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348538).length < 2 ^ (prefixWord ++ tailWord_7348538).sum := by decide
  have hdescent : baseEnd_7348538 < baseStart_7348538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348561 : List Nat := [1, 2, 2, 1, 4, 2, 3, 2, 6]
def baseStart_7348561 : Nat := 118140960795 + 7348561 * 2 ^ 59
def prefixEnd_7348561 : Nat := 4983230072969 + 3 ^ 40 * 7348561 * 2
def baseEnd_7348561 : Nat := 419260434653836494999121

theorem tailTrace_7348561 : CollatzResearch.WordTrace tailWord_7348561 prefixEnd_7348561 419260434653836494999121 := by
  unfold tailWord_7348561
  simp only [CollatzResearch.WordTrace]
  refine ⟨268024038730426006145525537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178682692486950670763683691 268024038730426006145525537)
  ·
    refine ⟨201018029047819504609144153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268024038730426006145525537 201018029047819504609144153)
    ·
      refine ⟨150763521785864628456858115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201018029047819504609144153 150763521785864628456858115)
      ·
        refine ⟨226145282678796942685287173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150763521785864628456858115 226145282678796942685287173)
        ·
          refine ⟨42402240502274426753491345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226145282678796942685287173 42402240502274426753491345)
          ·
            refine ⟨31801680376705820065118509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42402240502274426753491345 31801680376705820065118509)
            ·
              refine ⟨11925630141264682524419441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31801680376705820065118509 11925630141264682524419441)
              ·
                refine ⟨8944222605948511893314581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11925630141264682524419441 8944222605948511893314581)
                ·
                  refine ⟨419260434653836494999121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8944222605948511893314581 419260434653836494999121)
                  ·
                    rfl

theorem cell23_7348561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 2, 6].length) (baseStart_7348561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348561 prefixEnd_7348561 := by exact prefixLift 7348561
  have htrace : WordTrace (prefixWord ++ tailWord_7348561) baseStart_7348561 baseEnd_7348561 := by
    simpa [prefixWord, tailWord_7348561, baseEnd_7348561] using wordTrace_append hprefix tailTrace_7348561
  have hstable : (prefixWord ++ tailWord_7348561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348561).length < 2 ^ (prefixWord ++ tailWord_7348561).sum := by decide
  have hdescent : baseEnd_7348561 < baseStart_7348561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348622 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7348622 : Nat := 118140960795 + 7348622 * 2 ^ 59
def prefixEnd_7348622 : Nat := 4983230072969 + 3 ^ 40 * 7348622 * 2
def baseEnd_7348622 : Nat := 3773375234204452716329309

theorem tailTrace_7348622 : CollatzResearch.WordTrace tailWord_7348622 prefixEnd_7348622 3773375234204452716329309 := by
  unfold tailWord_7348622
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503282947900626695437015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178684175722136675708997413 33503282947900626695437015)
  ·
    refine ⟨50254924421850940043155523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33503282947900626695437015 50254924421850940043155523)
    ·
      refine ⟨75382386632776410064733285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50254924421850940043155523 75382386632776410064733285)
      ·
        refine ⟨14134197493645576887137491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75382386632776410064733285 14134197493645576887137491)
        ·
          refine ⟨21201296240468365330706237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14134197493645576887137491 21201296240468365330706237)
          ·
            refine ⟨7950486090175636999014839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21201296240468365330706237 7950486090175636999014839)
            ·
              refine ⟨11925729135263455498522259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950486090175636999014839 11925729135263455498522259)
              ·
                refine ⟨17888593702895183247783389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925729135263455498522259 17888593702895183247783389)
                ·
                  refine ⟨6708222638585693717918771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17888593702895183247783389 6708222638585693717918771)
                  ·
                    refine ⟨10062333957878540576878157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6708222638585693717918771 10062333957878540576878157)
                    ·
                      refine ⟨3773375234204452716329309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062333957878540576878157 3773375234204452716329309)
                      ·
                        rfl

theorem cell23_7348622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7348622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348622 prefixEnd_7348622 := by exact prefixLift 7348622
  have htrace : WordTrace (prefixWord ++ tailWord_7348622) baseStart_7348622 baseEnd_7348622 := by
    simpa [prefixWord, tailWord_7348622, baseEnd_7348622] using wordTrace_append hprefix tailTrace_7348622
  have hstable : (prefixWord ++ tailWord_7348622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348622).length < 2 ^ (prefixWord ++ tailWord_7348622).sum := by decide
  have hdescent : baseEnd_7348622 < baseStart_7348622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348631 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5]
def baseStart_7348631 : Nat := 118140960795 + 7348631 * 2 ^ 59
def prefixEnd_7348631 : Nat := 4983230072969 + 3 ^ 40 * 7348631 * 2
def baseEnd_7348631 : Nat := 3773379855530343181116767

theorem tailTrace_7348631 : CollatzResearch.WordTrace tailWord_7348631 prefixEnd_7348631 3773379855530343181116767 := by
  unfold tailWord_7348631
  simp only [CollatzResearch.WordTrace]
  refine ⟨268026591840172408100573747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178684394560114938733715831 268026591840172408100573747)
  ·
    refine ⟨402039887760258612150860621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268026591840172408100573747 402039887760258612150860621)
    ·
      refine ⟨150764957910096979556572733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402039887760258612150860621 150764957910096979556572733)
      ·
        refine ⟨56536859216286367333714775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150764957910096979556572733 56536859216286367333714775)
        ·
          refine ⟨84805288824429551000572163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56536859216286367333714775 84805288824429551000572163)
          ·
            refine ⟨127207933236644326500858245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84805288824429551000572163 127207933236644326500858245)
            ·
              refine ⟨23851487481870811218910921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127207933236644326500858245 23851487481870811218910921)
              ·
                refine ⟨17888615611403108414183191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23851487481870811218910921 17888615611403108414183191)
                ·
                  refine ⟨26832923417104662621274787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17888615611403108414183191 26832923417104662621274787)
                  ·
                    refine ⟨40249385125656993931912181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26832923417104662621274787 40249385125656993931912181)
                    ·
                      refine ⟨3773379855530343181116767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40249385125656993931912181 3773379855530343181116767)
                      ·
                        rfl

theorem cell23_7348631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_7348631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348631 prefixEnd_7348631 := by exact prefixLift 7348631
  have htrace : WordTrace (prefixWord ++ tailWord_7348631) baseStart_7348631 baseEnd_7348631 := by
    simpa [prefixWord, tailWord_7348631, baseEnd_7348631] using wordTrace_append hprefix tailTrace_7348631
  have hstable : (prefixWord ++ tailWord_7348631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348631).length < 2 ^ (prefixWord ++ tailWord_7348631).sum := by decide
  have hdescent : baseEnd_7348631 < baseStart_7348631 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348679 : List Nat := [1, 1, 4, 1, 1, 4, 4, 2, 1, 2, 2]
def baseStart_7348679 : Nat := 118140960795 + 7348679 * 2 ^ 59
def prefixEnd_7348679 : Nat := 4983230072969 + 3 ^ 40 * 7348679 * 2
def baseEnd_7348679 : Nat := 3773404502601758993316547

theorem tailTrace_7348679 : CollatzResearch.WordTrace tailWord_7348679 prefixEnd_7348679 3773404502601758993316547 := by
  unfold tailWord_7348679
  simp only [CollatzResearch.WordTrace]
  refine ⟨268028342543998512298321091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178685561695999008198880727 268028342543998512298321091)
  ·
    refine ⟨402042513815997768447481637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268028342543998512298321091 402042513815997768447481637)
    ·
      refine ⟨75382971340499581583902807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402042513815997768447481637 75382971340499581583902807)
      ·
        refine ⟨113074457010749372375854211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75382971340499581583902807 113074457010749372375854211)
        ·
          refine ⟨169611685516124058563781317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113074457010749372375854211 169611685516124058563781317)
          ·
            refine ⟨31802191034273260980708997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169611685516124058563781317 31802191034273260980708997)
            ·
              refine ⟨5962910818926236433882937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31802191034273260980708997 5962910818926236433882937)
              ·
                refine ⟨4472183114194677325412203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962910818926236433882937 4472183114194677325412203)
                ·
                  refine ⟨6708274671292015988118305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472183114194677325412203 6708274671292015988118305)
                  ·
                    refine ⟨5031206003469011991088729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708274671292015988118305 5031206003469011991088729)
                    ·
                      refine ⟨3773404502601758993316547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031206003469011991088729 3773404502601758993316547)
                      ·
                        rfl

theorem cell23_7348679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 2, 1, 2, 2].length) (baseStart_7348679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348679 prefixEnd_7348679 := by exact prefixLift 7348679
  have htrace : WordTrace (prefixWord ++ tailWord_7348679) baseStart_7348679 baseEnd_7348679 := by
    simpa [prefixWord, tailWord_7348679, baseEnd_7348679] using wordTrace_append hprefix tailTrace_7348679
  have hstable : (prefixWord ++ tailWord_7348679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348679).length < 2 ^ (prefixWord ++ tailWord_7348679).sum := by decide
  have hdescent : baseEnd_7348679 < baseStart_7348679 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348705 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 1, 3, 2]
def baseStart_7348705 : Nat := 118140960795 + 7348705 * 2 ^ 59
def prefixEnd_7348705 : Nat := 4983230072969 + 3 ^ 40 * 7348705 * 2
def baseEnd_7348705 : Nat := 3773417853098775891591427

theorem tailTrace_7348705 : CollatzResearch.WordTrace tailWord_7348705 prefixEnd_7348705 3773417853098775891591427 := by
  unfold tailWord_7348705
  simp only [CollatzResearch.WordTrace]
  refine ⟨268029290841904318738767569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178686193894602879159178379 268029290841904318738767569)
  ·
    refine ⟨201021968131428239054075677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268029290841904318738767569 201021968131428239054075677)
    ·
      refine ⟨75383238049285589645278379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201021968131428239054075677 75383238049285589645278379)
      ·
        refine ⟨113074857073928384467917569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75383238049285589645278379 113074857073928384467917569)
        ·
          refine ⟨84806142805446288350938177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113074857073928384467917569 84806142805446288350938177)
          ·
            refine ⟨63604607104084716263203633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84806142805446288350938177 63604607104084716263203633)
            ·
              refine ⟨47703455328063537197402725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63604607104084716263203633 47703455328063537197402725)
              ·
                refine ⟨8944397874011913224513011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47703455328063537197402725 8944397874011913224513011)
                ·
                  refine ⟨13416596811017869836769517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944397874011913224513011 13416596811017869836769517)
                  ·
                    refine ⟨5031223804131701188788569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13416596811017869836769517 5031223804131701188788569)
                    ·
                      refine ⟨3773417853098775891591427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031223804131701188788569 3773417853098775891591427)
                      ·
                        rfl

theorem cell23_7348705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 3, 2].length) (baseStart_7348705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348705 prefixEnd_7348705 := by exact prefixLift 7348705
  have htrace : WordTrace (prefixWord ++ tailWord_7348705) baseStart_7348705 baseEnd_7348705 := by
    simpa [prefixWord, tailWord_7348705, baseEnd_7348705] using wordTrace_append hprefix tailTrace_7348705
  have hstable : (prefixWord ++ tailWord_7348705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348705).length < 2 ^ (prefixWord ++ tailWord_7348705).sum := by decide
  have hdescent : baseEnd_7348705 < baseStart_7348705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348711 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 1, 8]
def baseStart_7348711 : Nat := 118140960795 + 7348711 * 2 ^ 59
def prefixEnd_7348711 : Nat := 4983230072969 + 3 ^ 40 * 7348711 * 2
def baseEnd_7348711 : Nat := 1257806977994234289372133

theorem tailTrace_7348711 : CollatzResearch.WordTrace tailWord_7348711 prefixEnd_7348711 1257806977994234289372133 := by
  unfold tailWord_7348711
  simp only [CollatzResearch.WordTrace]
  refine ⟨268029509679882581763485987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178686339786588387842323991 268029509679882581763485987)
  ·
    refine ⟨402044264519823872645228981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268029509679882581763485987 402044264519823872645228981)
    ·
      refine ⟨37691649798733488060490217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402044264519823872645228981 37691649798733488060490217)
      ·
        refine ⟨28268737349050116045367663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37691649798733488060490217 28268737349050116045367663)
        ·
          refine ⟨42403106023575174068051495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28268737349050116045367663 42403106023575174068051495)
          ·
            refine ⟨63604659035362761102077243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42403106023575174068051495 63604659035362761102077243)
            ·
              refine ⟨95406988553044141653115865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63604659035362761102077243 95406988553044141653115865)
              ·
                refine ⟨71555241414783106239836899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95406988553044141653115865 71555241414783106239836899)
                ·
                  refine ⟨107332862122174659359755349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71555241414783106239836899 107332862122174659359755349)
                  ·
                    refine ⟨1257806977994234289372133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107332862122174659359755349 1257806977994234289372133)
                    ·
                      rfl

theorem cell23_7348711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_7348711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348711 prefixEnd_7348711 := by exact prefixLift 7348711
  have htrace : WordTrace (prefixWord ++ tailWord_7348711) baseStart_7348711 baseEnd_7348711 := by
    simpa [prefixWord, tailWord_7348711, baseEnd_7348711] using wordTrace_append hprefix tailTrace_7348711
  have hstable : (prefixWord ++ tailWord_7348711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348711).length < 2 ^ (prefixWord ++ tailWord_7348711).sum := by decide
  have hdescent : baseEnd_7348711 < baseStart_7348711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348721 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 5]
def baseStart_7348721 : Nat := 118140960795 + 7348721 * 2 ^ 59
def prefixEnd_7348721 : Nat := 4983230072969 + 3 ^ 40 * 7348721 * 2
def baseEnd_7348721 : Nat := 3773426068789247828991353

theorem tailTrace_7348721 : CollatzResearch.WordTrace tailWord_7348721 prefixEnd_7348721 3773426068789247828991353 := by
  unfold tailWord_7348721
  simp only [CollatzResearch.WordTrace]
  refine ⟨268029874409846353471350017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178686582939897568980900011 268029874409846353471350017)
  ·
    refine ⟨201022405807384765103512513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268029874409846353471350017 201022405807384765103512513)
    ·
      refine ⟨150766804355538573827634385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201022405807384765103512513 150766804355538573827634385)
      ·
        refine ⟨113075103266653930370725789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150766804355538573827634385 113075103266653930370725789)
        ·
          refine ⟨42403163724995223889022171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113075103266653930370725789 42403163724995223889022171)
          ·
            refine ⟨63604745587492835833533257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42403163724995223889022171 63604745587492835833533257)
            ·
              refine ⟨47703559190619626875149943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63604745587492835833533257 47703559190619626875149943)
              ·
                refine ⟨71555338785929440312724915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47703559190619626875149943 71555338785929440312724915)
                ·
                  refine ⟨107333008178894160469087373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71555338785929440312724915 107333008178894160469087373)
                  ·
                    refine ⟨40249878067085310175907765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107333008178894160469087373 40249878067085310175907765)
                    ·
                      refine ⟨3773426068789247828991353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40249878067085310175907765 3773426068789247828991353)
                      ·
                        rfl

theorem cell23_7348721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_7348721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348721 prefixEnd_7348721 := by exact prefixLift 7348721
  have htrace : WordTrace (prefixWord ++ tailWord_7348721) baseStart_7348721 baseEnd_7348721 := by
    simpa [prefixWord, tailWord_7348721, baseEnd_7348721] using wordTrace_append hprefix tailTrace_7348721
  have hstable : (prefixWord ++ tailWord_7348721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348721).length < 2 ^ (prefixWord ++ tailWord_7348721).sum := by decide
  have hdescent : baseEnd_7348721 < baseStart_7348721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348735 : List Nat := [1, 1, 2, 2, 1, 2, 5, 1, 4, 2, 2]
def baseStart_7348735 : Nat := 118140960795 + 7348735 * 2 ^ 59
def prefixEnd_7348735 : Nat := 4983230072969 + 3 ^ 40 * 7348735 * 2
def baseEnd_7348735 : Nat := 3773433257518410774216289

theorem tailTrace_7348735 : CollatzResearch.WordTrace tailWord_7348735 prefixEnd_7348735 3773433257518410774216289 := by
  unfold tailWord_7348735
  simp only [CollatzResearch.WordTrace]
  refine ⟨268030385031795633862359659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178686923354530422574906439 268030385031795633862359659)
  ·
    refine ⟨402045577547693450793539489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268030385031795633862359659 402045577547693450793539489)
    ·
      refine ⟨301534183160770088095154617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402045577547693450793539489 301534183160770088095154617)
      ·
        refine ⟨226150637370577566071365963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301534183160770088095154617 226150637370577566071365963)
        ·
          refine ⟨339225956055866349107048945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226150637370577566071365963 339225956055866349107048945)
          ·
            refine ⟨254419467041899761830286709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339225956055866349107048945 254419467041899761830286709)
            ·
              refine ⟨23851825035178102671589379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254419467041899761830286709 23851825035178102671589379)
              ·
                refine ⟨35777737552767154007384069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23851825035178102671589379 35777737552767154007384069)
                ·
                  refine ⟨6708325791143841376384513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35777737552767154007384069 6708325791143841376384513)
                  ·
                    refine ⟨5031244343357881032288385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708325791143841376384513 5031244343357881032288385)
                    ·
                      refine ⟨3773433257518410774216289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031244343357881032288385 3773433257518410774216289)
                      ·
                        rfl

theorem cell23_7348735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 1, 4, 2, 2].length) (baseStart_7348735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348735 prefixEnd_7348735 := by exact prefixLift 7348735
  have htrace : WordTrace (prefixWord ++ tailWord_7348735) baseStart_7348735 baseEnd_7348735 := by
    simpa [prefixWord, tailWord_7348735, baseEnd_7348735] using wordTrace_append hprefix tailTrace_7348735
  have hstable : (prefixWord ++ tailWord_7348735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348735).length < 2 ^ (prefixWord ++ tailWord_7348735).sum := by decide
  have hdescent : baseEnd_7348735 < baseStart_7348735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348741 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 7]
def baseStart_7348741 : Nat := 118140960795 + 7348741 * 2 ^ 59
def prefixEnd_7348741 : Nat := 4983230072969 + 3 ^ 40 * 7348741 * 2
def baseEnd_7348741 : Nat := 419270704266926416749029

theorem tailTrace_7348741 : CollatzResearch.WordTrace tailWord_7348741 prefixEnd_7348741 419270704266926416749029 := by
  unfold tailWord_7348741
  simp only [CollatzResearch.WordTrace]
  refine ⟨268030603869773896887078077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178687069246515931258052051 268030603869773896887078077)
  ·
    refine ⟨100511476451165211332654279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268030603869773896887078077 100511476451165211332654279)
    ·
      refine ⟨150767214676747816998981419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100511476451165211332654279 150767214676747816998981419)
      ·
        refine ⟨226150822015121725498472129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150767214676747816998981419 226150822015121725498472129)
        ·
          refine ⟨169613116511341294123854097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226150822015121725498472129 169613116511341294123854097)
          ·
            refine ⟨127209837383505970592890573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169613116511341294123854097 127209837383505970592890573)
            ·
              refine ⟨47703689018814738972333965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127209837383505970592890573 47703689018814738972333965)
              ·
                refine ⟨17888883382055527114625237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47703689018814738972333965 17888883382055527114625237)
                ·
                  refine ⟨419270704266926416749029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17888883382055527114625237 419270704266926416749029)
                  ·
                    rfl

theorem cell23_7348741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 7].length) (baseStart_7348741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348741 prefixEnd_7348741 := by exact prefixLift 7348741
  have htrace : WordTrace (prefixWord ++ tailWord_7348741) baseStart_7348741 baseEnd_7348741 := by
    simpa [prefixWord, tailWord_7348741, baseEnd_7348741] using wordTrace_append hprefix tailTrace_7348741
  have hstable : (prefixWord ++ tailWord_7348741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348741).length < 2 ^ (prefixWord ++ tailWord_7348741).sum := by decide
  have hdescent : baseEnd_7348741 < baseStart_7348741 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348748 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_7348748 : Nat := 118140960795 + 7348748 * 2 ^ 59
def prefixEnd_7348748 : Nat := 4983230072969 + 3 ^ 40 * 7348748 * 2
def baseEnd_7348748 : Nat := 3773439932766919223353729

theorem tailTrace_7348748 : CollatzResearch.WordTrace tailWord_7348748 prefixEnd_7348748 3773439932766919223353729 := by
  unfold tailWord_7348748
  simp only [CollatzResearch.WordTrace]
  refine ⟨134015429590374268541291449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178687239453832358055055265 134015429590374268541291449)
  ·
    refine ⟨100511572192780701405968587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134015429590374268541291449 100511572192780701405968587)
    ·
      refine ⟨150767358289171052108952881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100511572192780701405968587 150767358289171052108952881)
      ·
        refine ⟨113075518716878289081714661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150767358289171052108952881 113075518716878289081714661)
        ·
          refine ⟨21201659759414679202821499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113075518716878289081714661 21201659759414679202821499)
          ·
            refine ⟨31802489639122018804232249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21201659759414679202821499 31802489639122018804232249)
            ·
              refine ⟨23851867229341514103174187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31802489639122018804232249 23851867229341514103174187)
              ·
                refine ⟨35777800844012271154761281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23851867229341514103174187 35777800844012271154761281)
                ·
                  refine ⟨26833350633009203366070961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35777800844012271154761281 26833350633009203366070961)
                  ·
                    refine ⟨20125012974756902524553221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26833350633009203366070961 20125012974756902524553221)
                    ·
                      refine ⟨3773439932766919223353729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20125012974756902524553221 3773439932766919223353729)
                      ·
                        rfl

theorem cell23_7348748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_7348748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348748 prefixEnd_7348748 := by exact prefixLift 7348748
  have htrace : WordTrace (prefixWord ++ tailWord_7348748) baseStart_7348748 baseEnd_7348748 := by
    simpa [prefixWord, tailWord_7348748, baseEnd_7348748] using wordTrace_append hprefix tailTrace_7348748
  have hstable : (prefixWord ++ tailWord_7348748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348748).length < 2 ^ (prefixWord ++ tailWord_7348748).sum := by decide
  have hdescent : baseEnd_7348748 < baseStart_7348748 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348831 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 10]
def baseStart_7348831 : Nat := 118140960795 + 7348831 * 2 ^ 59
def prefixEnd_7348831 : Nat := 4983230072969 + 3 ^ 40 * 7348831 * 2
def baseEnd_7348831 : Nat := 419275839073471377623983

theorem tailTrace_7348831 : CollatzResearch.WordTrace tailWord_7348831 prefixEnd_7348831 419275839073471377623983 := by
  unfold tailWord_7348831
  simp only [CollatzResearch.WordTrace]
  refine ⟨268033886439447842257854347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178689257626298561505236231 268033886439447842257854347)
  ·
    refine ⟨402050829659171763386781521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268033886439447842257854347 402050829659171763386781521)
    ·
      refine ⟨301538122244378822540086141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402050829659171763386781521 301538122244378822540086141)
      ·
        refine ⟨113076795841642058452532303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301538122244378822540086141 113076795841642058452532303)
        ·
          refine ⟨169615193762463087678798455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113076795841642058452532303 169615193762463087678798455)
          ·
            refine ⟨254422790643694631518197683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169615193762463087678798455 254422790643694631518197683)
            ·
              refine ⟨381634185965541947277296525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254422790643694631518197683 381634185965541947277296525)
              ·
                refine ⟨143112819737078230228986197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381634185965541947277296525 143112819737078230228986197)
                ·
                  refine ⟨419275839073471377623983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 143112819737078230228986197 419275839073471377623983)
                  ·
                    rfl

theorem cell23_7348831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 10].length) (baseStart_7348831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348831 prefixEnd_7348831 := by exact prefixLift 7348831
  have htrace : WordTrace (prefixWord ++ tailWord_7348831) baseStart_7348831 baseEnd_7348831 := by
    simpa [prefixWord, tailWord_7348831, baseEnd_7348831] using wordTrace_append hprefix tailTrace_7348831
  have hstable : (prefixWord ++ tailWord_7348831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348831).length < 2 ^ (prefixWord ++ tailWord_7348831).sum := by decide
  have hdescent : baseEnd_7348831 < baseStart_7348831 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348909 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_7348909 : Nat := 118140960795 + 7348909 * 2 ^ 59
def prefixEnd_7348909 : Nat := 4983230072969 + 3 ^ 40 * 7348909 * 2
def baseEnd_7348909 : Nat := 3773522603152293093440489

theorem tailTrace_7348909 : CollatzResearch.WordTrace tailWord_7348909 prefixEnd_7348909 3773522603152293093440489 := by
  unfold tailWord_7348909
  simp only [CollatzResearch.WordTrace]
  refine ⟨268036731333165261579193781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178691154222110174386129187 268036731333165261579193781)
  ·
    refine ⟨25128443562484243273049417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268036731333165261579193781 25128443562484243273049417)
    ·
      refine ⟨18846332671863182454787063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25128443562484243273049417 18846332671863182454787063)
      ·
        refine ⟨28269499007794773682180595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18846332671863182454787063 28269499007794773682180595)
        ·
          refine ⟨42404248511692160523270893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28269499007794773682180595 42404248511692160523270893)
          ·
            refine ⟨15901593191884560196226585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42404248511692160523270893 15901593191884560196226585)
            ·
              refine ⟨11926194893913420147169939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15901593191884560196226585 11926194893913420147169939)
              ·
                refine ⟨17889292340870130220754909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11926194893913420147169939 17889292340870130220754909)
                ·
                  refine ⟨6708484627826298832783091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17889292340870130220754909 6708484627826298832783091)
                  ·
                    refine ⟨10062726941739448249174637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6708484627826298832783091 10062726941739448249174637)
                    ·
                      refine ⟨3773522603152293093440489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062726941739448249174637 3773522603152293093440489)
                      ·
                        rfl

theorem cell23_7348909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_7348909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348909 prefixEnd_7348909 := by exact prefixLift 7348909
  have htrace : WordTrace (prefixWord ++ tailWord_7348909) baseStart_7348909 baseEnd_7348909 := by
    simpa [prefixWord, tailWord_7348909, baseEnd_7348909] using wordTrace_append hprefix tailTrace_7348909
  have hstable : (prefixWord ++ tailWord_7348909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348909).length < 2 ^ (prefixWord ++ tailWord_7348909).sum := by decide
  have hdescent : baseEnd_7348909 < baseStart_7348909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348925 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 1, 6]
def baseStart_7348925 : Nat := 118140960795 + 7348925 * 2 ^ 59
def prefixEnd_7348925 : Nat := 4983230072969 + 3 ^ 40 * 7348925 * 2
def baseEnd_7348925 : Nat := 1257843606280921676946805

theorem tailTrace_7348925 : CollatzResearch.WordTrace tailWord_7348925 prefixEnd_7348925 1257843606280921676946805 := by
  unfold tailWord_7348925
  simp only [CollatzResearch.WordTrace]
  refine ⟨268037314901107296311776229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178691543267404864207850819 268037314901107296311776229)
  ·
    refine ⟨50256996543957618058458043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268037314901107296311776229 50256996543957618058458043)
    ·
      refine ⟨75385494815936427087687065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50256996543957618058458043 75385494815936427087687065)
      ·
        refine ⟨56539121111952320315765299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75385494815936427087687065 56539121111952320315765299)
        ·
          refine ⟨84808681667928480473647949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56539121111952320315765299 84808681667928480473647949)
          ·
            refine ⟨31803255625473180177617981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84808681667928480473647949 31803255625473180177617981)
            ·
              refine ⟨11926220859552442566606743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31803255625473180177617981 11926220859552442566606743)
              ·
                refine ⟨17889331289328663849910115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11926220859552442566606743 17889331289328663849910115)
                ·
                  refine ⟨26833996933992995774865173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17889331289328663849910115 26833996933992995774865173)
                  ·
                    refine ⟨1257843606280921676946805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26833996933992995774865173 1257843606280921676946805)
                    ·
                      rfl

theorem cell23_7348925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 6].length) (baseStart_7348925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348925 prefixEnd_7348925 := by exact prefixLift 7348925
  have htrace : WordTrace (prefixWord ++ tailWord_7348925) baseStart_7348925 baseEnd_7348925 := by
    simpa [prefixWord, tailWord_7348925, baseEnd_7348925] using wordTrace_append hprefix tailTrace_7348925
  have hstable : (prefixWord ++ tailWord_7348925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348925).length < 2 ^ (prefixWord ++ tailWord_7348925).sum := by decide
  have hdescent : baseEnd_7348925 < baseStart_7348925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348932 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_7348932 : Nat := 118140960795 + 7348932 * 2 ^ 59
def prefixEnd_7348932 : Nat := 4983230072969 + 3 ^ 40 * 7348932 * 2
def baseEnd_7348932 : Nat := 3773534413207346503452883

theorem tailTrace_7348932 : CollatzResearch.WordTrace tailWord_7348932 prefixEnd_7348932 3773534413207346503452883 := by
  unfold tailWord_7348932
  simp only [CollatzResearch.WordTrace]
  refine ⟨134018785106040968253640525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178691713474721291004854033 134018785106040968253640525)
  ·
    refine ⟨50257044414765363095115197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134018785106040968253640525 50257044414765363095115197)
    ·
      refine ⟨18846391655537011160668199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50257044414765363095115197 18846391655537011160668199)
      ·
        refine ⟨28269587483305516741002299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18846391655537011160668199 28269587483305516741002299)
        ·
          refine ⟨42404381224958275111503449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28269587483305516741002299 42404381224958275111503449)
          ·
            refine ⟨31803285918718706333627587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42404381224958275111503449 31803285918718706333627587)
            ·
              refine ⟨47704928878078059500441381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31803285918718706333627587 47704928878078059500441381)
              ·
                refine ⟨8944674164639636156332759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47704928878078059500441381 8944674164639636156332759)
                ·
                  refine ⟨13417011246959454234499139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944674164639636156332759 13417011246959454234499139)
                  ·
                    refine ⟨20125516870439181351748709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13417011246959454234499139 20125516870439181351748709)
                    ·
                      refine ⟨3773534413207346503452883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20125516870439181351748709 3773534413207346503452883)
                      ·
                        rfl

theorem cell23_7348932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_7348932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348932 prefixEnd_7348932 := by exact prefixLift 7348932
  have htrace : WordTrace (prefixWord ++ tailWord_7348932) baseStart_7348932 baseEnd_7348932 := by
    simpa [prefixWord, tailWord_7348932, baseEnd_7348932] using wordTrace_append hprefix tailTrace_7348932
  have hstable : (prefixWord ++ tailWord_7348932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348932).length < 2 ^ (prefixWord ++ tailWord_7348932).sum := by decide
  have hdescent : baseEnd_7348932 < baseStart_7348932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348952 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3]
def baseStart_7348952 : Nat := 118140960795 + 7348952 * 2 ^ 59
def prefixEnd_7348952 : Nat := 4983230072969 + 3 ^ 40 * 7348952 * 2
def baseEnd_7348952 : Nat := 3773544682820436425202791

theorem tailTrace_7348952 : CollatzResearch.WordTrace tailWord_7348952 prefixEnd_7348952 3773544682820436425202791 := by
  unfold tailWord_7348952
  simp only [CollatzResearch.WordTrace]
  refine ⟨134019149836004739961504555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178692199781339653282006073 134019149836004739961504555)
  ·
    refine ⟨201028724754007109942256833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134019149836004739961504555 201028724754007109942256833)
    ·
      refine ⟨150771543565505332456692625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201028724754007109942256833 150771543565505332456692625)
      ·
        refine ⟨113078657674128999342519469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150771543565505332456692625 113078657674128999342519469)
        ·
          refine ⟨42404496627798374753444801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113078657674128999342519469 42404496627798374753444801)
          ·
            refine ⟨31803372470848781065083601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42404496627798374753444801 31803372470848781065083601)
            ·
              refine ⟨23852529353136585798812701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31803372470848781065083601 23852529353136585798812701)
              ·
                refine ⟨8944698507426219674554763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23852529353136585798812701 8944698507426219674554763)
                ·
                  refine ⟨13417047761139329511832145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8944698507426219674554763 13417047761139329511832145)
                  ·
                    refine ⟨10062785820854497133874109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13417047761139329511832145 10062785820854497133874109)
                    ·
                      refine ⟨3773544682820436425202791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062785820854497133874109 3773544682820436425202791)
                      ·
                        rfl

theorem cell23_7348952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 1, 2, 3].length) (baseStart_7348952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348952 prefixEnd_7348952 := by exact prefixLift 7348952
  have htrace : WordTrace (prefixWord ++ tailWord_7348952) baseStart_7348952 baseEnd_7348952 := by
    simpa [prefixWord, tailWord_7348952, baseEnd_7348952] using wordTrace_append hprefix tailTrace_7348952
  have hstable : (prefixWord ++ tailWord_7348952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348952).length < 2 ^ (prefixWord ++ tailWord_7348952).sum := by decide
  have hdescent : baseEnd_7348952 < baseStart_7348952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7348982 : List Nat := [5, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7348982 : Nat := 118140960795 + 7348982 * 2 ^ 59
def prefixEnd_7348982 : Nat := 4983230072969 + 3 ^ 40 * 7348982 * 2
def baseEnd_7348982 : Nat := 3773560087240071307827653

theorem tailTrace_7348982 : CollatzResearch.WordTrace tailWord_7348982 prefixEnd_7348982 3773560087240071307827653 := by
  unfold tailWord_7348982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16752462116368799690412575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178692929241267196697734133 16752462116368799690412575)
  ·
    refine ⟨25128693174553199535618863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16752462116368799690412575 25128693174553199535618863)
    ·
      refine ⟨37693039761829799303428295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25128693174553199535618863 37693039761829799303428295)
      ·
        refine ⟨56539559642744698955142443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37693039761829799303428295 56539559642744698955142443)
        ·
          refine ⟨84809339464117048432713665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56539559642744698955142443 84809339464117048432713665)
          ·
            refine ⟨63607004598087786324535249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84809339464117048432713665 63607004598087786324535249)
            ·
              refine ⟨47705253448565839743401437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63607004598087786324535249 47705253448565839743401437)
              ·
                refine ⟨17889470043212189903775539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47705253448565839743401437 17889470043212189903775539)
                ·
                  refine ⟨26834205064818284855663309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17889470043212189903775539 26834205064818284855663309)
                  ·
                    refine ⟨10062826899306856820873741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26834205064818284855663309 10062826899306856820873741)
                    ·
                      refine ⟨3773560087240071307827653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062826899306856820873741 3773560087240071307827653)
                      ·
                        rfl

theorem cell23_7348982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7348982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7348982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7348982 prefixEnd_7348982 := by exact prefixLift 7348982
  have htrace : WordTrace (prefixWord ++ tailWord_7348982) baseStart_7348982 baseEnd_7348982 := by
    simpa [prefixWord, tailWord_7348982, baseEnd_7348982] using wordTrace_append hprefix tailTrace_7348982
  have hstable : (prefixWord ++ tailWord_7348982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7348982).length < 2 ^ (prefixWord ++ tailWord_7348982).sum := by decide
  have hdescent : baseEnd_7348982 < baseStart_7348982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7348982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349025 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 3]
def baseStart_7349025 : Nat := 118140960795 + 7349025 * 2 ^ 59
def prefixEnd_7349025 : Nat := 4983230072969 + 3 ^ 40 * 7349025 * 2
def baseEnd_7349025 : Nat := 3773582166908214639589955

theorem tailTrace_7349025 : CollatzResearch.WordTrace tailWord_7349025 prefixEnd_7349025 3773582166908214639589955 := by
  unfold tailWord_7349025
  simp only [CollatzResearch.WordTrace]
  refine ⟨268040962200745013390416529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178693974800496675593611019 268040962200745013390416529)
  ·
    refine ⟨201030721650558760042812397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268040962200745013390416529 201030721650558760042812397)
    ·
      refine ⟨75386520618959535016054649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201030721650558760042812397 75386520618959535016054649)
      ·
        refine ⟨56539890464219651262040987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75386520618959535016054649 56539890464219651262040987)
        ·
          refine ⟨84809835696329476893061481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56539890464219651262040987 84809835696329476893061481)
          ·
            refine ⟨63607376772247107669796111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84809835696329476893061481 63607376772247107669796111)
            ·
              refine ⟨95411065158370661504694167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63607376772247107669796111 95411065158370661504694167)
              ·
                refine ⟨143116597737555992257041251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95411065158370661504694167 143116597737555992257041251)
                ·
                  refine ⟨214674896606333988385561877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143116597737555992257041251 214674896606333988385561877)
                  ·
                    refine ⟨10062885778421905705573213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214674896606333988385561877 10062885778421905705573213)
                    ·
                      refine ⟨3773582166908214639589955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10062885778421905705573213 3773582166908214639589955)
                      ·
                        rfl

theorem cell23_7349025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_7349025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349025 prefixEnd_7349025 := by exact prefixLift 7349025
  have htrace : WordTrace (prefixWord ++ tailWord_7349025) baseStart_7349025 baseEnd_7349025 := by
    simpa [prefixWord, tailWord_7349025, baseEnd_7349025] using wordTrace_append hprefix tailTrace_7349025
  have hstable : (prefixWord ++ tailWord_7349025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349025).length < 2 ^ (prefixWord ++ tailWord_7349025).sum := by decide
  have hdescent : baseEnd_7349025 < baseStart_7349025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349045 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 9]
def baseStart_7349045 : Nat := 118140960795 + 7349045 * 2 ^ 59
def prefixEnd_7349045 : Nat := 4983230072969 + 3 ^ 40 * 7349045 * 2
def baseEnd_7349045 : Nat := 419288048502367173482207

theorem tailTrace_7349045 : CollatzResearch.WordTrace tailWord_7349045 prefixEnd_7349045 419288048502367173482207 := by
  unfold tailWord_7349045
  simp only [CollatzResearch.WordTrace]
  refine ⟨268041691660672556806144589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178694461107115037870763059 268041691660672556806144589)
  ·
    refine ⟨100515634372752208802304221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268041691660672556806144589 100515634372752208802304221)
    ·
      refine ⟨37693362889782078300864083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100515634372752208802304221 37693362889782078300864083)
      ·
        refine ⟨56540044334673117451296125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37693362889782078300864083 56540044334673117451296125)
        ·
          refine ⟨21202516625502419044236047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56540044334673117451296125 21202516625502419044236047)
          ·
            refine ⟨31803774938253628566354071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21202516625502419044236047 31803774938253628566354071)
            ·
              refine ⟨47705662407380442849531107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31803774938253628566354071 47705662407380442849531107)
              ·
                refine ⟨71558493611070664274296661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47705662407380442849531107 71558493611070664274296661)
                ·
                  refine ⟨419288048502367173482207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71558493611070664274296661 419288048502367173482207)
                  ·
                    rfl

theorem cell23_7349045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_7349045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349045 prefixEnd_7349045 := by exact prefixLift 7349045
  have htrace : WordTrace (prefixWord ++ tailWord_7349045) baseStart_7349045 baseEnd_7349045 := by
    simpa [prefixWord, tailWord_7349045, baseEnd_7349045] using wordTrace_append hprefix tailTrace_7349045
  have hstable : (prefixWord ++ tailWord_7349045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349045).length < 2 ^ (prefixWord ++ tailWord_7349045).sum := by decide
  have hdescent : baseEnd_7349045 < baseStart_7349045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349073 : List Nat := [1, 2, 2, 1, 6, 2, 1, 2, 2, 2, 2]
def baseStart_7349073 : Nat := 118140960795 + 7349073 * 2 ^ 59
def prefixEnd_7349073 : Nat := 4983230072969 + 3 ^ 40 * 7349073 * 2
def baseEnd_7349073 : Nat := 3773606813979630451789735

theorem tailTrace_7349073 : CollatzResearch.WordTrace tailWord_7349073 prefixEnd_7349073 3773606813979630451789735 := by
  unfold tailWord_7349073
  simp only [CollatzResearch.WordTrace]
  refine ⟨268042712904571117588163873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178695141936380745058775915 268042712904571117588163873)
  ·
    refine ⟨201032034678428338191122905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268042712904571117588163873 201032034678428338191122905)
    ·
      refine ⟨150774026008821253643342179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201032034678428338191122905 150774026008821253643342179)
      ·
        refine ⟨226161039013231880465013269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150774026008821253643342179 226161039013231880465013269)
        ·
          refine ⟨10601298703745244396797497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226161039013231880465013269 10601298703745244396797497)
          ·
            refine ⟨7950974027808933297598123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10601298703745244396797497 7950974027808933297598123)
            ·
              refine ⟨11926461041713399946397185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7950974027808933297598123 11926461041713399946397185)
              ·
                refine ⟨8944845781285049959797889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11926461041713399946397185 8944845781285049959797889)
                ·
                  refine ⟨6708634335963787469848417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944845781285049959797889 6708634335963787469848417)
                  ·
                    refine ⟨5031475751972840602386313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708634335963787469848417 5031475751972840602386313)
                    ·
                      refine ⟨3773606813979630451789735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031475751972840602386313 3773606813979630451789735)
                      ·
                        rfl

theorem cell23_7349073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2, 2, 2].length) (baseStart_7349073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349073 prefixEnd_7349073 := by exact prefixLift 7349073
  have htrace : WordTrace (prefixWord ++ tailWord_7349073) baseStart_7349073 baseEnd_7349073 := by
    simpa [prefixWord, tailWord_7349073, baseEnd_7349073] using wordTrace_append hprefix tailTrace_7349073
  have hstable : (prefixWord ++ tailWord_7349073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349073).length < 2 ^ (prefixWord ++ tailWord_7349073).sum := by decide
  have hdescent : baseEnd_7349073 < baseStart_7349073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349075 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 2, 5]
def baseStart_7349075 : Nat := 118140960795 + 7349075 * 2 ^ 59
def prefixEnd_7349075 : Nat := 4983230072969 + 3 ^ 40 * 7349075 * 2
def baseEnd_7349075 : Nat := 1257869280313646481321575

theorem tailTrace_7349075 : CollatzResearch.WordTrace tailWord_7349075 prefixEnd_7349075 1257869280313646481321575 := by
  unfold tailWord_7349075
  simp only [CollatzResearch.WordTrace]
  refine ⟨268042785850563871929736679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178695190567042581286491119 268042785850563871929736679)
  ·
    refine ⟨402064178775845807894605019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268042785850563871929736679 402064178775845807894605019)
    ·
      refine ⟨603096268163768711841907529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402064178775845807894605019 603096268163768711841907529)
      ·
        refine ⟨452322201122826533881430647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 603096268163768711841907529 452322201122826533881430647)
        ·
          refine ⟨678483301684239800822145971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452322201122826533881430647 678483301684239800822145971)
          ·
            refine ⟨1017724952526359701233218957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678483301684239800822145971 1017724952526359701233218957)
            ·
              refine ⟨381646857197384887962457109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1017724952526359701233218957 381646857197384887962457109)
              ·
                refine ⟨17889696431127416623240177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 381646857197384887962457109 17889696431127416623240177)
                ·
                  refine ⟨13417272323345562467430133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17889696431127416623240177 13417272323345562467430133)
                  ·
                    refine ⟨1257869280313646481321575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13417272323345562467430133 1257869280313646481321575)
                    ·
                      rfl

theorem cell23_7349075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 5].length) (baseStart_7349075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349075 prefixEnd_7349075 := by exact prefixLift 7349075
  have htrace : WordTrace (prefixWord ++ tailWord_7349075) baseStart_7349075 baseEnd_7349075 := by
    simpa [prefixWord, tailWord_7349075, baseEnd_7349075] using wordTrace_append hprefix tailTrace_7349075
  have hstable : (prefixWord ++ tailWord_7349075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349075).length < 2 ^ (prefixWord ++ tailWord_7349075).sum := by decide
  have hdescent : baseEnd_7349075 < baseStart_7349075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349090 : List Nat := [3, 3, 2, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_7349090 : Nat := 118140960795 + 7349090 * 2 ^ 59
def prefixEnd_7349090 : Nat := 4983230072969 + 3 ^ 40 * 7349090 * 2
def baseEnd_7349090 : Nat := 3773615543150756885277157

theorem tailTrace_7349090 : CollatzResearch.WordTrace tailWord_7349090 prefixEnd_7349090 3773615543150756885277157 := by
  unfold tailWord_7349090
  simp only [CollatzResearch.WordTrace]
  refine ⟨67010833236377382372883181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178695555297006352994355149 67010833236377382372883181)
  ·
    refine ⟨25129062463641518389831193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67010833236377382372883181 25129062463641518389831193)
    ·
      refine ⟨18846796847731138792373395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25129062463641518389831193 18846796847731138792373395)
      ·
        refine ⟨28270195271596708188560093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18846796847731138792373395 28270195271596708188560093)
        ·
          refine ⟨10601323226848765570710035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28270195271596708188560093 10601323226848765570710035)
          ·
            refine ⟨15901984840273148356065053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10601323226848765570710035 15901984840273148356065053)
            ·
              refine ⟨5963244315102430633524395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15901984840273148356065053 5963244315102430633524395)
              ·
                refine ⟨8944866472653645950286593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963244315102430633524395 8944866472653645950286593)
                ·
                  refine ⟨6708649854490234462714945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8944866472653645950286593 6708649854490234462714945)
                  ·
                    refine ⟨5031487390867675847036209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708649854490234462714945 5031487390867675847036209)
                    ·
                      refine ⟨3773615543150756885277157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031487390867675847036209 3773615543150756885277157)
                      ·
                        rfl

theorem cell23_7349090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_7349090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349090 prefixEnd_7349090 := by exact prefixLift 7349090
  have htrace : WordTrace (prefixWord ++ tailWord_7349090) baseStart_7349090 baseEnd_7349090 := by
    simpa [prefixWord, tailWord_7349090, baseEnd_7349090] using wordTrace_append hprefix tailTrace_7349090
  have hstable : (prefixWord ++ tailWord_7349090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349090).length < 2 ^ (prefixWord ++ tailWord_7349090).sum := by decide
  have hdescent : baseEnd_7349090 < baseStart_7349090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349112 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2]
def baseStart_7349112 : Nat := 118140960795 + 7349112 * 2 ^ 59
def prefixEnd_7349112 : Nat := 4983230072969 + 3 ^ 40 * 7349112 * 2
def baseEnd_7349112 : Nat := 3773626839725155799202055

theorem tailTrace_7349112 : CollatzResearch.WordTrace tailWord_7349112 prefixEnd_7349112 3773626839725155799202055 := by
  unfold tailWord_7349112
  simp only [CollatzResearch.WordTrace]
  refine ⟨134022067675714913624416795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178696090234286551499222393 134022067675714913624416795)
  ·
    refine ⟨201033101513572370436625193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134022067675714913624416795 201033101513572370436625193)
    ·
      refine ⟨150774826135179277827468895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201033101513572370436625193 150774826135179277827468895)
      ·
        refine ⟨226162239202768916741203343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150774826135179277827468895 226162239202768916741203343)
        ·
          refine ⟨339243358804153375111805015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226162239202768916741203343 339243358804153375111805015)
          ·
            refine ⟨508865038206230062667707523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339243358804153375111805015 508865038206230062667707523)
            ·
              refine ⟨763297557309345094001561285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508865038206230062667707523 763297557309345094001561285)
              ·
                refine ⟨143118291995502205125292741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763297557309345094001561285 143118291995502205125292741)
                ·
                  refine ⟨26834679749156663460992389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143118291995502205125292741 26834679749156663460992389)
                  ·
                    refine ⟨5031502452966874398936073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26834679749156663460992389 5031502452966874398936073)
                    ·
                      refine ⟨3773626839725155799202055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031502452966874398936073 3773626839725155799202055)
                      ·
                        rfl

theorem cell23_7349112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 4, 4, 2].length) (baseStart_7349112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349112 prefixEnd_7349112 := by exact prefixLift 7349112
  have htrace : WordTrace (prefixWord ++ tailWord_7349112) baseStart_7349112 baseEnd_7349112 := by
    simpa [prefixWord, tailWord_7349112, baseEnd_7349112] using wordTrace_append hprefix tailTrace_7349112
  have hstable : (prefixWord ++ tailWord_7349112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349112).length < 2 ^ (prefixWord ++ tailWord_7349112).sum := by decide
  have hdescent : baseEnd_7349112 < baseStart_7349112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349132 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_7349132 : Nat := 118140960795 + 7349132 * 2 ^ 59
def prefixEnd_7349132 : Nat := 4983230072969 + 3 ^ 40 * 7349132 * 2
def baseEnd_7349132 : Nat := 3773637109338245720951963

theorem tailTrace_7349132 : CollatzResearch.WordTrace tailWord_7349132 prefixEnd_7349132 3773637109338245720951963 := by
  unfold tailWord_7349132
  simp only [CollatzResearch.WordTrace]
  refine ⟨134022432405678685332280825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178696576540904913776374433 134022432405678685332280825)
  ·
    refine ⟨100516824304259013999210619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134022432405678685332280825 100516824304259013999210619)
    ·
      refine ⟨150775236456388520998815929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100516824304259013999210619 150775236456388520998815929)
      ·
        refine ⟨113081427342291390749111947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150775236456388520998815929 113081427342291390749111947)
        ·
          refine ⟨169622141013437086123667921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113081427342291390749111947 169622141013437086123667921)
          ·
            refine ⟨127216605760077814592750941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169622141013437086123667921 127216605760077814592750941)
            ·
              refine ⟨47706227160029180472281603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127216605760077814592750941 47706227160029180472281603)
              ·
                refine ⟨71559340740043770708422405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47706227160029180472281603 71559340740043770708422405)
                ·
                  refine ⟨13417376388758207007829201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71559340740043770708422405 13417376388758207007829201)
                  ·
                    refine ⟨10063032291568655255871901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13417376388758207007829201 10063032291568655255871901)
                    ·
                      refine ⟨3773637109338245720951963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063032291568655255871901 3773637109338245720951963)
                      ·
                        rfl

theorem cell23_7349132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_7349132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349132 prefixEnd_7349132 := by exact prefixLift 7349132
  have htrace : WordTrace (prefixWord ++ tailWord_7349132) baseStart_7349132 baseEnd_7349132 := by
    simpa [prefixWord, tailWord_7349132, baseEnd_7349132] using wordTrace_append hprefix tailTrace_7349132
  have hstable : (prefixWord ++ tailWord_7349132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349132).length < 2 ^ (prefixWord ++ tailWord_7349132).sum := by decide
  have hdescent : baseEnd_7349132 < baseStart_7349132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349155 : List Nat := [1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6]
def baseStart_7349155 : Nat := 118140960795 + 7349155 * 2 ^ 59
def prefixEnd_7349155 : Nat := 4983230072969 + 3 ^ 40 * 7349155 * 2
def baseEnd_7349155 : Nat := 3773648919393299130964357

theorem tailTrace_7349155 : CollatzResearch.WordTrace tailWord_7349155 prefixEnd_7349155 3773648919393299130964357 := by
  unfold tailWord_7349155
  simp only [CollatzResearch.WordTrace]
  refine ⟨268045703690274045592648919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178697135793516030395099279 268045703690274045592648919)
  ·
    refine ⟨402068555535411068388973379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268045703690274045592648919 402068555535411068388973379)
    ·
      refine ⟨603102833303116602583460069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402068555535411068388973379 603102833303116602583460069)
      ·
        refine ⟨113081781244334362984398763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603102833303116602583460069 113081781244334362984398763)
        ·
          refine ⟨169622671866501544476598145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113081781244334362984398763 169622671866501544476598145)
          ·
            refine ⟨127217003899876158357448609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169622671866501544476598145 127217003899876158357448609)
            ·
              refine ⟨95412752924907118768086457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127217003899876158357448609 95412752924907118768086457)
              ·
                refine ⟨71559564693680339076064843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95412752924907118768086457 71559564693680339076064843)
                ·
                  refine ⟨107339347040520508614097265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71559564693680339076064843 107339347040520508614097265)
                  ·
                    refine ⟨80504510280390381460572949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107339347040520508614097265 80504510280390381460572949)
                    ·
                      refine ⟨3773648919393299130964357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80504510280390381460572949 3773648919393299130964357)
                      ·
                        rfl

theorem cell23_7349155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_7349155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349155 prefixEnd_7349155 := by exact prefixLift 7349155
  have htrace : WordTrace (prefixWord ++ tailWord_7349155) baseStart_7349155 baseEnd_7349155 := by
    simpa [prefixWord, tailWord_7349155, baseEnd_7349155] using wordTrace_append hprefix tailTrace_7349155
  have hstable : (prefixWord ++ tailWord_7349155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349155).length < 2 ^ (prefixWord ++ tailWord_7349155).sum := by decide
  have hdescent : baseEnd_7349155 < baseStart_7349155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349219 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 4]
def baseStart_7349219 : Nat := 118140960795 + 7349219 * 2 ^ 59
def prefixEnd_7349219 : Nat := 4983230072969 + 3 ^ 40 * 7349219 * 2
def baseEnd_7349219 : Nat := 3773681782155186880564063

theorem tailTrace_7349219 : CollatzResearch.WordTrace tailWord_7349219 prefixEnd_7349219 3773681782155186880564063 := by
  unfold tailWord_7349219
  simp only [CollatzResearch.WordTrace]
  refine ⟨268048037962042184522978711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178698691974694789681985807 268048037962042184522978711)
  ·
    refine ⟨402072056943063276784468067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268048037962042184522978711 402072056943063276784468067)
    ·
      refine ⟨603108085414594915176702101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402072056943063276784468067 603108085414594915176702101)
      ·
        refine ⟨28270691503809136648907911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 603108085414594915176702101 28270691503809136648907911)
        ·
          refine ⟨42406037255713704973361867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28270691503809136648907911 42406037255713704973361867)
          ·
            refine ⟨63609055883570557460042801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42406037255713704973361867 63609055883570557460042801)
            ·
              refine ⟨47706791912677918095032101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63609055883570557460042801 47706791912677918095032101)
              ·
                refine ⟨8945023483627109642818519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47706791912677918095032101 8945023483627109642818519)
                ·
                  refine ⟨13417535225440664464227779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945023483627109642818519 13417535225440664464227779)
                  ·
                    refine ⟨20126302838160996696341669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13417535225440664464227779 20126302838160996696341669)
                    ·
                      refine ⟨3773681782155186880564063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20126302838160996696341669 3773681782155186880564063)
                      ·
                        rfl

theorem cell23_7349219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_7349219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349219 prefixEnd_7349219 := by exact prefixLift 7349219
  have htrace : WordTrace (prefixWord ++ tailWord_7349219) baseStart_7349219 baseEnd_7349219 := by
    simpa [prefixWord, tailWord_7349219, baseEnd_7349219] using wordTrace_append hprefix tailTrace_7349219
  have hstable : (prefixWord ++ tailWord_7349219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349219).length < 2 ^ (prefixWord ++ tailWord_7349219).sum := by decide
  have hdescent : baseEnd_7349219 < baseStart_7349219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349223 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 2, 3, 2]
def baseStart_7349223 : Nat := 118140960795 + 7349223 * 2 ^ 59
def prefixEnd_7349223 : Nat := 4983230072969 + 3 ^ 40 * 7349223 * 2
def baseEnd_7349223 : Nat := 3773683836077804864914045

theorem tailTrace_7349223 : CollatzResearch.WordTrace tailWord_7349223 prefixEnd_7349223 3773683836077804864914045 := by
  unfold tailWord_7349223
  simp only [CollatzResearch.WordTrace]
  refine ⟨268048183854027693206124323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178698789236018462137416215 268048183854027693206124323)
  ·
    refine ⟨402072275781041539809186485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268048183854027693206124323 402072275781041539809186485)
    ·
      refine ⟨37694275854472644357111233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402072275781041539809186485 37694275854472644357111233)
      ·
        refine ⟨28270706890854483267833425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37694275854472644357111233 28270706890854483267833425)
        ·
          refine ⟨21203030168140862450875069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28270706890854483267833425 21203030168140862450875069)
          ·
            refine ⟨7951136313052823419078151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21203030168140862450875069 7951136313052823419078151)
            ·
              refine ⟨11926704469579235128617227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951136313052823419078151 11926704469579235128617227)
              ·
                refine ⟨17890056704368852692925841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11926704469579235128617227 17890056704368852692925841)
                ·
                  refine ⟨13417542528276639519694381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17890056704368852692925841 13417542528276639519694381)
                  ·
                    refine ⟨5031578448103739819885393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13417542528276639519694381 5031578448103739819885393)
                    ·
                      refine ⟨3773683836077804864914045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031578448103739819885393 3773683836077804864914045)
                      ·
                        rfl

theorem cell23_7349223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_7349223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349223 prefixEnd_7349223 := by exact prefixLift 7349223
  have htrace : WordTrace (prefixWord ++ tailWord_7349223) baseStart_7349223 baseEnd_7349223 := by
    simpa [prefixWord, tailWord_7349223, baseEnd_7349223] using wordTrace_append hprefix tailTrace_7349223
  have hstable : (prefixWord ++ tailWord_7349223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349223).length < 2 ^ (prefixWord ++ tailWord_7349223).sum := by decide
  have hdescent : baseEnd_7349223 < baseStart_7349223 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349230 : List Nat := [4, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_7349230 : Nat := 118140960795 + 7349230 * 2 ^ 59
def prefixEnd_7349230 : Nat := 4983230072969 + 3 ^ 40 * 7349230 * 2
def baseEnd_7349230 : Nat := 3773687430442386337526513

theorem tailTrace_7349230 : CollatzResearch.WordTrace tailWord_7349230 prefixEnd_7349230 3773687430442386337526513 := by
  unfold tailWord_7349230
  simp only [CollatzResearch.WordTrace]
  refine ⟨33506054895625291675203643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178698959443334888934419429 33506054895625291675203643)
  ·
    refine ⟨50259082343437937512805465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33506054895625291675203643 50259082343437937512805465)
    ·
      refine ⟨37694311757578453134604099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50259082343437937512805465 37694311757578453134604099)
      ·
        refine ⟨56541467636367679701906149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37694311757578453134604099 56541467636367679701906149)
        ·
          refine ⟨10601525181818939944107403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56541467636367679701906149 10601525181818939944107403)
          ·
            refine ⟨15902287772728409916161105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10601525181818939944107403 15902287772728409916161105)
            ·
              refine ⟨11926715829546307437120829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15902287772728409916161105 11926715829546307437120829)
              ·
                refine ⟨4472518436079865288920311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11926715829546307437120829 4472518436079865288920311)
                ·
                  refine ⟨6708777654119797933380467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472518436079865288920311 6708777654119797933380467)
                  ·
                    refine ⟨10063166481179696900070701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6708777654119797933380467 10063166481179696900070701)
                    ·
                      refine ⟨3773687430442386337526513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063166481179696900070701 3773687430442386337526513)
                      ·
                        rfl

theorem cell23_7349230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_7349230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349230 prefixEnd_7349230 := by exact prefixLift 7349230
  have htrace : WordTrace (prefixWord ++ tailWord_7349230) baseStart_7349230 baseEnd_7349230 := by
    simpa [prefixWord, tailWord_7349230, baseEnd_7349230] using wordTrace_append hprefix tailTrace_7349230
  have hstable : (prefixWord ++ tailWord_7349230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349230).length < 2 ^ (prefixWord ++ tailWord_7349230).sum := by decide
  have hdescent : baseEnd_7349230 < baseStart_7349230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349253 : List Nat := [1, 3, 1, 1, 2, 3, 1, 6, 1, 2, 2]
def baseStart_7349253 : Nat := 118140960795 + 7349253 * 2 ^ 59
def prefixEnd_7349253 : Nat := 4983230072969 + 3 ^ 40 * 7349253 * 2
def baseEnd_7349253 : Nat := 3773699240497439747538907

theorem tailTrace_7349253 : CollatzResearch.WordTrace tailWord_7349253 prefixEnd_7349253 3773699240497439747538907 := by
  unfold tailWord_7349253
  simp only [CollatzResearch.WordTrace]
  refine ⟨268049278043919008329716413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178699518695946005553144275 268049278043919008329716413)
  ·
    refine ⟨100518479266469628123643655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268049278043919008329716413 100518479266469628123643655)
    ·
      refine ⟨150777718899704442185465483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100518479266469628123643655 150777718899704442185465483)
      ·
        refine ⟨226166578349556663278198225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150777718899704442185465483 226166578349556663278198225)
        ·
          refine ⟨169624933762167497458648669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226166578349556663278198225 169624933762167497458648669)
          ·
            refine ⟨63609350160812811546993251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169624933762167497458648669 63609350160812811546993251)
            ·
              refine ⟨95414025241219217320489877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63609350160812811546993251 95414025241219217320489877)
              ·
                refine ⟨4472532433182150811897963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95414025241219217320489877 4472532433182150811897963)
                ·
                  refine ⟨6708798649773226217846945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472532433182150811897963 6708798649773226217846945)
                  ·
                    refine ⟨5031598987329919663385209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708798649773226217846945 5031598987329919663385209)
                    ·
                      refine ⟨3773699240497439747538907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031598987329919663385209 3773699240497439747538907)
                      ·
                        rfl

theorem cell23_7349253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_7349253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349253 prefixEnd_7349253 := by exact prefixLift 7349253
  have htrace : WordTrace (prefixWord ++ tailWord_7349253) baseStart_7349253 baseEnd_7349253 := by
    simpa [prefixWord, tailWord_7349253, baseEnd_7349253] using wordTrace_append hprefix tailTrace_7349253
  have hstable : (prefixWord ++ tailWord_7349253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349253).length < 2 ^ (prefixWord ++ tailWord_7349253).sum := by decide
  have hdescent : baseEnd_7349253 < baseStart_7349253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349276 : List Nat := [2, 2, 3, 1, 4, 2, 2, 7]
def baseStart_7349276 : Nat := 118140960795 + 7349276 * 2 ^ 59
def prefixEnd_7349276 : Nat := 4983230072969 + 3 ^ 40 * 7349276 * 2
def baseEnd_7349276 : Nat := 139767075946388635464863

theorem tailTrace_7349276 : CollatzResearch.WordTrace tailWord_7349276 prefixEnd_7349276 139767075946388635464863 := by
  unfold tailWord_7349276
  simp only [CollatzResearch.WordTrace]
  refine ⟨134025058461417841628901841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178700077948557122171869121 134025058461417841628901841)
  ·
    refine ⟨100518793846063381221676381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134025058461417841628901841 100518793846063381221676381)
    ·
      refine ⟨37694547692273767958128643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100518793846063381221676381 37694547692273767958128643)
      ·
        refine ⟨56541821538410651937192965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37694547692273767958128643 56541821538410651937192965)
        ·
          refine ⟨10601591538451997238223681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56541821538410651937192965 10601591538451997238223681)
          ·
            refine ⟨7951193653838997928667761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10601591538451997238223681 7951193653838997928667761)
            ·
              refine ⟨5963395240379248446500821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951193653838997928667761 5963395240379248446500821)
              ·
                refine ⟨139767075946388635464863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5963395240379248446500821 139767075946388635464863)
                ·
                  rfl

theorem cell23_7349276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 7].length) (baseStart_7349276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349276 prefixEnd_7349276 := by exact prefixLift 7349276
  have htrace : WordTrace (prefixWord ++ tailWord_7349276) baseStart_7349276 baseEnd_7349276 := by
    simpa [prefixWord, tailWord_7349276, baseEnd_7349276] using wordTrace_append hprefix tailTrace_7349276
  have hstable : (prefixWord ++ tailWord_7349276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349276).length < 2 ^ (prefixWord ++ tailWord_7349276).sum := by decide
  have hdescent : baseEnd_7349276 < baseStart_7349276 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349287 : List Nat := [1, 1, 7, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7349287 : Nat := 118140960795 + 7349287 * 2 ^ 59
def prefixEnd_7349287 : Nat := 4983230072969 + 3 ^ 40 * 7349287 * 2
def baseEnd_7349287 : Nat := 3773716698839692614513751

theorem tailTrace_7349287 : CollatzResearch.WordTrace tailWord_7349287 prefixEnd_7349287 3773716698839692614513751 := by
  unfold tailWord_7349287
  simp only [CollatzResearch.WordTrace]
  refine ⟨268050518125795832136454115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178700345417197221424302743 268050518125795832136454115)
  ·
    refine ⟨402075777188693748204681173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268050518125795832136454115 402075777188693748204681173)
    ·
      refine ⟨9423651027860009723547215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 402075777188693748204681173 9423651027860009723547215)
      ·
        refine ⟨14135476541790014585320823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9423651027860009723547215 14135476541790014585320823)
        ·
          refine ⟨21203214812685021877981235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135476541790014585320823 21203214812685021877981235)
          ·
            refine ⟨31804822219027532816971853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21203214812685021877981235 31804822219027532816971853)
            ·
              refine ⟨11926808332135324806364445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31804822219027532816971853 11926808332135324806364445)
              ·
                refine ⟨4472553124550746802386667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11926808332135324806364445 4472553124550746802386667)
                ·
                  refine ⟨6708829686826120203580001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472553124550746802386667 6708829686826120203580001)
                  ·
                    refine ⟨5031622265119590152685001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6708829686826120203580001 5031622265119590152685001)
                    ·
                      refine ⟨3773716698839692614513751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031622265119590152685001 3773716698839692614513751)
                      ·
                        rfl

theorem cell23_7349287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7349287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349287 prefixEnd_7349287 := by exact prefixLift 7349287
  have htrace : WordTrace (prefixWord ++ tailWord_7349287) baseStart_7349287 baseEnd_7349287 := by
    simpa [prefixWord, tailWord_7349287, baseEnd_7349287] using wordTrace_append hprefix tailTrace_7349287
  have hstable : (prefixWord ++ tailWord_7349287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349287).length < 2 ^ (prefixWord ++ tailWord_7349287).sum := by decide
  have hdescent : baseEnd_7349287 < baseStart_7349287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349296 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2]
def baseStart_7349296 : Nat := 118140960795 + 7349296 * 2 ^ 59
def prefixEnd_7349296 : Nat := 4983230072969 + 3 ^ 40 * 7349296 * 2
def baseEnd_7349296 : Nat := 3773721320165583079301209

theorem tailTrace_7349296 : CollatzResearch.WordTrace tailWord_7349296 prefixEnd_7349296 3773721320165583079301209 := by
  unfold tailWord_7349296
  simp only [CollatzResearch.WordTrace]
  refine ⟨134025423191381613336765871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178700564255175484449021161 134025423191381613336765871)
  ·
    refine ⟨201038134787072420005148807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134025423191381613336765871 201038134787072420005148807)
    ·
      refine ⟨301557202180608630007723211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201038134787072420005148807 301557202180608630007723211)
      ·
        refine ⟨452335803270912945011584817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301557202180608630007723211 452335803270912945011584817)
        ·
          refine ⟨339251852453184708758688613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452335803270912945011584817 339251852453184708758688613)
          ·
            refine ⟨63609722334972132892254115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 339251852453184708758688613 63609722334972132892254115)
            ·
              refine ⟨95414583502458199338381173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63609722334972132892254115 95414583502458199338381173)
              ·
                refine ⟨8945117203355456187973235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95414583502458199338381173 8945117203355456187973235)
                ·
                  refine ⟨13417675805033184281959853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945117203355456187973235 13417675805033184281959853)
                  ·
                    refine ⟨5031628426887444105734945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13417675805033184281959853 5031628426887444105734945)
                    ·
                      refine ⟨3773721320165583079301209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031628426887444105734945 3773721320165583079301209)
                      ·
                        rfl

theorem cell23_7349296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2].length) (baseStart_7349296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349296 prefixEnd_7349296 := by exact prefixLift 7349296
  have htrace : WordTrace (prefixWord ++ tailWord_7349296) baseStart_7349296 baseEnd_7349296 := by
    simpa [prefixWord, tailWord_7349296, baseEnd_7349296] using wordTrace_append hprefix tailTrace_7349296
  have hstable : (prefixWord ++ tailWord_7349296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349296).length < 2 ^ (prefixWord ++ tailWord_7349296).sum := by decide
  have hdescent : baseEnd_7349296 < baseStart_7349296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349312 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_7349312 : Nat := 118140960795 + 7349312 * 2 ^ 59
def prefixEnd_7349312 : Nat := 4983230072969 + 3 ^ 40 * 7349312 * 2
def baseEnd_7349312 : Nat := 3773729535856055016701135

theorem tailTrace_7349312 : CollatzResearch.WordTrace tailWord_7349312 prefixEnd_7349312 3773729535856055016701135 := by
  unfold tailWord_7349312
  simp only [CollatzResearch.WordTrace]
  refine ⟨134025714975352630703057095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178700953300470174270742793 134025714975352630703057095)
  ·
    refine ⟨201038572463028946054585643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134025714975352630703057095 201038572463028946054585643)
    ·
      refine ⟨301557858694543419081878465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201038572463028946054585643 301557858694543419081878465)
      ·
        refine ⟨226168394020907564311408849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301557858694543419081878465 226168394020907564311408849)
        ·
          refine ⟨169626295515680673233556637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226168394020907564311408849 169626295515680673233556637)
          ·
            refine ⟨63609860818380252462583739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169626295515680673233556637 63609860818380252462583739)
            ·
              refine ⟨95414791227570378693875609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63609860818380252462583739 95414791227570378693875609)
              ·
                refine ⟨71561093420677784020406707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95414791227570378693875609 71561093420677784020406707)
                ·
                  refine ⟨107341640131016676030610061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71561093420677784020406707 107341640131016676030610061)
                  ·
                    refine ⟨40253115049131253511478773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107341640131016676030610061 40253115049131253511478773)
                    ·
                      refine ⟨3773729535856055016701135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40253115049131253511478773 3773729535856055016701135)
                      ·
                        rfl

theorem cell23_7349312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_7349312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349312 prefixEnd_7349312 := by exact prefixLift 7349312
  have htrace : WordTrace (prefixWord ++ tailWord_7349312) baseStart_7349312 baseEnd_7349312 := by
    simpa [prefixWord, tailWord_7349312, baseEnd_7349312] using wordTrace_append hprefix tailTrace_7349312
  have hstable : (prefixWord ++ tailWord_7349312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349312).length < 2 ^ (prefixWord ++ tailWord_7349312).sum := by decide
  have hdescent : baseEnd_7349312 < baseStart_7349312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349326 : List Nat := [4, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_7349326 : Nat := 118140960795 + 7349326 * 2 ^ 59
def prefixEnd_7349326 : Nat := 4983230072969 + 3 ^ 40 * 7349326 * 2
def baseEnd_7349326 : Nat := 3773736724585217961926071

theorem tailTrace_7349326 : CollatzResearch.WordTrace tailWord_7349326 prefixEnd_7349326 3773736724585217961926071 := by
  unfold tailWord_7349326
  simp only [CollatzResearch.WordTrace]
  refine ⟨33506492571581817724640479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178701293715103027864749221 33506492571581817724640479)
  ·
    refine ⟨50259738857372726586960719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33506492571581817724640479 50259738857372726586960719)
    ·
      refine ⟨75389608286059089880441079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50259738857372726586960719 75389608286059089880441079)
      ·
        refine ⟨113084412429088634820661619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75389608286059089880441079 113084412429088634820661619)
        ·
          refine ⟨169626618643632952230992429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113084412429088634820661619 169626618643632952230992429)
          ·
            refine ⟨63609981991362357086622161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169626618643632952230992429 63609981991362357086622161)
            ·
              refine ⟨47707486493521767814966621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63609981991362357086622161 47707486493521767814966621)
              ·
                refine ⟨17890307435070662930612483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47707486493521767814966621 17890307435070662930612483)
                ·
                  refine ⟨26835461152605994395918725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17890307435070662930612483 26835461152605994395918725)
                  ·
                    refine ⟨5031648966113623949234761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26835461152605994395918725 5031648966113623949234761)
                    ·
                      refine ⟨3773736724585217961926071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031648966113623949234761 3773736724585217961926071)
                      ·
                        rfl

theorem cell23_7349326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_7349326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349326 prefixEnd_7349326 := by exact prefixLift 7349326
  have htrace : WordTrace (prefixWord ++ tailWord_7349326) baseStart_7349326 baseEnd_7349326 := by
    simpa [prefixWord, tailWord_7349326, baseEnd_7349326] using wordTrace_append hprefix tailTrace_7349326
  have hstable : (prefixWord ++ tailWord_7349326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349326).length < 2 ^ (prefixWord ++ tailWord_7349326).sum := by decide
  have hdescent : baseEnd_7349326 < baseStart_7349326 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349330 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 1, 3, 2]
def baseStart_7349330 : Nat := 118140960795 + 7349330 * 2 ^ 59
def prefixEnd_7349330 : Nat := 4983230072969 + 3 ^ 40 * 7349330 * 2
def baseEnd_7349330 : Nat := 3773738778507835946276053

theorem tailTrace_7349330 : CollatzResearch.WordTrace tailWord_7349330 prefixEnd_7349330 3773738778507835946276053 := by
  unfold tailWord_7349330
  simp only [CollatzResearch.WordTrace]
  refine ⟨67013021616160012620067361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178701390976426700320179629 67013021616160012620067361)
  ·
    refine ⟨50259766212120009465050521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67013021616160012620067361 50259766212120009465050521)
    ·
      refine ⟨37694824659090007098787891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50259766212120009465050521 37694824659090007098787891)
      ·
        refine ⟨56542236988635010648181837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37694824659090007098787891 56542236988635010648181837)
        ·
          refine ⟨21203338870738128993068189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56542236988635010648181837 21203338870738128993068189)
          ·
            refine ⟨7951252076526798372400571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21203338870738128993068189 7951252076526798372400571)
            ·
              refine ⟨11926878114790197558600857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951252076526798372400571 11926878114790197558600857)
              ·
                refine ⟨8945158586092648168950643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11926878114790197558600857 8945158586092648168950643)
                ·
                  refine ⟨13417737879138972253425965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945158586092648168950643 13417737879138972253425965)
                  ·
                    refine ⟨5031651704677114595034737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13417737879138972253425965 5031651704677114595034737)
                    ·
                      refine ⟨3773738778507835946276053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031651704677114595034737 3773738778507835946276053)
                      ·
                        rfl

theorem cell23_7349330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_7349330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349330 prefixEnd_7349330 := by exact prefixLift 7349330
  have htrace : WordTrace (prefixWord ++ tailWord_7349330) baseStart_7349330 baseEnd_7349330 := by
    simpa [prefixWord, tailWord_7349330, baseEnd_7349330] using wordTrace_append hprefix tailTrace_7349330
  have hstable : (prefixWord ++ tailWord_7349330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349330).length < 2 ^ (prefixWord ++ tailWord_7349330).sum := by decide
  have hdescent : baseEnd_7349330 < baseStart_7349330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349346 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_7349346 : Nat := 118140960795 + 7349346 * 2 ^ 59
def prefixEnd_7349346 : Nat := 4983230072969 + 3 ^ 40 * 7349346 * 2
def baseEnd_7349346 : Nat := 3773746994198307883675979

theorem tailTrace_7349346 : CollatzResearch.WordTrace tailWord_7349346 prefixEnd_7349346 3773746994198307883675979 := by
  unfold tailWord_7349346
  simp only [CollatzResearch.WordTrace]
  refine ⟨67013167508145521303212973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178701780021721390141901261 67013167508145521303212973)
  ·
    refine ⟨25129937815554570488704865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67013167508145521303212973 25129937815554570488704865)
    ·
      refine ⟨18847453361665927866528649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25129937815554570488704865 18847453361665927866528649)
      ·
        refine ⟨14135590021249445899896487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18847453361665927866528649 14135590021249445899896487)
        ·
          refine ⟨21203385031874168849844731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135590021249445899896487 21203385031874168849844731)
          ·
            refine ⟨31805077547811253274767097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21203385031874168849844731 31805077547811253274767097)
            ·
              refine ⟨23853808160858439956075323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31805077547811253274767097 23853808160858439956075323)
              ·
                refine ⟨35780712241287659934112985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23853808160858439956075323 35780712241287659934112985)
                ·
                  refine ⟨26835534180965744950584739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35780712241287659934112985 26835534180965744950584739)
                  ·
                    refine ⟨40253301271448617425877109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26835534180965744950584739 40253301271448617425877109)
                    ·
                      refine ⟨3773746994198307883675979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40253301271448617425877109 3773746994198307883675979)
                      ·
                        rfl

theorem cell23_7349346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_7349346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349346 prefixEnd_7349346 := by exact prefixLift 7349346
  have htrace : WordTrace (prefixWord ++ tailWord_7349346) baseStart_7349346 baseEnd_7349346 := by
    simpa [prefixWord, tailWord_7349346, baseEnd_7349346] using wordTrace_append hprefix tailTrace_7349346
  have hstable : (prefixWord ++ tailWord_7349346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349346).length < 2 ^ (prefixWord ++ tailWord_7349346).sum := by decide
  have hdescent : baseEnd_7349346 < baseStart_7349346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349359 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3]
def baseStart_7349359 : Nat := 118140960795 + 7349359 * 2 ^ 59
def prefixEnd_7349359 : Nat := 4983230072969 + 3 ^ 40 * 7349359 * 2
def baseEnd_7349359 : Nat := 3773753669446816332813419

theorem tailTrace_7349359 : CollatzResearch.WordTrace tailWord_7349359 prefixEnd_7349359 3773753669446816332813419 := by
  unfold tailWord_7349359
  simp only [CollatzResearch.WordTrace]
  refine ⟨268053144181534988433075131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178702096121023325622050087 268053144181534988433075131)
  ·
    refine ⟨402079716272302482649612697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268053144181534988433075131 402079716272302482649612697)
    ·
      refine ⟨301559787204226861987209523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402079716272302482649612697 301559787204226861987209523)
      ·
        refine ⟨452339680806340292980814285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301559787204226861987209523 452339680806340292980814285)
        ·
          refine ⟨169627380302377609867805357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452339680806340292980814285 169627380302377609867805357)
          ·
            refine ⟨63610267613391603700427009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169627380302377609867805357 63610267613391603700427009)
            ·
              refine ⟨47707700710043702775320257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63610267613391603700427009 47707700710043702775320257)
              ·
                refine ⟨35780775532532777081490193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47707700710043702775320257 35780775532532777081490193)
                ·
                  refine ⟨26835581649399582811117645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35780775532532777081490193 26835581649399582811117645)
                  ·
                    refine ⟨10063343118524843554169117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26835581649399582811117645 10063343118524843554169117)
                    ·
                      refine ⟨3773753669446816332813419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063343118524843554169117 3773753669446816332813419)
                      ·
                        rfl

theorem cell23_7349359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 3].length) (baseStart_7349359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349359 prefixEnd_7349359 := by exact prefixLift 7349359
  have htrace : WordTrace (prefixWord ++ tailWord_7349359) baseStart_7349359 baseEnd_7349359 := by
    simpa [prefixWord, tailWord_7349359, baseEnd_7349359] using wordTrace_append hprefix tailTrace_7349359
  have hstable : (prefixWord ++ tailWord_7349359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349359).length < 2 ^ (prefixWord ++ tailWord_7349359).sum := by decide
  have hdescent : baseEnd_7349359 < baseStart_7349359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349386 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_7349386 : Nat := 118140960795 + 7349386 * 2 ^ 59
def prefixEnd_7349386 : Nat := 4983230072969 + 3 ^ 40 * 7349386 * 2
def baseEnd_7349386 : Nat := 3773767533424487727175795

theorem tailTrace_7349386 : CollatzResearch.WordTrace tailWord_7349386 prefixEnd_7349386 3773767533424487727175795 := by
  unfold tailWord_7349386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67013532238109293011077003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178702752634958114696205341 67013532238109293011077003)
  ·
    refine ⟨100520298357163939516615505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67013532238109293011077003 100520298357163939516615505)
    ·
      refine ⟨75390223767872954637461629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100520298357163939516615505 75390223767872954637461629)
      ·
        refine ⟨28271333912952357989048111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75390223767872954637461629 28271333912952357989048111)
        ·
          refine ⟨42407000869428536983572167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28271333912952357989048111 42407000869428536983572167)
          ·
            refine ⟨63610501304142805475358251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42407000869428536983572167 63610501304142805475358251)
            ·
              refine ⟨95415751956214208213037377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63610501304142805475358251 95415751956214208213037377)
              ·
                refine ⟨71561813967160656159778033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95415751956214208213037377 71561813967160656159778033)
                ·
                  refine ⟨53671360475370492119833525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71561813967160656159778033 53671360475370492119833525)
                  ·
                    refine ⟨5031690044565983636234393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53671360475370492119833525 5031690044565983636234393)
                    ·
                      refine ⟨3773767533424487727175795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031690044565983636234393 3773767533424487727175795)
                      ·
                        rfl

theorem cell23_7349386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_7349386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349386 prefixEnd_7349386 := by exact prefixLift 7349386
  have htrace : WordTrace (prefixWord ++ tailWord_7349386) baseStart_7349386 baseEnd_7349386 := by
    simpa [prefixWord, tailWord_7349386, baseEnd_7349386] using wordTrace_append hprefix tailTrace_7349386
  have hstable : (prefixWord ++ tailWord_7349386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349386).length < 2 ^ (prefixWord ++ tailWord_7349386).sum := by decide
  have hdescent : baseEnd_7349386 < baseStart_7349386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349392 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 1, 10]
def baseStart_7349392 : Nat := 118140960795 + 7349392 * 2 ^ 59
def prefixEnd_7349392 : Nat := 4983230072969 + 3 ^ 40 * 7349392 * 2
def baseEnd_7349392 : Nat := 1257923538102804901233589

theorem tailTrace_7349392 : CollatzResearch.WordTrace tailWord_7349392 prefixEnd_7349392 1257923538102804901233589 := by
  unfold tailWord_7349392
  simp only [CollatzResearch.WordTrace]
  refine ⟨134027173895207717534513215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178702898526943623379350953 134027173895207717534513215)
  ·
    refine ⟨201040760842811576301769823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134027173895207717534513215 201040760842811576301769823)
    ·
      refine ⟨301561141264217364452654735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201040760842811576301769823 301561141264217364452654735)
      ·
        refine ⟨452341711896326046678982103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301561141264217364452654735 452341711896326046678982103)
        ·
          refine ⟨678512567844489070018473155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452341711896326046678982103 678512567844489070018473155)
          ·
            refine ⟨1017768851766733605027709733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678512567844489070018473155 1017768851766733605027709733)
            ·
              refine ⟨190831659706262550942695575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1017768851766733605027709733 190831659706262550942695575)
              ·
                refine ⟨286247489559393826414043363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190831659706262550942695575 286247489559393826414043363)
                ·
                  refine ⟨429371234339090739621065045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 286247489559393826414043363 429371234339090739621065045)
                  ·
                    refine ⟨1257923538102804901233589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 429371234339090739621065045 1257923538102804901233589)
                    ·
                      rfl

theorem cell23_7349392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_7349392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349392 prefixEnd_7349392 := by exact prefixLift 7349392
  have htrace : WordTrace (prefixWord ++ tailWord_7349392) baseStart_7349392 baseEnd_7349392 := by
    simpa [prefixWord, tailWord_7349392, baseEnd_7349392] using wordTrace_append hprefix tailTrace_7349392
  have hstable : (prefixWord ++ tailWord_7349392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349392).length < 2 ^ (prefixWord ++ tailWord_7349392).sum := by decide
  have hdescent : baseEnd_7349392 < baseStart_7349392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349426 : List Nat := [3, 2, 1, 1, 1, 4, 1, 3, 3, 4]
def baseStart_7349426 : Nat := 118140960795 + 7349426 * 2 ^ 59
def prefixEnd_7349426 : Nat := 4983230072969 + 3 ^ 40 * 7349426 * 2
def baseEnd_7349426 : Nat := 1257929357550222523558537

theorem tailTrace_7349426 : CollatzResearch.WordTrace tailWord_7349426 prefixEnd_7349426 1257929357550222523558537 := by
  unfold tailWord_7349426
  simp only [CollatzResearch.WordTrace]
  refine ⟨67013896968073064718941033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178703725248194839250509421 67013896968073064718941033)
  ·
    refine ⟨50260422726054798539205775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67013896968073064718941033 50260422726054798539205775)
    ·
      refine ⟨75390634089082197808808663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50260422726054798539205775 75390634089082197808808663)
      ·
        refine ⟨113085951133623296713212995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75390634089082197808808663 113085951133623296713212995)
        ·
          refine ⟨169628926700434945069819493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113085951133623296713212995 169628926700434945069819493)
          ·
            refine ⟨31805423756331552200591155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169628926700434945069819493 31805423756331552200591155)
            ·
              refine ⟨47708135634497328300886733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31805423756331552200591155 47708135634497328300886733)
              ·
                refine ⟨17890550862936498112832525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47708135634497328300886733 17890550862936498112832525)
                ·
                  refine ⟨6708956573601186792312197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17890550862936498112832525 6708956573601186792312197)
                  ·
                    refine ⟨1257929357550222523558537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6708956573601186792312197 1257929357550222523558537)
                    ·
                      rfl

theorem cell23_7349426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_7349426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349426 prefixEnd_7349426 := by exact prefixLift 7349426
  have htrace : WordTrace (prefixWord ++ tailWord_7349426) baseStart_7349426 baseEnd_7349426 := by
    simpa [prefixWord, tailWord_7349426, baseEnd_7349426] using wordTrace_append hprefix tailTrace_7349426
  have hstable : (prefixWord ++ tailWord_7349426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349426).length < 2 ^ (prefixWord ++ tailWord_7349426).sum := by decide
  have hdescent : baseEnd_7349426 < baseStart_7349426 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349436 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_7349436 : Nat := 118140960795 + 7349436 * 2 ^ 59
def prefixEnd_7349436 : Nat := 4983230072969 + 3 ^ 40 * 7349436 * 2
def baseEnd_7349436 : Nat := 3773793207457212531550565

theorem tailTrace_7349436 : CollatzResearch.WordTrace tailWord_7349436 prefixEnd_7349436 3773793207457212531550565 := by
  unfold tailWord_7349436
  simp only [CollatzResearch.WordTrace]
  refine ⟨134027976301128015291814081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178703968401504020389085441 134027976301128015291814081)
  ·
    refine ⟨100520982225846011468860561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134027976301128015291814081 100520982225846011468860561)
    ·
      refine ⟨75390736669384508601645421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100520982225846011468860561 75390736669384508601645421)
      ·
        refine ⟨28271526251019190725617033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75390736669384508601645421 28271526251019190725617033)
        ·
          refine ⟨21203644688264393044212775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28271526251019190725617033 21203644688264393044212775)
          ·
            refine ⟨31805467032396589566319163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21203644688264393044212775 31805467032396589566319163)
            ·
              refine ⟨47708200548594884349478745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31805467032396589566319163 47708200548594884349478745)
              ·
                refine ⟨35781150411446163262109059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47708200548594884349478745 35781150411446163262109059)
                ·
                  refine ⟨53671725617169244893163589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35781150411446163262109059 53671725617169244893163589)
                  ·
                    refine ⟨10063448553219233417468173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53671725617169244893163589 10063448553219233417468173)
                    ·
                      refine ⟨3773793207457212531550565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063448553219233417468173 3773793207457212531550565)
                      ·
                        rfl

theorem cell23_7349436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_7349436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349436 prefixEnd_7349436 := by exact prefixLift 7349436
  have htrace : WordTrace (prefixWord ++ tailWord_7349436) baseStart_7349436 baseEnd_7349436 := by
    simpa [prefixWord, tailWord_7349436, baseEnd_7349436] using wordTrace_append hprefix tailTrace_7349436
  have hstable : (prefixWord ++ tailWord_7349436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349436).length < 2 ^ (prefixWord ++ tailWord_7349436).sum := by decide
  have hdescent : baseEnd_7349436 < baseStart_7349436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349439 : List Nat := [1, 1, 2, 2, 2, 2, 2, 5, 6]
def baseStart_7349439 : Nat := 118140960795 + 7349439 * 2 ^ 59
def prefixEnd_7349439 : Nat := 4983230072969 + 3 ^ 40 * 7349439 * 2
def baseEnd_7349439 : Nat := 419310527544352891090339

theorem tailTrace_7349439 : CollatzResearch.WordTrace tailWord_7349439 prefixEnd_7349439 419310527544352891090339 := by
  unfold tailWord_7349439
  simp only [CollatzResearch.WordTrace]
  refine ⟨268056062021245162095987371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178704041347496774730658247 268056062021245162095987371)
  ·
    refine ⟨402084093031867743143981057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268056062021245162095987371 402084093031867743143981057)
    ·
      refine ⟨301563069773900807357985793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402084093031867743143981057 301563069773900807357985793)
      ·
        refine ⟨226172302330425605518489345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301563069773900807357985793 226172302330425605518489345)
        ·
          refine ⟨169629226747819204138867009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226172302330425605518489345 169629226747819204138867009)
          ·
            refine ⟨127221920060864403104150257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169629226747819204138867009 127221920060864403104150257)
            ·
              refine ⟨95416440045648302328112693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127221920060864403104150257 95416440045648302328112693)
              ·
                refine ⟨8945291254279528343260565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95416440045648302328112693 8945291254279528343260565)
                ·
                  refine ⟨419310527544352891090339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8945291254279528343260565 419310527544352891090339)
                  ·
                    rfl

theorem cell23_7349439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 6].length) (baseStart_7349439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349439 prefixEnd_7349439 := by exact prefixLift 7349439
  have htrace : WordTrace (prefixWord ++ tailWord_7349439) baseStart_7349439 baseEnd_7349439 := by
    simpa [prefixWord, tailWord_7349439, baseEnd_7349439] using wordTrace_append hprefix tailTrace_7349439
  have hstable : (prefixWord ++ tailWord_7349439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349439).length < 2 ^ (prefixWord ++ tailWord_7349439).sum := by decide
  have hdescent : baseEnd_7349439 < baseStart_7349439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349477 : List Nat := [1, 3, 1, 4, 3, 1, 3, 2, 1, 4]
def baseStart_7349477 : Nat := 118140960795 + 7349477 * 2 ^ 59
def prefixEnd_7349477 : Nat := 4983230072969 + 3 ^ 40 * 7349477 * 2
def baseEnd_7349477 : Nat := 1257938086721348957045959

theorem tailTrace_7349477 : CollatzResearch.WordTrace tailWord_7349477 prefixEnd_7349477 1257938086721348957045959 := by
  unfold tailWord_7349477
  simp only [CollatzResearch.WordTrace]
  refine ⟨268057447995107494585870685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178704965330071663057247123 268057447995107494585870685)
  ·
    refine ⟨100521542998165310469701507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268057447995107494585870685 100521542998165310469701507)
    ·
      refine ⟨150782314497247965704552261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100521542998165310469701507 150782314497247965704552261)
      ·
        refine ⟨28271683968233993569603549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150782314497247965704552261 28271683968233993569603549)
        ·
          refine ⟨10601881488087747588601331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28271683968233993569603549 10601881488087747588601331)
          ·
            refine ⟨15902822232131621382901997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10601881488087747588601331 15902822232131621382901997)
            ·
              refine ⟨5963558337049358018588249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15902822232131621382901997 5963558337049358018588249)
              ·
                refine ⟨4472668752787018513941187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5963558337049358018588249 4472668752787018513941187)
                ·
                  refine ⟨6709003129180527770911781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472668752787018513941187 6709003129180527770911781)
                  ·
                    refine ⟨1257938086721348957045959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709003129180527770911781 1257938086721348957045959)
                    ·
                      rfl

theorem cell23_7349477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_7349477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349477 prefixEnd_7349477 := by exact prefixLift 7349477
  have htrace : WordTrace (prefixWord ++ tailWord_7349477) baseStart_7349477 baseEnd_7349477 := by
    simpa [prefixWord, tailWord_7349477, baseEnd_7349477] using wordTrace_append hprefix tailTrace_7349477
  have hstable : (prefixWord ++ tailWord_7349477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349477).length < 2 ^ (prefixWord ++ tailWord_7349477).sum := by decide
  have hdescent : baseEnd_7349477 < baseStart_7349477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349483 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 3]
def baseStart_7349483 : Nat := 118140960795 + 7349483 * 2 ^ 59
def prefixEnd_7349483 : Nat := 4983230072969 + 3 ^ 40 * 7349483 * 2
def baseEnd_7349483 : Nat := 3773817341047973847662849

theorem tailTrace_7349483 : CollatzResearch.WordTrace tailWord_7349483 prefixEnd_7349483 3773817341047973847662849 := by
  unfold tailWord_7349483
  simp only [CollatzResearch.WordTrace]
  refine ⟨268057666833085757610589103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178705111222057171740392735 268057666833085757610589103)
  ·
    refine ⟨402086500249628636415883655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268057666833085757610589103 402086500249628636415883655)
    ·
      refine ⟨603129750374442954623825483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402086500249628636415883655 603129750374442954623825483)
      ·
        refine ⟨904694625561664431935738225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603129750374442954623825483 904694625561664431935738225)
        ·
          refine ⟨678520969171248323951803669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904694625561664431935738225 678520969171248323951803669)
          ·
            refine ⟨31805670429902265185240797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 678520969171248323951803669 31805670429902265185240797)
            ·
              refine ⟨11927126411213349444465299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31805670429902265185240797 11927126411213349444465299)
              ·
                refine ⟨17890689616820024166697949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11927126411213349444465299 17890689616820024166697949)
                ·
                  refine ⟨6709008606307509062511731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17890689616820024166697949 6709008606307509062511731)
                  ·
                    refine ⟨10063512909461263593767597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709008606307509062511731 10063512909461263593767597)
                    ·
                      refine ⟨3773817341047973847662849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063512909461263593767597 3773817341047973847662849)
                      ·
                        rfl

theorem cell23_7349483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 3, 1, 3].length) (baseStart_7349483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349483 prefixEnd_7349483 := by exact prefixLift 7349483
  have htrace : WordTrace (prefixWord ++ tailWord_7349483) baseStart_7349483 baseEnd_7349483 := by
    simpa [prefixWord, tailWord_7349483, baseEnd_7349483] using wordTrace_append hprefix tailTrace_7349483
  have hstable : (prefixWord ++ tailWord_7349483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349483).length < 2 ^ (prefixWord ++ tailWord_7349483).sum := by decide
  have hdescent : baseEnd_7349483 < baseStart_7349483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349489 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 4]
def baseStart_7349489 : Nat := 118140960795 + 7349489 * 2 ^ 59
def prefixEnd_7349489 : Nat := 4983230072969 + 3 ^ 40 * 7349489 * 2
def baseEnd_7349489 : Nat := 3773820421931900824187821

theorem tailTrace_7349489 : CollatzResearch.WordTrace tailWord_7349489 prefixEnd_7349489 3773820421931900824187821 := by
  unfold tailWord_7349489
  simp only [CollatzResearch.WordTrace]
  refine ⟨268057885671064020635307521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178705257114042680423538347 268057885671064020635307521)
  ·
    refine ⟨201043414253298015476480641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268057885671064020635307521 201043414253298015476480641)
    ·
      refine ⟨150782560689973511607360481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201043414253298015476480641 150782560689973511607360481)
      ·
        refine ⟨113086920517480133705520361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150782560689973511607360481 113086920517480133705520361)
        ·
          refine ⟨84815190388110100279140271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113086920517480133705520361 84815190388110100279140271)
          ·
            refine ⟨127222785582165150418710407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84815190388110100279140271 127222785582165150418710407)
            ·
              refine ⟨190834178373247725628065611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127222785582165150418710407 190834178373247725628065611)
              ·
                refine ⟨286251267559871588442098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190834178373247725628065611 286251267559871588442098417)
                ·
                  refine ⟨214688450669903691331573813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 286251267559871588442098417 214688450669903691331573813)
                  ·
                    refine ⟨20127042250303471062335045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214688450669903691331573813 20127042250303471062335045)
                    ·
                      refine ⟨3773820421931900824187821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20127042250303471062335045 3773820421931900824187821)
                      ·
                        rfl

theorem cell23_7349489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_7349489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349489 prefixEnd_7349489 := by exact prefixLift 7349489
  have htrace : WordTrace (prefixWord ++ tailWord_7349489) baseStart_7349489 baseEnd_7349489 := by
    simpa [prefixWord, tailWord_7349489, baseEnd_7349489] using wordTrace_append hprefix tailTrace_7349489
  have hstable : (prefixWord ++ tailWord_7349489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349489).length < 2 ^ (prefixWord ++ tailWord_7349489).sum := by decide
  have hdescent : baseEnd_7349489 < baseStart_7349489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349490 : List Nat := [3, 2, 1, 3, 3, 2, 2, 1, 6]
def baseStart_7349490 : Nat := 118140960795 + 7349490 * 2 ^ 59
def prefixEnd_7349490 : Nat := 4983230072969 + 3 ^ 40 * 7349490 * 2
def baseEnd_7349490 : Nat := 419313437268061702252813

theorem tailTrace_7349490 : CollatzResearch.WordTrace tailWord_7349490 prefixEnd_7349490 419313437268061702252813 := by
  unfold tailWord_7349490
  simp only [CollatzResearch.WordTrace]
  refine ⟨67014480536015099451523481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178705281429373598537395949 67014480536015099451523481)
  ·
    refine ⟨50260860402011324588642611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67014480536015099451523481 50260860402011324588642611)
    ·
      refine ⟨75391290603016986882963917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50260860402011324588642611 75391290603016986882963917)
      ·
        refine ⟨28271733976131370081111469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75391290603016986882963917 28271733976131370081111469)
        ·
          refine ⟨10601900241049263780416801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28271733976131370081111469 10601900241049263780416801)
          ·
            refine ⟨7951425180786947835312601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10601900241049263780416801 7951425180786947835312601)
            ·
              refine ⟨5963568885590210876484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951425180786947835312601 5963568885590210876484451)
              ·
                refine ⟨8945353328385316314726677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963568885590210876484451 8945353328385316314726677)
                ·
                  refine ⟨419313437268061702252813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8945353328385316314726677 419313437268061702252813)
                  ·
                    rfl

theorem cell23_7349490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 6].length) (baseStart_7349490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349490 prefixEnd_7349490 := by exact prefixLift 7349490
  have htrace : WordTrace (prefixWord ++ tailWord_7349490) baseStart_7349490 baseEnd_7349490 := by
    simpa [prefixWord, tailWord_7349490, baseEnd_7349490] using wordTrace_append hprefix tailTrace_7349490
  have hstable : (prefixWord ++ tailWord_7349490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349490).length < 2 ^ (prefixWord ++ tailWord_7349490).sum := by decide
  have hdescent : baseEnd_7349490 < baseStart_7349490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349503 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 1, 5]
def baseStart_7349503 : Nat := 118140960795 + 7349503 * 2 ^ 59
def prefixEnd_7349503 : Nat := 4983230072969 + 3 ^ 40 * 7349503 * 2
def baseEnd_7349503 : Nat := 1257942536887021256470919

theorem tailTrace_7349503 : CollatzResearch.WordTrace tailWord_7349503 prefixEnd_7349503 1257942536887021256470919 := by
  unfold tailWord_7349503
  simp only [CollatzResearch.WordTrace]
  refine ⟨268058396293013301026317163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178705597528675534017544775 268058396293013301026317163)
  ·
    refine ⟨402087594439519951539475745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268058396293013301026317163 402087594439519951539475745)
    ·
      refine ⟨301565695829639963654606809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402087594439519951539475745 301565695829639963654606809)
      ·
        refine ⟨226174271872229972740955107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301565695829639963654606809 226174271872229972740955107)
        ·
          refine ⟨339261407808344959111432661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226174271872229972740955107 339261407808344959111432661)
          ·
            refine ⟨7951439245508084979174203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 339261407808344959111432661 7951439245508084979174203)
            ·
              refine ⟨11927158868262127468761305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951439245508084979174203 11927158868262127468761305)
              ·
                refine ⟨8945369151196595601570979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11927158868262127468761305 8945369151196595601570979)
                ·
                  refine ⟨13418053726794893402356469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945369151196595601570979 13418053726794893402356469)
                  ·
                    refine ⟨1257942536887021256470919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13418053726794893402356469 1257942536887021256470919)
                    ·
                      rfl

theorem cell23_7349503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 5].length) (baseStart_7349503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349503 prefixEnd_7349503 := by exact prefixLift 7349503
  have htrace : WordTrace (prefixWord ++ tailWord_7349503) baseStart_7349503 baseEnd_7349503 := by
    simpa [prefixWord, tailWord_7349503, baseEnd_7349503] using wordTrace_append hprefix tailTrace_7349503
  have hstable : (prefixWord ++ tailWord_7349503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349503).length < 2 ^ (prefixWord ++ tailWord_7349503).sum := by decide
  have hdescent : baseEnd_7349503 < baseStart_7349503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349516 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 1, 6]
def baseStart_7349516 : Nat := 118140960795 + 7349516 * 2 ^ 59
def prefixEnd_7349516 : Nat := 4983230072969 + 3 ^ 40 * 7349516 * 2
def baseEnd_7349516 : Nat := 1257944761969857406183399

theorem tailTrace_7349516 : CollatzResearch.WordTrace tailWord_7349516 prefixEnd_7349516 1257944761969857406183399 := by
  unfold tailWord_7349516
  simp only [CollatzResearch.WordTrace]
  refine ⟨134029435220983102123270201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178705913627977469497693601 134029435220983102123270201)
  ·
    refine ⟨100522076415737326592452651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134029435220983102123270201 100522076415737326592452651)
    ·
      refine ⟨150783114623605989888678977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100522076415737326592452651 150783114623605989888678977)
      ·
        refine ⟨113087335967704492416509233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150783114623605989888678977 113087335967704492416509233)
        ·
          refine ⟨84815501975778369312381925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113087335967704492416509233 84815501975778369312381925)
          ·
            refine ⟨15902906620458444246071611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84815501975778369312381925 15902906620458444246071611)
            ·
              refine ⟨23854359930687666369107417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15902906620458444246071611 23854359930687666369107417)
              ·
                refine ⟨17890769948015749776830563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23854359930687666369107417 17890769948015749776830563)
                ·
                  refine ⟨26836154922023624665245845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17890769948015749776830563 26836154922023624665245845)
                  ·
                    refine ⟨1257944761969857406183399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26836154922023624665245845 1257944761969857406183399)
                    ·
                      rfl

theorem cell23_7349516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_7349516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349516 prefixEnd_7349516 := by exact prefixLift 7349516
  have htrace : WordTrace (prefixWord ++ tailWord_7349516) baseStart_7349516 baseEnd_7349516 := by
    simpa [prefixWord, tailWord_7349516, baseEnd_7349516] using wordTrace_append hprefix tailTrace_7349516
  have hstable : (prefixWord ++ tailWord_7349516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349516).length < 2 ^ (prefixWord ++ tailWord_7349516).sum := by decide
  have hdescent : baseEnd_7349516 < baseStart_7349516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349540 : List Nat := [2, 3, 1, 3, 1, 1, 2, 3, 3, 2, 2]
def baseStart_7349540 : Nat := 118140960795 + 7349540 * 2 ^ 59
def prefixEnd_7349540 : Nat := 4983230072969 + 3 ^ 40 * 7349540 * 2
def baseEnd_7349540 : Nat := 3773846609445280124650087

theorem tailTrace_7349540 : CollatzResearch.WordTrace tailWord_7349540 prefixEnd_7349540 3773846609445280124650087 := by
  unfold tailWord_7349540
  simp only [CollatzResearch.WordTrace]
  refine ⟨134029872896939628172707037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178706497195919504230276049 134029872896939628172707037)
  ·
    refine ⟨50261202336352360564765139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134029872896939628172707037 50261202336352360564765139)
    ·
      refine ⟨75391803504528540847147709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50261202336352360564765139 75391803504528540847147709)
      ·
        refine ⟨28271926314198202817680391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75391803504528540847147709 28271926314198202817680391)
        ·
          refine ⟨42407889471297304226520587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28271926314198202817680391 42407889471297304226520587)
          ·
            refine ⟨63611834206945956339780881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42407889471297304226520587 63611834206945956339780881)
            ·
              refine ⟨47708875655209467254835661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63611834206945956339780881 47708875655209467254835661)
              ·
                refine ⟨17890828370703550220563373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47708875655209467254835661 17890828370703550220563373)
                ·
                  refine ⟨6709060639013831332711265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17890828370703550220563373 6709060639013831332711265)
                  ·
                    refine ⟨5031795479260373499533449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6709060639013831332711265 5031795479260373499533449)
                    ·
                      refine ⟨3773846609445280124650087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031795479260373499533449 3773846609445280124650087)
                      ·
                        rfl

theorem cell23_7349540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_7349540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349540 prefixEnd_7349540 := by exact prefixLift 7349540
  have htrace : WordTrace (prefixWord ++ tailWord_7349540) baseStart_7349540 baseEnd_7349540 := by
    simpa [prefixWord, tailWord_7349540, baseEnd_7349540] using wordTrace_append hprefix tailTrace_7349540
  have hstable : (prefixWord ++ tailWord_7349540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349540).length < 2 ^ (prefixWord ++ tailWord_7349540).sum := by decide
  have hdescent : baseEnd_7349540 < baseStart_7349540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349553 : List Nat := [1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_7349553 : Nat := 118140960795 + 7349553 * 2 ^ 59
def prefixEnd_7349553 : Nat := 4983230072969 + 3 ^ 40 * 7349553 * 2
def baseEnd_7349553 : Nat := 3773853284693788573787527

theorem tailTrace_7349553 : CollatzResearch.WordTrace tailWord_7349553 prefixEnd_7349553 3773853284693788573787527 := by
  unfold tailWord_7349553
  simp only [CollatzResearch.WordTrace]
  refine ⟨268060219942832159565637313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178706813295221439710424875 268060219942832159565637313)
  ·
    refine ⟨201045164957124119674227985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268060219942832159565637313 201045164957124119674227985)
    ·
      refine ⟨150783873717843089755670989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201045164957124119674227985 150783873717843089755670989)
      ·
        refine ⟨56543952644191158658376621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150783873717843089755670989 56543952644191158658376621)
        ·
          refine ⟨21203982241571684496891233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56543952644191158658376621 21203982241571684496891233)
          ·
            refine ⟨15902986681178763372668425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21203982241571684496891233 15902986681178763372668425)
            ·
              refine ⟨11927240010884072529501319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15902986681178763372668425 11927240010884072529501319)
              ·
                refine ⟨17890860016326108794251979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11927240010884072529501319 17890860016326108794251979)
                ·
                  refine ⟨26836290024489163191377969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17890860016326108794251979 26836290024489163191377969)
                  ·
                    refine ⟨20127217518366872393533477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26836290024489163191377969 20127217518366872393533477)
                    ·
                      refine ⟨3773853284693788573787527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20127217518366872393533477 3773853284693788573787527)
                      ·
                        rfl

theorem cell23_7349553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_7349553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349553 prefixEnd_7349553 := by exact prefixLift 7349553
  have htrace : WordTrace (prefixWord ++ tailWord_7349553) baseStart_7349553 baseEnd_7349553 := by
    simpa [prefixWord, tailWord_7349553, baseEnd_7349553] using wordTrace_append hprefix tailTrace_7349553
  have hstable : (prefixWord ++ tailWord_7349553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349553).length < 2 ^ (prefixWord ++ tailWord_7349553).sum := by decide
  have hdescent : baseEnd_7349553 < baseStart_7349553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349574 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4]
def baseStart_7349574 : Nat := 118140960795 + 7349574 * 2 ^ 59
def prefixEnd_7349574 : Nat := 4983230072969 + 3 ^ 40 * 7349574 * 2
def baseEnd_7349574 : Nat := 3773864067787532991624931

theorem tailTrace_7349574 : CollatzResearch.WordTrace tailWord_7349574 prefixEnd_7349574 3773864067787532991624931 := by
  unfold tailWord_7349574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376905808617377504754743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178707323917170720101434517 8376905808617377504754743)
  ·
    refine ⟨12565358712926066257132115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8376905808617377504754743 12565358712926066257132115)
    ·
      refine ⟨18848038069389099385698173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12565358712926066257132115 18848038069389099385698173)
      ·
        refine ⟨7068014276020912269636815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18848038069389099385698173 7068014276020912269636815)
        ·
          refine ⟨10602021414031368404455223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068014276020912269636815 10602021414031368404455223)
          ·
            refine ⟨15903032121047052606682835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602021414031368404455223 15903032121047052606682835)
            ·
              refine ⟨23854548181570578910024253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903032121047052606682835 23854548181570578910024253)
              ·
                refine ⟨8945455568088967091259095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23854548181570578910024253 8945455568088967091259095)
                ·
                  refine ⟨13418183352133450636888643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945455568088967091259095 13418183352133450636888643)
                  ·
                    refine ⟨20127275028200175955332965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13418183352133450636888643 20127275028200175955332965)
                    ·
                      refine ⟨3773864067787532991624931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20127275028200175955332965 3773864067787532991624931)
                      ·
                        rfl

theorem cell23_7349574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_7349574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349574 prefixEnd_7349574 := by exact prefixLift 7349574
  have htrace : WordTrace (prefixWord ++ tailWord_7349574) baseStart_7349574 baseEnd_7349574 := by
    simpa [prefixWord, tailWord_7349574, baseEnd_7349574] using wordTrace_append hprefix tailTrace_7349574
  have hstable : (prefixWord ++ tailWord_7349574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349574).length < 2 ^ (prefixWord ++ tailWord_7349574).sum := by decide
  have hdescent : baseEnd_7349574 < baseStart_7349574 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349607 : List Nat := [1, 1, 5, 1, 5, 1, 1, 1, 1, 3, 3]
def baseStart_7349607 : Nat := 118140960795 + 7349607 * 2 ^ 59
def prefixEnd_7349607 : Nat := 4983230072969 + 3 ^ 40 * 7349607 * 2
def baseEnd_7349607 : Nat := 3773881012649131362512279

theorem tailTrace_7349607 : CollatzResearch.WordTrace tailWord_7349607 prefixEnd_7349607 3773881012649131362512279 := by
  unfold tailWord_7349607
  simp only [CollatzResearch.WordTrace]
  refine ⟨268062189484636526788103075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178708126323091017858735383 268062189484636526788103075)
  ·
    refine ⟨402093284226954790182154613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268062189484636526788103075 402093284226954790182154613)
    ·
      refine ⟨37696245396277011579576995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402093284226954790182154613 37696245396277011579576995)
      ·
        refine ⟨56544368094415517369365493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37696245396277011579576995 56544368094415517369365493)
        ·
          refine ⟨5301034508851454753378015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56544368094415517369365493 5301034508851454753378015)
          ·
            refine ⟨7951551763277182130067023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301034508851454753378015 7951551763277182130067023)
            ·
              refine ⟨11927327644915773195100535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951551763277182130067023 11927327644915773195100535)
              ·
                refine ⟨17890991467373659792650803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11927327644915773195100535 17890991467373659792650803)
                ·
                  refine ⟨26836487201060489688976205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17890991467373659792650803 26836487201060489688976205)
                  ·
                    refine ⟨10063682700397683633366077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26836487201060489688976205 10063682700397683633366077)
                    ·
                      refine ⟨3773881012649131362512279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063682700397683633366077 3773881012649131362512279)
                      ·
                        rfl

theorem cell23_7349607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_7349607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349607 prefixEnd_7349607 := by exact prefixLift 7349607
  have htrace : WordTrace (prefixWord ++ tailWord_7349607) baseStart_7349607 baseEnd_7349607 := by
    simpa [prefixWord, tailWord_7349607, baseEnd_7349607] using wordTrace_append hprefix tailTrace_7349607
  have hstable : (prefixWord ++ tailWord_7349607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349607).length < 2 ^ (prefixWord ++ tailWord_7349607).sum := by decide
  have hdescent : baseEnd_7349607 < baseStart_7349607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349616 : List Nat := [2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_7349616 : Nat := 118140960795 + 7349616 * 2 ^ 59
def prefixEnd_7349616 : Nat := 4983230072969 + 3 ^ 40 * 7349616 * 2
def baseEnd_7349616 : Nat := 3773885633975021827299737

theorem tailTrace_7349616 : CollatzResearch.WordTrace tailWord_7349616 prefixEnd_7349616 3773885633975021827299737 := by
  unfold tailWord_7349616
  simp only [CollatzResearch.WordTrace]
  refine ⟨134031258870801960662590351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178708345161069280883453801 134031258870801960662590351)
  ·
    refine ⟨201046888306202940993885527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134031258870801960662590351 201046888306202940993885527)
    ·
      refine ⟨301570332459304411490828291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201046888306202940993885527 301570332459304411490828291)
      ·
        refine ⟨452355498688956617236242437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301570332459304411490828291 452355498688956617236242437)
        ·
          refine ⟨84816656004179365731795457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452355498688956617236242437 84816656004179365731795457)
          ·
            refine ⟨63612492003134524298846593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84816656004179365731795457 63612492003134524298846593)
            ·
              refine ⟨47709369002350893224134945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63612492003134524298846593 47709369002350893224134945)
              ·
                refine ⟨35782026751763169918101209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47709369002350893224134945 35782026751763169918101209)
                ·
                  refine ⟨26836520063822377438575907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35782026751763169918101209 26836520063822377438575907)
                  ·
                    refine ⟨40254780095733566157863861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26836520063822377438575907 40254780095733566157863861)
                    ·
                      refine ⟨3773885633975021827299737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40254780095733566157863861 3773885633975021827299737)
                      ·
                        rfl

theorem cell23_7349616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_7349616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349616 prefixEnd_7349616 := by exact prefixLift 7349616
  have htrace : WordTrace (prefixWord ++ tailWord_7349616) baseStart_7349616 baseEnd_7349616 := by
    simpa [prefixWord, tailWord_7349616, baseEnd_7349616] using wordTrace_append hprefix tailTrace_7349616
  have hstable : (prefixWord ++ tailWord_7349616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349616).length < 2 ^ (prefixWord ++ tailWord_7349616).sum := by decide
  have hdescent : baseEnd_7349616 < baseStart_7349616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349634 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7349634 : Nat := 118140960795 + 7349634 * 2 ^ 59
def prefixEnd_7349634 : Nat := 4983230072969 + 3 ^ 40 * 7349634 * 2
def baseEnd_7349634 : Nat := 3773894876626802756874655

theorem tailTrace_7349634 : CollatzResearch.WordTrace tailWord_7349634 prefixEnd_7349634 3773894876626802756874655 := by
  unfold tailWord_7349634
  simp only [CollatzResearch.WordTrace]
  refine ⟨67015793563884677599833989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178708782837025806932890637 67015793563884677599833989)
  ·
    refine ⟨12565461293228377049968873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67015793563884677599833989 12565461293228377049968873)
    ·
      refine ⟨9424095969921282787476655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12565461293228377049968873 9424095969921282787476655)
      ·
        refine ⟨14136143954881924181214983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424095969921282787476655 14136143954881924181214983)
        ·
          refine ⟨21204215932322886271822475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14136143954881924181214983 21204215932322886271822475)
          ·
            refine ⟨31806323898484329407733713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21204215932322886271822475 31806323898484329407733713)
            ·
              refine ⟨23854742923863247055800285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31806323898484329407733713 23854742923863247055800285)
              ·
                refine ⟨8945528596448717645925107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23854742923863247055800285 8945528596448717645925107)
                ·
                  refine ⟨13418292894673076468887661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945528596448717645925107 13418292894673076468887661)
                  ·
                    refine ⟨5031859835502403675832873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13418292894673076468887661 5031859835502403675832873)
                    ·
                      refine ⟨3773894876626802756874655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5031859835502403675832873 3773894876626802756874655)
                      ·
                        rfl

theorem cell23_7349634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7349634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349634 prefixEnd_7349634 := by exact prefixLift 7349634
  have htrace : WordTrace (prefixWord ++ tailWord_7349634) baseStart_7349634 baseEnd_7349634 := by
    simpa [prefixWord, tailWord_7349634, baseEnd_7349634] using wordTrace_append hprefix tailTrace_7349634
  have hstable : (prefixWord ++ tailWord_7349634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349634).length < 2 ^ (prefixWord ++ tailWord_7349634).sum := by decide
  have hdescent : baseEnd_7349634 < baseStart_7349634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349653 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 5]
def baseStart_7349653 : Nat := 118140960795 + 7349653 * 2 ^ 59
def prefixEnd_7349653 : Nat := 4983230072969 + 3 ^ 40 * 7349653 * 2
def baseEnd_7349653 : Nat := 419322736973248686948563

theorem tailTrace_7349653 : CollatzResearch.WordTrace tailWord_7349653 prefixEnd_7349653 419322736973248686948563 := by
  unfold tailWord_7349653
  simp only [CollatzResearch.WordTrace]
  refine ⟨268063867242469876644277613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178709244828313251096185075 268063867242469876644277613)
  ·
    refine ⟨100523950215926203741604105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268063867242469876644277613 100523950215926203741604105)
    ·
      refine ⟨75392962661944652806203079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100523950215926203741604105 75392962661944652806203079)
      ·
        refine ⟨113089443992916979209304619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75392962661944652806203079 113089443992916979209304619)
        ·
          refine ⟨169634165989375468813956929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113089443992916979209304619 169634165989375468813956929)
          ·
            refine ⟨127225624492031601610467697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169634165989375468813956929 127225624492031601610467697)
            ·
              refine ⟨95419218369023701207850773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127225624492031601610467697 95419218369023701207850773)
              ·
                refine ⟨4472775861047985994118005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95419218369023701207850773 4472775861047985994118005)
                ·
                  refine ⟨419322736973248686948563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4472775861047985994118005 419322736973248686948563)
                  ·
                    rfl

theorem cell23_7349653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 5].length) (baseStart_7349653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349653 prefixEnd_7349653 := by exact prefixLift 7349653
  have htrace : WordTrace (prefixWord ++ tailWord_7349653) baseStart_7349653 baseEnd_7349653 := by
    simpa [prefixWord, tailWord_7349653, baseEnd_7349653] using wordTrace_append hprefix tailTrace_7349653
  have hstable : (prefixWord ++ tailWord_7349653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349653).length < 2 ^ (prefixWord ++ tailWord_7349653).sum := by decide
  have hdescent : baseEnd_7349653 < baseStart_7349653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349700 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7349700 : Nat := 118140960795 + 7349700 * 2 ^ 59
def prefixEnd_7349700 : Nat := 4983230072969 + 3 ^ 40 * 7349700 * 2
def baseEnd_7349700 : Nat := 1257976255449999832883117

theorem tailTrace_7349700 : CollatzResearch.WordTrace tailWord_7349700 prefixEnd_7349700 1257976255449999832883117 := by
  unfold tailWord_7349700
  simp only [CollatzResearch.WordTrace]
  refine ⟨134032790736649801835619277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178710387648866402447492369 134032790736649801835619277)
  ·
    refine ⟨50262296526243675688357229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134032790736649801835619277 50262296526243675688357229)
    ·
      refine ⟨18848361197341378383133961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50262296526243675688357229 18848361197341378383133961)
      ·
        refine ⟨14136270898006033787350471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18848361197341378383133961 14136270898006033787350471)
        ·
          refine ⟨21204406347009050681025707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14136270898006033787350471 21204406347009050681025707)
          ·
            refine ⟨31806609520513576021538561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21204406347009050681025707 31806609520513576021538561)
            ·
              refine ⟨23854957140385182016153921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31806609520513576021538561 23854957140385182016153921)
              ·
                refine ⟨17891217855288886512115441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23854957140385182016153921 17891217855288886512115441)
                ·
                  refine ⟨13418413391466664884086581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17891217855288886512115441 13418413391466664884086581)
                  ·
                    refine ⟨1257976255449999832883117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13418413391466664884086581 1257976255449999832883117)
                    ·
                      rfl

theorem cell23_7349700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7349700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349700 prefixEnd_7349700 := by exact prefixLift 7349700
  have htrace : WordTrace (prefixWord ++ tailWord_7349700) baseStart_7349700 baseEnd_7349700 := by
    simpa [prefixWord, tailWord_7349700, baseEnd_7349700] using wordTrace_append hprefix tailTrace_7349700
  have hstable : (prefixWord ++ tailWord_7349700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349700).length < 2 ^ (prefixWord ++ tailWord_7349700).sum := by decide
  have hdescent : baseEnd_7349700 < baseStart_7349700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349703 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4]
def baseStart_7349703 : Nat := 118140960795 + 7349703 * 2 ^ 59
def prefixEnd_7349703 : Nat := 4983230072969 + 3 ^ 40 * 7349703 * 2
def baseEnd_7349703 : Nat := 3773930306791962986911837

theorem tailTrace_7349703 : CollatzResearch.WordTrace tailWord_7349703 prefixEnd_7349703 3773930306791962986911837 := by
  unfold tailWord_7349703
  simp only [CollatzResearch.WordTrace]
  refine ⟨268065690892288735183597763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178710460594859156789065175 268065690892288735183597763)
  ·
    refine ⟨402098536338433102775396645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268065690892288735183597763 402098536338433102775396645)
    ·
      refine ⟨75393475563456206770386871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 402098536338433102775396645 75393475563456206770386871)
      ·
        refine ⟨113090213345184310155580307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75393475563456206770386871 113090213345184310155580307)
        ·
          refine ⟨169635320017776465233370461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113090213345184310155580307 169635320017776465233370461)
          ·
            refine ⟨63613245006666174462513923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169635320017776465233370461 63613245006666174462513923)
            ·
              refine ⟨95419867509999261693770885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63613245006666174462513923 95419867509999261693770885)
              ·
                refine ⟨17891225158124861567582041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95419867509999261693770885 17891225158124861567582041)
                ·
                  refine ⟨13418418868593646175686531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17891225158124861567582041 13418418868593646175686531)
                  ·
                    refine ⟨20127628302890469263529797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13418418868593646175686531 20127628302890469263529797)
                    ·
                      refine ⟨3773930306791962986911837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20127628302890469263529797 3773930306791962986911837)
                      ·
                        rfl

theorem cell23_7349703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_7349703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349703 prefixEnd_7349703 := by exact prefixLift 7349703
  have htrace : WordTrace (prefixWord ++ tailWord_7349703) baseStart_7349703 baseEnd_7349703 := by
    simpa [prefixWord, tailWord_7349703, baseEnd_7349703] using wordTrace_append hprefix tailTrace_7349703
  have hstable : (prefixWord ++ tailWord_7349703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349703).length < 2 ^ (prefixWord ++ tailWord_7349703).sum := by decide
  have hdescent : baseEnd_7349703 < baseStart_7349703 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349821 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 3, 1, 3]
def baseStart_7349821 : Nat := 118140960795 + 7349821 * 2 ^ 59
def prefixEnd_7349821 : Nat := 4983230072969 + 3 ^ 40 * 7349821 * 2
def baseEnd_7349821 : Nat := 3773990897509193525236295

theorem tailTrace_7349821 : CollatzResearch.WordTrace tailWord_7349821 prefixEnd_7349821 3773990897509193525236295 := by
  unfold tailWord_7349821
  simp only [CollatzResearch.WordTrace]
  refine ⟨268069994705861241336393317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178713329803907494224262211 268069994705861241336393317)
  ·
    refine ⟨50263124007348982750573747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268069994705861241336393317 50263124007348982750573747)
    ·
      refine ⟨75394686011023474125860621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50263124007348982750573747 75394686011023474125860621)
      ·
        refine ⟨28273007254133802797197733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75394686011023474125860621 28273007254133802797197733)
        ·
          refine ⟨5301188860150088024474575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28273007254133802797197733 5301188860150088024474575)
          ·
            refine ⟨7951783290225132036711863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301188860150088024474575 7951783290225132036711863)
            ·
              refine ⟨11927674935337698055067795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951783290225132036711863 11927674935337698055067795)
              ·
                refine ⟨17891512403006547082601693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11927674935337698055067795 17891512403006547082601693)
                ·
                  refine ⟨6709317151127455155975635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17891512403006547082601693 6709317151127455155975635)
                  ·
                    refine ⟨10063975726691182733963453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709317151127455155975635 10063975726691182733963453)
                    ·
                      refine ⟨3773990897509193525236295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10063975726691182733963453 3773990897509193525236295)
                      ·
                        rfl

theorem cell23_7349821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_7349821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349821 prefixEnd_7349821 := by exact prefixLift 7349821
  have htrace : WordTrace (prefixWord ++ tailWord_7349821) baseStart_7349821 baseEnd_7349821 := by
    simpa [prefixWord, tailWord_7349821, baseEnd_7349821] using wordTrace_append hprefix tailTrace_7349821
  have hstable : (prefixWord ++ tailWord_7349821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349821).length < 2 ^ (prefixWord ++ tailWord_7349821).sum := by decide
  have hdescent : baseEnd_7349821 < baseStart_7349821 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349823 : List Nat := [1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6]
def baseStart_7349823 : Nat := 118140960795 + 7349823 * 2 ^ 59
def prefixEnd_7349823 : Nat := 4983230072969 + 3 ^ 40 * 7349823 * 2
def baseEnd_7349823 : Nat := 3773991924470502517411285

theorem tailTrace_7349823 : CollatzResearch.WordTrace tailWord_7349823 prefixEnd_7349823 3773991924470502517411285 := by
  unfold tailWord_7349823
  simp only [CollatzResearch.WordTrace]
  refine ⟨268070067651853995677966123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178713378434569330451977415 268070067651853995677966123)
  ·
    refine ⟨402105101477780993516949185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268070067651853995677966123 402105101477780993516949185)
    ·
      refine ⟨301578826108335745137711889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402105101477780993516949185 301578826108335745137711889)
      ·
        refine ⟨226184119581251808853283917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301578826108335745137711889 226184119581251808853283917)
        ·
          refine ⟨84819044842969428319981469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226184119581251808853283917 84819044842969428319981469)
          ·
            refine ⟨31807141816113535619993051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84819044842969428319981469 31807141816113535619993051)
            ·
              refine ⟨47710712724170303429989577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31807141816113535619993051 47710712724170303429989577)
              ·
                refine ⟨35783034543127727572492183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47710712724170303429989577 35783034543127727572492183)
                ·
                  refine ⟨53674551814691591358738275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35783034543127727572492183 53674551814691591358738275)
                  ·
                    refine ⟨80511827722037387038107413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53674551814691591358738275 80511827722037387038107413)
                    ·
                      refine ⟨3773991924470502517411285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80511827722037387038107413 3773991924470502517411285)
                      ·
                        rfl

theorem cell23_7349823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 6].length) (baseStart_7349823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349823 prefixEnd_7349823 := by exact prefixLift 7349823
  have htrace : WordTrace (prefixWord ++ tailWord_7349823) baseStart_7349823 baseEnd_7349823 := by
    simpa [prefixWord, tailWord_7349823, baseEnd_7349823] using wordTrace_append hprefix tailTrace_7349823
  have hstable : (prefixWord ++ tailWord_7349823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349823).length < 2 ^ (prefixWord ++ tailWord_7349823).sum := by decide
  have hdescent : baseEnd_7349823 < baseStart_7349823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349847 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 3]
def baseStart_7349847 : Nat := 118140960795 + 7349847 * 2 ^ 59
def prefixEnd_7349847 : Nat := 4983230072969 + 3 ^ 40 * 7349847 * 2
def baseEnd_7349847 : Nat := 3774004248006210423511175

theorem tailTrace_7349847 : CollatzResearch.WordTrace tailWord_7349847 prefixEnd_7349847 3774004248006210423511175 := by
  unfold tailWord_7349847
  simp only [CollatzResearch.WordTrace]
  refine ⟨268070943003767047776839795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178713962002511365184559863 268070943003767047776839795)
  ·
    refine ⟨402106414505650571665259693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268070943003767047776839795 402106414505650571665259693)
    ·
      refine ⟨150789905439618964374472385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402106414505650571665259693 150789905439618964374472385)
      ·
        refine ⟨113092429079714223280854289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150789905439618964374472385 113092429079714223280854289)
        ·
          refine ⟨84819321809785667460640717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113092429079714223280854289 84819321809785667460640717)
          ·
            refine ⟨31807245678669625297740269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84819321809785667460640717 31807245678669625297740269)
            ·
              refine ⟨11927717129501109486652601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31807245678669625297740269 11927717129501109486652601)
              ·
                refine ⟨8945787847125832114989451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11927717129501109486652601 8945787847125832114989451)
                ·
                  refine ⟨13418681770688748172484177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945787847125832114989451 13418681770688748172484177)
                  ·
                    refine ⟨10064011328016561129363133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13418681770688748172484177 10064011328016561129363133)
                    ·
                      refine ⟨3774004248006210423511175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064011328016561129363133 3774004248006210423511175)
                      ·
                        rfl

theorem cell23_7349847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_7349847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349847 prefixEnd_7349847 := by exact prefixLift 7349847
  have htrace : WordTrace (prefixWord ++ tailWord_7349847) baseStart_7349847 baseEnd_7349847 := by
    simpa [prefixWord, tailWord_7349847, baseEnd_7349847] using wordTrace_append hprefix tailTrace_7349847
  have hstable : (prefixWord ++ tailWord_7349847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349847).length < 2 ^ (prefixWord ++ tailWord_7349847).sum := by decide
  have hdescent : baseEnd_7349847 < baseStart_7349847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349860 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 3, 3, 3]
def baseStart_7349860 : Nat := 118140960795 + 7349860 * 2 ^ 59
def prefixEnd_7349860 : Nat := 4983230072969 + 3 ^ 40 * 7349860 * 2
def baseEnd_7349860 : Nat := 3774010923254718872648615

theorem tailTrace_7349860 : CollatzResearch.WordTrace tailWord_7349860 prefixEnd_7349860 3774010923254718872648615 := by
  unfold tailWord_7349860
  simp only [CollatzResearch.WordTrace]
  refine ⟨134035708576359975498531517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178714278101813300664708689 134035708576359975498531517)
  ·
    refine ⟨50263390716134990811949319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134035708576359975498531517 50263390716134990811949319)
    ·
      refine ⟨75395086074202486217923979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50263390716134990811949319 75395086074202486217923979)
      ·
        refine ⟨113092629111303729326885969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75395086074202486217923979 113092629111303729326885969)
        ·
          refine ⟨84819471833477796995164477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113092629111303729326885969 84819471833477796995164477)
          ·
            refine ⟨31807301937554173873186679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84819471833477796995164477 31807301937554173873186679)
            ·
              refine ⟨47710952906331260809780019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31807301937554173873186679 47710952906331260809780019)
              ·
                refine ⟨71566429359496891214670029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47710952906331260809780019 71566429359496891214670029)
                ·
                  refine ⟨26837411009811334205501261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71566429359496891214670029 26837411009811334205501261)
                  ·
                    refine ⟨10064029128679250327062973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26837411009811334205501261 10064029128679250327062973)
                    ·
                      refine ⟨3774010923254718872648615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064029128679250327062973 3774010923254718872648615)
                      ·
                        rfl

theorem cell23_7349860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_7349860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349860 prefixEnd_7349860 := by exact prefixLift 7349860
  have htrace : WordTrace (prefixWord ++ tailWord_7349860) baseStart_7349860 baseEnd_7349860 := by
    simpa [prefixWord, tailWord_7349860, baseEnd_7349860] using wordTrace_append hprefix tailTrace_7349860
  have hstable : (prefixWord ++ tailWord_7349860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349860).length < 2 ^ (prefixWord ++ tailWord_7349860).sum := by decide
  have hdescent : baseEnd_7349860 < baseStart_7349860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349873 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_7349873 : Nat := 118140960795 + 7349873 * 2 ^ 59
def prefixEnd_7349873 : Nat := 4983230072969 + 3 ^ 40 * 7349873 * 2
def baseEnd_7349873 : Nat := 3774017598503227321786055

theorem tailTrace_7349873 : CollatzResearch.WordTrace tailWord_7349873 prefixEnd_7349873 3774017598503227321786055 := by
  unfold tailWord_7349873
  simp only [CollatzResearch.WordTrace]
  refine ⟨268071891301672854217286273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178714594201115236144857515 268071891301672854217286273)
  ·
    refine ⟨201053918476254640662964705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268071891301672854217286273 201053918476254640662964705)
    ·
      refine ⟨150790438857190980497223529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201053918476254640662964705 150790438857190980497223529)
      ·
        refine ⟨113092829142893235372917647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150790438857190980497223529 113092829142893235372917647)
        ·
          refine ⟨169639243714339853059376471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113092829142893235372917647 169639243714339853059376471)
          ·
            refine ⟨254458865571509779589064707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169639243714339853059376471 254458865571509779589064707)
            ·
              refine ⟨381688298357264669383597061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254458865571509779589064707 381688298357264669383597061)
              ·
                refine ⟨71566555941987125509424449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381688298357264669383597061 71566555941987125509424449)
                ·
                  refine ⟨53674916956490344132068337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71566555941987125509424449 53674916956490344132068337)
                  ·
                    refine ⟨40256187717367758099051253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53674916956490344132068337 40256187717367758099051253)
                    ·
                      refine ⟨3774017598503227321786055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40256187717367758099051253 3774017598503227321786055)
                      ·
                        rfl

theorem cell23_7349873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_7349873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349873 prefixEnd_7349873 := by exact prefixLift 7349873
  have htrace : WordTrace (prefixWord ++ tailWord_7349873) baseStart_7349873 baseEnd_7349873 := by
    simpa [prefixWord, tailWord_7349873, baseEnd_7349873] using wordTrace_append hprefix tailTrace_7349873
  have hstable : (prefixWord ++ tailWord_7349873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349873).length < 2 ^ (prefixWord ++ tailWord_7349873).sum := by decide
  have hdescent : baseEnd_7349873 < baseStart_7349873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349878 : List Nat := [5, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7349878 : Nat := 118140960795 + 7349878 * 2 ^ 59
def prefixEnd_7349878 : Nat := 4983230072969 + 3 ^ 40 * 7349878 * 2
def baseEnd_7349878 : Nat := 3774020165906499802223533

theorem tailTrace_7349878 : CollatzResearch.WordTrace tailWord_7349878 prefixEnd_7349878 3774020165906499802223533 := by
  unfold tailWord_7349878
  simp only [CollatzResearch.WordTrace]
  refine ⟨16754504604165921254451143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178714715777769826714145525 16754504604165921254451143)
  ·
    refine ⟨25131756906248881881676715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16754504604165921254451143 25131756906248881881676715)
    ·
      refine ⟨37697635359373322822515073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25131756906248881881676715 37697635359373322822515073)
      ·
        refine ⟨28273226519529992116886305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37697635359373322822515073 28273226519529992116886305)
        ·
          refine ⟨21204919889647494087664729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28273226519529992116886305 21204919889647494087664729)
          ·
            refine ⟨15903689917235620565748547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21204919889647494087664729 15903689917235620565748547)
            ·
              refine ⟨23855534875853430848622821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903689917235620565748547 23855534875853430848622821)
              ·
                refine ⟨4472912789222518284116779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23855534875853430848622821 4472912789222518284116779)
                ·
                  refine ⟨6709369183833777426175169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472912789222518284116779 6709369183833777426175169)
                  ·
                    refine ⟨5032026887875333069631377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6709369183833777426175169 5032026887875333069631377)
                    ·
                      refine ⟨3774020165906499802223533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032026887875333069631377 3774020165906499802223533)
                      ·
                        rfl

theorem cell23_7349878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7349878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349878 prefixEnd_7349878 := by exact prefixLift 7349878
  have htrace : WordTrace (prefixWord ++ tailWord_7349878) baseStart_7349878 baseEnd_7349878 := by
    simpa [prefixWord, tailWord_7349878, baseEnd_7349878] using wordTrace_append hprefix tailTrace_7349878
  have hstable : (prefixWord ++ tailWord_7349878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349878).length < 2 ^ (prefixWord ++ tailWord_7349878).sum := by decide
  have hdescent : baseEnd_7349878 < baseStart_7349878 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349883 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4]
def baseStart_7349883 : Nat := 118140960795 + 7349883 * 2 ^ 59
def prefixEnd_7349883 : Nat := 4983230072969 + 3 ^ 40 * 7349883 * 2
def baseEnd_7349883 : Nat := 3774022733309772282661009

theorem tailTrace_7349883 : CollatzResearch.WordTrace tailWord_7349883 prefixEnd_7349883 3774022733309772282661009 := by
  unfold tailWord_7349883
  simp only [CollatzResearch.WordTrace]
  refine ⟨268072256031636625925150303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178714837354424417283433535 268072256031636625925150303)
  ·
    refine ⟨402108384047454938887725455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268072256031636625925150303 402108384047454938887725455)
    ·
      refine ⟨603162576071182408331588183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402108384047454938887725455 603162576071182408331588183)
      ·
        refine ⟨904743864106773612497382275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603162576071182408331588183 904743864106773612497382275)
        ·
          refine ⟨1357115796160160418746073413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904743864106773612497382275 1357115796160160418746073413)
          ·
            refine ⟨254459211780030078514888765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1357115796160160418746073413 254459211780030078514888765)
            ·
              refine ⟨95422204417511279443083287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254459211780030078514888765 95422204417511279443083287)
              ·
                refine ⟨143133306626266919164624931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95422204417511279443083287 143133306626266919164624931)
                ·
                  refine ⟨214699959939400378746937397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143133306626266919164624931 214699959939400378746937397)
                  ·
                    refine ⟨20128121244318785507525381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214699959939400378746937397 20128121244318785507525381)
                    ·
                      refine ⟨3774022733309772282661009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20128121244318785507525381 3774022733309772282661009)
                      ·
                        rfl

theorem cell23_7349883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 4].length) (baseStart_7349883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349883 prefixEnd_7349883 := by exact prefixLift 7349883
  have htrace : WordTrace (prefixWord ++ tailWord_7349883) baseStart_7349883 baseEnd_7349883 := by
    simpa [prefixWord, tailWord_7349883, baseEnd_7349883] using wordTrace_append hprefix tailTrace_7349883
  have hstable : (prefixWord ++ tailWord_7349883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349883).length < 2 ^ (prefixWord ++ tailWord_7349883).sum := by decide
  have hdescent : baseEnd_7349883 < baseStart_7349883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349921 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7349921 : Nat := 118140960795 + 7349921 * 2 ^ 59
def prefixEnd_7349921 : Nat := 4983230072969 + 3 ^ 40 * 7349921 * 2
def baseEnd_7349921 : Nat := 3774042245574643133985835

theorem tailTrace_7349921 : CollatzResearch.WordTrace tailWord_7349921 prefixEnd_7349921 3774042245574643133985835 := by
  unfold tailWord_7349921
  simp only [CollatzResearch.WordTrace]
  refine ⟨268073642005498958415033617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178715761336999305610022411 268073642005498958415033617)
  ·
    refine ⟨201055231504124218811275213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268073642005498958415033617 201055231504124218811275213)
    ·
      refine ⟨75395711814046582054228205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201055231504124218811275213 75395711814046582054228205)
      ·
        refine ⟨28273391930267468270335577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75395711814046582054228205 28273391930267468270335577)
        ·
          refine ⟨21205043947700601202751683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28273391930267468270335577 21205043947700601202751683)
          ·
            refine ⟨31807565921550901804127525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21205043947700601202751683 31807565921550901804127525)
            ·
              refine ⟨5963918610290794088273911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31807565921550901804127525 5963918610290794088273911)
              ·
                refine ⟨8945877915436191132410867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963918610290794088273911 8945877915436191132410867)
                ·
                  refine ⟨13418816873154286698616301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8945877915436191132410867 13418816873154286698616301)
                  ·
                    refine ⟨5032056327432857511981113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13418816873154286698616301 5032056327432857511981113)
                    ·
                      refine ⟨3774042245574643133985835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032056327432857511981113 3774042245574643133985835)
                      ·
                        rfl

theorem cell23_7349921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7349921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349921 prefixEnd_7349921 := by exact prefixLift 7349921
  have htrace : WordTrace (prefixWord ++ tailWord_7349921) baseStart_7349921 baseEnd_7349921 := by
    simpa [prefixWord, tailWord_7349921, baseEnd_7349921] using wordTrace_append hprefix tailTrace_7349921
  have hstable : (prefixWord ++ tailWord_7349921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349921).length < 2 ^ (prefixWord ++ tailWord_7349921).sum := by decide
  have hdescent : baseEnd_7349921 < baseStart_7349921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349923 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 9]
def baseStart_7349923 : Nat := 118140960795 + 7349923 * 2 ^ 59
def prefixEnd_7349923 : Nat := 4983230072969 + 3 ^ 40 * 7349923 * 2
def baseEnd_7349923 : Nat := 419338141392883569573425

theorem tailTrace_7349923 : CollatzResearch.WordTrace tailWord_7349923 prefixEnd_7349923 419338141392883569573425 := by
  unfold tailWord_7349923
  simp only [CollatzResearch.WordTrace]
  refine ⟨268073714951491712756606423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178715809967661141837737615 268073714951491712756606423)
  ·
    refine ⟨402110572427237569134909635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268073714951491712756606423 402110572427237569134909635)
    ·
      refine ⟨603165858640856353702364453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402110572427237569134909635 603165858640856353702364453)
      ·
        refine ⟨113093598495160566319193335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603165858640856353702364453 113093598495160566319193335)
        ·
          refine ⟨169640397742740849478790003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113093598495160566319193335 169640397742740849478790003)
          ·
            refine ⟨254460596614111274218185005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169640397742740849478790003 254460596614111274218185005)
            ·
              refine ⟨95422723730291727831819377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254460596614111274218185005 95422723730291727831819377)
              ·
                refine ⟨71567042797718795873864533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95422723730291727831819377 71567042797718795873864533)
                ·
                  refine ⟨419338141392883569573425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71567042797718795873864533 419338141392883569573425)
                  ·
                    rfl

theorem cell23_7349923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 9].length) (baseStart_7349923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349923 prefixEnd_7349923 := by exact prefixLift 7349923
  have htrace : WordTrace (prefixWord ++ tailWord_7349923) baseStart_7349923 baseEnd_7349923 := by
    simpa [prefixWord, tailWord_7349923, baseEnd_7349923] using wordTrace_append hprefix tailTrace_7349923
  have hstable : (prefixWord ++ tailWord_7349923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349923).length < 2 ^ (prefixWord ++ tailWord_7349923).sum := by decide
  have hdescent : baseEnd_7349923 < baseStart_7349923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349928 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7349928 : Nat := 118140960795 + 7349928 * 2 ^ 59
def prefixEnd_7349928 : Nat := 4983230072969 + 3 ^ 40 * 7349928 * 2
def baseEnd_7349928 : Nat := 3774045839939224606598303

theorem tailTrace_7349928 : CollatzResearch.WordTrace tailWord_7349928 prefixEnd_7349928 3774045839939224606598303 := by
  unfold tailWord_7349928
  simp only [CollatzResearch.WordTrace]
  refine ⟨134036948658236799305269219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178715931544315732407025625 134036948658236799305269219)
  ·
    refine ⟨201055422987355198957903829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134036948658236799305269219 201055422987355198957903829)
    ·
      refine ⟨4712236476266137475575871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 201055422987355198957903829 4712236476266137475575871)
      ·
        refine ⟨7068354714399206213363807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4712236476266137475575871 7068354714399206213363807)
        ·
          refine ⟨10602532071598809320045711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7068354714399206213363807 10602532071598809320045711)
          ·
            refine ⟨15903798107398213980068567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602532071598809320045711 15903798107398213980068567)
            ·
              refine ⟨23855697161097320970102851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903798107398213980068567 23855697161097320970102851)
              ·
                refine ⟨35783545741645981455154277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23855697161097320970102851 35783545741645981455154277)
                ·
                  refine ⟨6709414826558621522841427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35783545741645981455154277 6709414826558621522841427)
                  ·
                    refine ⟨10064122239837932284262141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709414826558621522841427 10064122239837932284262141)
                    ·
                      refine ⟨3774045839939224606598303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064122239837932284262141 3774045839939224606598303)
                      ·
                        rfl

theorem cell23_7349928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7349928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349928 prefixEnd_7349928 := by exact prefixLift 7349928
  have htrace : WordTrace (prefixWord ++ tailWord_7349928) baseStart_7349928 baseEnd_7349928 := by
    simpa [prefixWord, tailWord_7349928, baseEnd_7349928] using wordTrace_append hprefix tailTrace_7349928
  have hstable : (prefixWord ++ tailWord_7349928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349928).length < 2 ^ (prefixWord ++ tailWord_7349928).sum := by decide
  have hdescent : baseEnd_7349928 < baseStart_7349928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349951 : List Nat := [1, 1, 2, 2, 2, 3, 5, 1, 2, 2, 2]
def baseStart_7349951 : Nat := 118140960795 + 7349951 * 2 ^ 59
def prefixEnd_7349951 : Nat := 4983230072969 + 3 ^ 40 * 7349951 * 2
def baseEnd_7349951 : Nat := 3774057649994278016610697

theorem tailTrace_7349951 : CollatzResearch.WordTrace tailWord_7349951 prefixEnd_7349951 3774057649994278016610697 := by
  unfold tailWord_7349951
  simp only [CollatzResearch.WordTrace]
  refine ⟨268074736195390273538625707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178716490796926849025750471 268074736195390273538625707)
  ·
    refine ⟨402112104293085410307938561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268074736195390273538625707 402112104293085410307938561)
    ·
      refine ⟨301584078219814057730953921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402112104293085410307938561 301584078219814057730953921)
      ·
        refine ⟨226188058664860543298215441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301584078219814057730953921 226188058664860543298215441)
        ·
          refine ⟨169641043998645407473661581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226188058664860543298215441 169641043998645407473661581)
          ·
            refine ⟨63615391499492027802623093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169641043998645407473661581 63615391499492027802623093)
            ·
              refine ⟨5963942953077377606495915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63615391499492027802623093 5963942953077377606495915)
              ·
                refine ⟨8945914429616066409743873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963942953077377606495915 8945914429616066409743873)
                ·
                  refine ⟨6709435822212049807307905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8945914429616066409743873 6709435822212049807307905)
                  ·
                    refine ⟨5032076866659037355480929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6709435822212049807307905 5032076866659037355480929)
                    ·
                      refine ⟨3774057649994278016610697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032076866659037355480929 3774057649994278016610697)
                      ·
                        rfl

theorem cell23_7349951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 5, 1, 2, 2, 2].length) (baseStart_7349951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349951 prefixEnd_7349951 := by exact prefixLift 7349951
  have htrace : WordTrace (prefixWord ++ tailWord_7349951) baseStart_7349951 baseEnd_7349951 := by
    simpa [prefixWord, tailWord_7349951, baseEnd_7349951] using wordTrace_append hprefix tailTrace_7349951
  have hstable : (prefixWord ++ tailWord_7349951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349951).length < 2 ^ (prefixWord ++ tailWord_7349951).sum := by decide
  have hdescent : baseEnd_7349951 < baseStart_7349951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349991 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 7]
def baseStart_7349991 : Nat := 118140960795 + 7349991 * 2 ^ 59
def prefixEnd_7349991 : Nat := 4983230072969 + 3 ^ 40 * 7349991 * 2
def baseEnd_7349991 : Nat := 419342021024495317790057

theorem tailTrace_7349991 : CollatzResearch.WordTrace tailWord_7349991 prefixEnd_7349991 419342021024495317790057 := by
  unfold tailWord_7349991
  simp only [CollatzResearch.WordTrace]
  refine ⟨268076195115245360370081827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178717463410163573580054551 268076195115245360370081827)
  ·
    refine ⟨402114292672868040555122741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268076195115245360370081827 402114292672868040555122741)
    ·
      refine ⟨37698214938081378802042757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 402114292672868040555122741 37698214938081378802042757)
      ·
        refine ⟨7068415300890258525383017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37698214938081378802042757 7068415300890258525383017)
        ·
          refine ⟨5301311475667693894037263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7068415300890258525383017 5301311475667693894037263)
          ·
            refine ⟨7951967213501540841055895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301311475667693894037263 7951967213501540841055895)
            ·
              refine ⟨11927950820252311261583843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7951967213501540841055895 11927950820252311261583843)
              ·
                refine ⟨17891926230378466892375765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11927950820252311261583843 17891926230378466892375765)
                ·
                  refine ⟨419342021024495317790057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17891926230378466892375765 419342021024495317790057)
                  ·
                    rfl

theorem cell23_7349991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 7].length) (baseStart_7349991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349991 prefixEnd_7349991 := by exact prefixLift 7349991
  have htrace : WordTrace (prefixWord ++ tailWord_7349991) baseStart_7349991 baseEnd_7349991 := by
    simpa [prefixWord, tailWord_7349991, baseEnd_7349991] using wordTrace_append hprefix tailTrace_7349991
  have hstable : (prefixWord ++ tailWord_7349991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349991).length < 2 ^ (prefixWord ++ tailWord_7349991).sum := by decide
  have hdescent : baseEnd_7349991 < baseStart_7349991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7349997 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7349997 : Nat := 118140960795 + 7349997 * 2 ^ 59
def prefixEnd_7349997 : Nat := 4983230072969 + 3 ^ 40 * 7349997 * 2
def baseEnd_7349997 : Nat := 3774081270104384836635485

theorem tailTrace_7349997 : CollatzResearch.WordTrace tailWord_7349997 prefixEnd_7349997 3774081270104384836635485 := by
  unfold tailWord_7349997
  simp only [CollatzResearch.WordTrace]
  refine ⟨268076413953223623394800245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178717609302149082263200163 268076413953223623394800245)
  ·
    refine ⟨25132163808114714693262523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268076413953223623394800245 25132163808114714693262523)
    ·
      refine ⟨37698245712172072039893785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25132163808114714693262523 37698245712172072039893785)
      ·
        refine ⟨28273684284129054029920339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37698245712172072039893785 28273684284129054029920339)
        ·
          refine ⟨42410526426193581044880509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28273684284129054029920339 42410526426193581044880509)
          ·
            refine ⟨15903947409822592891830191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42410526426193581044880509 15903947409822592891830191)
            ·
              refine ⟨23855921114733889337745287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15903947409822592891830191 23855921114733889337745287)
              ·
                refine ⟨35783881672100834006617931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23855921114733889337745287 35783881672100834006617931)
                ·
                  refine ⟨53675822508151251009926897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35783881672100834006617931 53675822508151251009926897)
                  ·
                    refine ⟨40256866881113438257445173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53675822508151251009926897 40256866881113438257445173)
                    ·
                      refine ⟨3774081270104384836635485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40256866881113438257445173 3774081270104384836635485)
                      ·
                        rfl

theorem cell23_7349997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7349997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7349997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7349997 prefixEnd_7349997 := by exact prefixLift 7349997
  have htrace : WordTrace (prefixWord ++ tailWord_7349997) baseStart_7349997 baseEnd_7349997 := by
    simpa [prefixWord, tailWord_7349997, baseEnd_7349997] using wordTrace_append hprefix tailTrace_7349997
  have hstable : (prefixWord ++ tailWord_7349997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7349997).length < 2 ^ (prefixWord ++ tailWord_7349997).sum := by decide
  have hdescent : baseEnd_7349997 < baseStart_7349997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7349997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350007 : List Nat := [1, 1, 3, 1, 1, 1, 4, 3, 2, 4, 2]
def baseStart_7350007 : Nat := 118140960795 + 7350007 * 2 ^ 59
def prefixEnd_7350007 : Nat := 4983230072969 + 3 ^ 40 * 7350007 * 2
def baseEnd_7350007 : Nat := 3774086404910929797510439

theorem tailTrace_7350007 : CollatzResearch.WordTrace tailWord_7350007 prefixEnd_7350007 3774086404910929797510439 := by
  unfold tailWord_7350007
  simp only [CollatzResearch.WordTrace]
  refine ⟨268076778683187395102664275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178717852455458263401776183 268076778683187395102664275)
  ·
    refine ⟨402115168024781092653996413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268076778683187395102664275 402115168024781092653996413)
    ·
      refine ⟨150793188009292909745248655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402115168024781092653996413 150793188009292909745248655)
      ·
        refine ⟨226189782013939364617872983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150793188009292909745248655 226189782013939364617872983)
        ·
          refine ⟨339284673020909046926809475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226189782013939364617872983 339284673020909046926809475)
          ·
            refine ⟨508927009531363570390214213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339284673020909046926809475 508927009531363570390214213)
            ·
              refine ⟨95423814287130669448165165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508927009531363570390214213 95423814287130669448165165)
              ·
                refine ⟨35783930357674001043061937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95423814287130669448165165 35783930357674001043061937)
                ·
                  refine ⟨26837947768255500782296453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35783930357674001043061937 26837947768255500782296453)
                  ·
                    refine ⟨5032115206547906396680585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26837947768255500782296453 5032115206547906396680585)
                    ·
                      refine ⟨3774086404910929797510439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032115206547906396680585 3774086404910929797510439)
                      ·
                        rfl

theorem cell23_7350007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 4, 2].length) (baseStart_7350007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350007 prefixEnd_7350007 := by exact prefixLift 7350007
  have htrace : WordTrace (prefixWord ++ tailWord_7350007) baseStart_7350007 baseEnd_7350007 := by
    simpa [prefixWord, tailWord_7350007, baseEnd_7350007] using wordTrace_append hprefix tailTrace_7350007
  have hstable : (prefixWord ++ tailWord_7350007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350007).length < 2 ^ (prefixWord ++ tailWord_7350007).sum := by decide
  have hdescent : baseEnd_7350007 < baseStart_7350007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350017 : List Nat := [1, 2, 4, 1, 1, 1, 2, 4, 3, 4]
def baseStart_7350017 : Nat := 118140960795 + 7350017 * 2 ^ 59
def prefixEnd_7350017 : Nat := 4983230072969 + 3 ^ 40 * 7350017 * 2
def baseEnd_7350017 : Nat := 1258030513239158252795131

theorem tailTrace_7350017 : CollatzResearch.WordTrace tailWord_7350017 prefixEnd_7350017 1258030513239158252795131 := by
  unfold tailWord_7350017
  simp only [CollatzResearch.WordTrace]
  refine ⟨268077143413151166810528305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178718095608767444540352203 268077143413151166810528305)
  ·
    refine ⟨201057857559863375107896229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268077143413151166810528305 201057857559863375107896229)
    ·
      refine ⟨37698348292474382832730543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201057857559863375107896229 37698348292474382832730543)
      ·
        refine ⟨56547522438711574249095815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37698348292474382832730543 56547522438711574249095815)
        ·
          refine ⟨84821283658067361373643723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56547522438711574249095815 84821283658067361373643723)
          ·
            refine ⟨127231925487101042060465585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84821283658067361373643723 127231925487101042060465585)
            ·
              refine ⟨95423944115325781545349189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127231925487101042060465585 95423944115325781545349189)
              ·
                refine ⟨17891989521623584039752973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95423944115325781545349189 17891989521623584039752973)
                ·
                  refine ⟨6709496070608844014907365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17891989521623584039752973 6709496070608844014907365)
                  ·
                    refine ⟨1258030513239158252795131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709496070608844014907365 1258030513239158252795131)
                    ·
                      rfl

theorem cell23_7350017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_7350017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350017 prefixEnd_7350017 := by exact prefixLift 7350017
  have htrace : WordTrace (prefixWord ++ tailWord_7350017) baseStart_7350017 baseEnd_7350017 := by
    simpa [prefixWord, tailWord_7350017, baseEnd_7350017] using wordTrace_append hprefix tailTrace_7350017
  have hstable : (prefixWord ++ tailWord_7350017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350017).length < 2 ^ (prefixWord ++ tailWord_7350017).sum := by decide
  have hdescent : baseEnd_7350017 < baseStart_7350017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350027 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3]
def baseStart_7350027 : Nat := 118140960795 + 7350027 * 2 ^ 59
def prefixEnd_7350027 : Nat := 4983230072969 + 3 ^ 40 * 7350027 * 2
def baseEnd_7350027 : Nat := 3774096674524019719260347

theorem tailTrace_7350027 : CollatzResearch.WordTrace tailWord_7350027 prefixEnd_7350027 3774096674524019719260347 := by
  unfold tailWord_7350027
  simp only [CollatzResearch.WordTrace]
  refine ⟨268077508143114938518392335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178718338762076625678928223 268077508143114938518392335)
  ·
    refine ⟨402116262214672407777588503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268077508143114938518392335 402116262214672407777588503)
    ·
      refine ⟨603174393322008611666382755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402116262214672407777588503 603174393322008611666382755)
      ·
        refine ⟨904761589983012917499574133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603174393322008611666382755 904761589983012917499574133)
        ·
          refine ⟨84821399060907461015585075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 904761589983012917499574133 84821399060907461015585075)
          ·
            refine ⟨127232098591361191523377613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84821399060907461015585075 127232098591361191523377613)
            ·
              refine ⟨47712036971760446821266605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127232098591361191523377613 47712036971760446821266605)
              ·
                refine ⟨17892013864410167557974977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47712036971760446821266605 17892013864410167557974977)
                ·
                  refine ⟨13419010398307625668481233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17892013864410167557974977 13419010398307625668481233)
                  ·
                    refine ⟨10064257798730719251360925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13419010398307625668481233 10064257798730719251360925)
                    ·
                      refine ⟨3774096674524019719260347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064257798730719251360925 3774096674524019719260347)
                      ·
                        rfl

theorem cell23_7350027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 3].length) (baseStart_7350027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350027 prefixEnd_7350027 := by exact prefixLift 7350027
  have htrace : WordTrace (prefixWord ++ tailWord_7350027) baseStart_7350027 baseEnd_7350027 := by
    simpa [prefixWord, tailWord_7350027, baseEnd_7350027] using wordTrace_append hprefix tailTrace_7350027
  have hstable : (prefixWord ++ tailWord_7350027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350027).length < 2 ^ (prefixWord ++ tailWord_7350027).sum := by decide
  have hdescent : baseEnd_7350027 < baseStart_7350027 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350030 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 10]
def baseStart_7350030 : Nat := 118140960795 + 7350030 * 2 ^ 59
def prefixEnd_7350030 : Nat := 4983230072969 + 3 ^ 40 * 7350030 * 2
def baseEnd_7350030 : Nat := 419344246107331467502537

theorem tailTrace_7350030 : CollatzResearch.WordTrace tailWord_7350030 prefixEnd_7350030 419344246107331467502537 := by
  unfold tailWord_7350030
  simp only [CollatzResearch.WordTrace]
  refine ⟨33509702195263008753843943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178718411708069380020501029 33509702195263008753843943)
  ·
    refine ⟨50264553292894513130765915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33509702195263008753843943 50264553292894513130765915)
    ·
      refine ⟨75396829939341769696148873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50264553292894513130765915 75396829939341769696148873)
      ·
        refine ⟨56547622454506327272111655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75396829939341769696148873 56547622454506327272111655)
        ·
          refine ⟨84821433681759490908167483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56547622454506327272111655 84821433681759490908167483)
          ·
            refine ⟨127232150522639236362251225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84821433681759490908167483 127232150522639236362251225)
            ·
              refine ⟨95424112891979427271688419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127232150522639236362251225 95424112891979427271688419)
              ·
                refine ⟨143136169337969140907532629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95424112891979427271688419 143136169337969140907532629)
                ·
                  refine ⟨419344246107331467502537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 143136169337969140907532629 419344246107331467502537)
                  ·
                    rfl

theorem cell23_7350030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 10].length) (baseStart_7350030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350030 prefixEnd_7350030 := by exact prefixLift 7350030
  have htrace : WordTrace (prefixWord ++ tailWord_7350030) baseStart_7350030 baseEnd_7350030 := by
    simpa [prefixWord, tailWord_7350030, baseEnd_7350030] using wordTrace_append hprefix tailTrace_7350030
  have hstable : (prefixWord ++ tailWord_7350030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350030).length < 2 ^ (prefixWord ++ tailWord_7350030).sum := by decide
  have hdescent : baseEnd_7350030 < baseStart_7350030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350047 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 6]
def baseStart_7350047 : Nat := 118140960795 + 7350047 * 2 ^ 59
def prefixEnd_7350047 : Nat := 4983230072969 + 3 ^ 40 * 7350047 * 2
def baseEnd_7350047 : Nat := 419345216015234404556695

theorem tailTrace_7350047 : CollatzResearch.WordTrace tailWord_7350047 prefixEnd_7350047 419345216015234404556695 := by
  unfold tailWord_7350047
  simp only [CollatzResearch.WordTrace]
  refine ⟨268078237603042481934120395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178718825068694987956080263 268078237603042481934120395)
  ·
    refine ⟨402117356404563722901180593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268078237603042481934120395 402117356404563722901180593)
    ·
      refine ⟨301588017303422792175885445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402117356404563722901180593 301588017303422792175885445)
      ·
        refine ⟨56547753244391773532978521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301588017303422792175885445 56547753244391773532978521)
        ·
          refine ⟨42410814933293830149733891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56547753244391773532978521 42410814933293830149733891)
          ·
            refine ⟨63616222399940745224600837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42410814933293830149733891 63616222399940745224600837)
            ·
              refine ⟨11928041699988889729612657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63616222399940745224600837 11928041699988889729612657)
              ·
                refine ⟨8946031274991667297209493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11928041699988889729612657 8946031274991667297209493)
                ·
                  refine ⟨419345216015234404556695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8946031274991667297209493 419345216015234404556695)
                  ·
                    rfl

theorem cell23_7350047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 6].length) (baseStart_7350047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350047 prefixEnd_7350047 := by exact prefixLift 7350047
  have htrace : WordTrace (prefixWord ++ tailWord_7350047) baseStart_7350047 baseEnd_7350047 := by
    simpa [prefixWord, tailWord_7350047, baseEnd_7350047] using wordTrace_append hprefix tailTrace_7350047
  have hstable : (prefixWord ++ tailWord_7350047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350047).length < 2 ^ (prefixWord ++ tailWord_7350047).sum := by decide
  have hdescent : baseEnd_7350047 < baseStart_7350047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350051 : List Nat := [1, 1, 1, 4, 2, 1, 6, 2, 1, 4]
def baseStart_7350051 : Nat := 118140960795 + 7350051 * 2 ^ 59
def prefixEnd_7350051 : Nat := 4983230072969 + 3 ^ 40 * 7350051 * 2
def baseEnd_7350051 : Nat := 1258036332686575875120079

theorem tailTrace_7350051 : CollatzResearch.WordTrace tailWord_7350051 prefixEnd_7350051 1258036332686575875120079 := by
  unfold tailWord_7350051
  simp only [CollatzResearch.WordTrace]
  refine ⟨268078383495027990617266007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178718922330018660411510671 268078383495027990617266007)
  ·
    refine ⟨402117575242541985925899011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268078383495027990617266007 402117575242541985925899011)
    ·
      refine ⟨603176362863812978888848517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402117575242541985925899011 603176362863812978888848517)
      ·
        refine ⟨113095568036964933541659097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 603176362863812978888848517 113095568036964933541659097)
        ·
          refine ⟨84821676027723700156244323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113095568036964933541659097 84821676027723700156244323)
          ·
            refine ⟨127232514041585550234366485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84821676027723700156244323 127232514041585550234366485)
            ·
              refine ⟨5964024095699322667235929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127232514041585550234366485 5964024095699322667235929)
              ·
                refine ⟨4473018071774492000426947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964024095699322667235929 4473018071774492000426947)
                ·
                  refine ⟨6709527107661738000640421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473018071774492000426947 6709527107661738000640421)
                  ·
                    refine ⟨1258036332686575875120079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709527107661738000640421 1258036332686575875120079)
                    ·
                      rfl

theorem cell23_7350051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 1, 4].length) (baseStart_7350051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350051 prefixEnd_7350051 := by exact prefixLift 7350051
  have htrace : WordTrace (prefixWord ++ tailWord_7350051) baseStart_7350051 baseEnd_7350051 := by
    simpa [prefixWord, tailWord_7350051, baseEnd_7350051] using wordTrace_append hprefix tailTrace_7350051
  have hstable : (prefixWord ++ tailWord_7350051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350051).length < 2 ^ (prefixWord ++ tailWord_7350051).sum := by decide
  have hdescent : baseEnd_7350051 < baseStart_7350051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350074 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3]
def baseStart_7350074 : Nat := 118140960795 + 7350074 * 2 ^ 59
def prefixEnd_7350074 : Nat := 4983230072969 + 3 ^ 40 * 7350074 * 2
def baseEnd_7350074 : Nat := 3774120808114781035372631

theorem tailTrace_7350074 : CollatzResearch.WordTrace tailWord_7350074 prefixEnd_7350074 3774120808114781035372631 := by
  unfold tailWord_7350074
  simp only [CollatzResearch.WordTrace]
  refine ⟨67019805593486166386338319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178719481582629777030235517 67019805593486166386338319)
  ·
    refine ⟨100529708390229249579507479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67019805593486166386338319 100529708390229249579507479)
    ·
      refine ⟨150794562585343874369261219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100529708390229249579507479 150794562585343874369261219)
      ·
        refine ⟨226191843878015811553891829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150794562585343874369261219 226191843878015811553891829)
        ·
          refine ⟨21205485363563982333177359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226191843878015811553891829 21205485363563982333177359)
          ·
            refine ⟨31808228045345973499766039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21205485363563982333177359 31808228045345973499766039)
            ·
              refine ⟨47712342068018960249649059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31808228045345973499766039 47712342068018960249649059)
              ·
                refine ⟨71568513102028440374473589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47712342068018960249649059 71568513102028440374473589)
                ·
                  refine ⟨6709548103315166285106899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71568513102028440374473589 6709548103315166285106899)
                  ·
                    refine ⟨10064322154972749427660349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709548103315166285106899 10064322154972749427660349)
                    ·
                      refine ⟨3774120808114781035372631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064322154972749427660349 3774120808114781035372631)
                      ·
                        rfl

theorem cell23_7350074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 5, 1, 3].length) (baseStart_7350074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350074 prefixEnd_7350074 := by exact prefixLift 7350074
  have htrace : WordTrace (prefixWord ++ tailWord_7350074) baseStart_7350074 baseEnd_7350074 := by
    simpa [prefixWord, tailWord_7350074, baseEnd_7350074] using wordTrace_append hprefix tailTrace_7350074
  have hstable : (prefixWord ++ tailWord_7350074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350074).length < 2 ^ (prefixWord ++ tailWord_7350074).sum := by decide
  have hdescent : baseEnd_7350074 < baseStart_7350074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350108 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_7350108 : Nat := 118140960795 + 7350108 * 2 ^ 59
def prefixEnd_7350108 : Nat := 4983230072969 + 3 ^ 40 * 7350108 * 2
def baseEnd_7350108 : Nat := 3774138266457033902347475

theorem tailTrace_7350108 : CollatzResearch.WordTrace tailWord_7350108 prefixEnd_7350108 3774138266457033902347475 := by
  unfold tailWord_7350108
  simp only [CollatzResearch.WordTrace]
  refine ⟨134040231227910744676045489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178720308303880992901393985 134040231227910744676045489)
  ·
    refine ⟨100530173420933058507034117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134040231227910744676045489 100530173420933058507034117)
    ·
      refine ⟨18849407516424948470068897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100530173420933058507034117 18849407516424948470068897)
      ·
        refine ⟨14137055637318711352551673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18849407516424948470068897 14137055637318711352551673)
        ·
          refine ⟨10602791727989033514413755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14137055637318711352551673 10602791727989033514413755)
          ·
            refine ⟨15904187591983550271620633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10602791727989033514413755 15904187591983550271620633)
            ·
              refine ⟨11928140693987662703715475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15904187591983550271620633 11928140693987662703715475)
              ·
                refine ⟨17892211040981494055573213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11928140693987662703715475 17892211040981494055573213)
                ·
                  refine ⟨6709579140368060270839955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17892211040981494055573213 6709579140368060270839955)
                  ·
                    refine ⟨10064368710552090406259933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709579140368060270839955 10064368710552090406259933)
                    ·
                      refine ⟨3774138266457033902347475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064368710552090406259933 3774138266457033902347475)
                      ·
                        rfl

theorem cell23_7350108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_7350108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350108 prefixEnd_7350108 := by exact prefixLift 7350108
  have htrace : WordTrace (prefixWord ++ tailWord_7350108) baseStart_7350108 baseEnd_7350108 := by
    simpa [prefixWord, tailWord_7350108, baseEnd_7350108] using wordTrace_append hprefix tailTrace_7350108
  have hstable : (prefixWord ++ tailWord_7350108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350108).length < 2 ^ (prefixWord ++ tailWord_7350108).sum := by decide
  have hdescent : baseEnd_7350108 < baseStart_7350108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350124 : List Nat := [2, 2, 1, 1, 4, 4, 1, 1, 1, 6]
def baseStart_7350124 : Nat := 118140960795 + 7350124 * 2 ^ 59
def prefixEnd_7350124 : Nat := 4983230072969 + 3 ^ 40 * 7350124 * 2
def baseEnd_7350124 : Nat := 1258048827382501946582467

theorem tailTrace_7350124 : CollatzResearch.WordTrace tailWord_7350124 prefixEnd_7350124 1258048827382501946582467 := by
  unfold tailWord_7350124
  simp only [CollatzResearch.WordTrace]
  refine ⟨134040523011881762042336713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178720697349175682723115617 134040523011881762042336713)
  ·
    refine ⟨100530392258911321531752535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134040523011881762042336713 100530392258911321531752535)
    ·
      refine ⟨150795588388366982297628803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100530392258911321531752535 150795588388366982297628803)
      ·
        refine ⟨226193382582550473446443205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150795588388366982297628803 226193382582550473446443205)
        ·
          refine ⟨42411259234228213771208101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226193382582550473446443205 42411259234228213771208101)
          ·
            refine ⟨7952111106417790082101519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42411259234228213771208101 7952111106417790082101519)
            ·
              refine ⟨11928166659626685123152279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952111106417790082101519 11928166659626685123152279)
              ·
                refine ⟨17892249989440027684728419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11928166659626685123152279 17892249989440027684728419)
                ·
                  refine ⟨26838374984160041527092629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17892249989440027684728419 26838374984160041527092629)
                  ·
                    refine ⟨1258048827382501946582467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26838374984160041527092629 1258048827382501946582467)
                    ·
                      rfl

theorem cell23_7350124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_7350124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350124 prefixEnd_7350124 := by exact prefixLift 7350124
  have htrace : WordTrace (prefixWord ++ tailWord_7350124) baseStart_7350124 baseEnd_7350124 := by
    simpa [prefixWord, tailWord_7350124, baseEnd_7350124] using wordTrace_append hprefix tailTrace_7350124
  have hstable : (prefixWord ++ tailWord_7350124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350124).length < 2 ^ (prefixWord ++ tailWord_7350124).sum := by decide
  have hdescent : baseEnd_7350124 < baseStart_7350124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350142 : List Nat := [4, 2, 3, 1, 1, 3, 1, 3, 1, 1, 3]
def baseStart_7350142 : Nat := 118140960795 + 7350142 * 2 ^ 59
def prefixEnd_7350142 : Nat := 4983230072969 + 3 ^ 40 * 7350142 * 2
def baseEnd_7350142 : Nat := 3774155724799286769322319

theorem tailTrace_7350142 : CollatzResearch.WordTrace tailWord_7350142 prefixEnd_7350142 3774155724799286769322319 := by
  unfold tailWord_7350142
  simp only [CollatzResearch.WordTrace]
  refine ⟨33510212817212289144853585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178721135025132208772552453 33510212817212289144853585)
  ·
    refine ⟨25132659612909216858640189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33510212817212289144853585 25132659612909216858640189)
    ·
      refine ⟨9424747354840956321990071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25132659612909216858640189 9424747354840956321990071)
      ·
        refine ⟨14137121032261434482985107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424747354840956321990071 14137121032261434482985107)
        ·
          refine ⟨21205681548392151724477661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137121032261434482985107 21205681548392151724477661)
          ·
            refine ⟨7952130580647056896679123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21205681548392151724477661 7952130580647056896679123)
            ·
              refine ⟨11928195870970585345018685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952130580647056896679123 11928195870970585345018685)
              ·
                refine ⟨4473073451613969504382007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11928195870970585345018685 4473073451613969504382007)
                ·
                  refine ⟨6709610177420954256573011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473073451613969504382007 6709610177420954256573011)
                  ·
                    refine ⟨10064415266131431384859517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709610177420954256573011 10064415266131431384859517)
                    ·
                      refine ⟨3774155724799286769322319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064415266131431384859517 3774155724799286769322319)
                      ·
                        rfl

theorem cell23_7350142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_7350142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350142 prefixEnd_7350142 := by exact prefixLift 7350142
  have htrace : WordTrace (prefixWord ++ tailWord_7350142) baseStart_7350142 baseEnd_7350142 := by
    simpa [prefixWord, tailWord_7350142, baseEnd_7350142] using wordTrace_append hprefix tailTrace_7350142
  have hstable : (prefixWord ++ tailWord_7350142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350142).length < 2 ^ (prefixWord ++ tailWord_7350142).sum := by decide
  have hdescent : baseEnd_7350142 < baseStart_7350142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350154 : List Nat := [3, 1, 2, 4, 2, 2, 9]
def baseStart_7350154 : Nat := 118140960795 + 7350154 * 2 ^ 59
def prefixEnd_7350154 : Nat := 4983230072969 + 3 ^ 40 * 7350154 * 2
def baseEnd_7350154 : Nat := 46594591192186922498423

theorem tailTrace_7350154 : CollatzResearch.WordTrace tailWord_7350154 prefixEnd_7350154 46594591192186922498423 := by
  unfold tailWord_7350154
  simp only [CollatzResearch.WordTrace]
  refine ⟨67020535053413709802066379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178721426809103226138843677 67020535053413709802066379)
  ·
    refine ⟨100530802580120564703099569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67020535053413709802066379 100530802580120564703099569)
    ·
      refine ⟨75398101935090423527324677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100530802580120564703099569 75398101935090423527324677)
      ·
        refine ⟨14137144112829454411373377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75398101935090423527324677 14137144112829454411373377)
        ·
          refine ⟨10602858084622090808530033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14137144112829454411373377 10602858084622090808530033)
          ·
            refine ⟨7952143563466568106397525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10602858084622090808530033 7952143563466568106397525)
            ·
              refine ⟨46594591192186922498423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7952143563466568106397525 46594591192186922498423)
              ·
                rfl

theorem cell23_7350154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 9].length) (baseStart_7350154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350154 prefixEnd_7350154 := by exact prefixLift 7350154
  have htrace : WordTrace (prefixWord ++ tailWord_7350154) baseStart_7350154 baseEnd_7350154 := by
    simpa [prefixWord, tailWord_7350154, baseEnd_7350154] using wordTrace_append hprefix tailTrace_7350154
  have hstable : (prefixWord ++ tailWord_7350154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350154).length < 2 ^ (prefixWord ++ tailWord_7350154).sum := by decide
  have hdescent : baseEnd_7350154 < baseStart_7350154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350165 : List Nat := [1, 3, 2, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_7350165 : Nat := 118140960795 + 7350165 * 2 ^ 59
def prefixEnd_7350165 : Nat := 4983230072969 + 3 ^ 40 * 7350165 * 2
def baseEnd_7350165 : Nat := 3774167534854340179334713

theorem tailTrace_7350165 : CollatzResearch.WordTrace tailWord_7350165 prefixEnd_7350165 3774167534854340179334713 := by
  unfold tailWord_7350165
  simp only [CollatzResearch.WordTrace]
  refine ⟨268082541416614988086915949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178721694277743325391277299 268082541416614988086915949)
  ·
    refine ⟨100530953031230620532593481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268082541416614988086915949 100530953031230620532593481)
    ·
      refine ⟨75398214773422965399445111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100530953031230620532593481 75398214773422965399445111)
      ·
        refine ⟨113097322160134448099167667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75398214773422965399445111 113097322160134448099167667)
        ·
          refine ⟨169645983240201672148751501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113097322160134448099167667 169645983240201672148751501)
          ·
            refine ⟨63617243715075627055781813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169645983240201672148751501 63617243715075627055781813)
            ·
              refine ⟨5964116598288340036479545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63617243715075627055781813 5964116598288340036479545)
              ·
                refine ⟨4473087448716255027359659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964116598288340036479545 4473087448716255027359659)
                ·
                  refine ⟨6709631173074382541039489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473087448716255027359659 6709631173074382541039489)
                  ·
                    refine ⟨5032223379805786905779617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6709631173074382541039489 5032223379805786905779617)
                    ·
                      refine ⟨3774167534854340179334713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032223379805786905779617 3774167534854340179334713)
                      ·
                        rfl

theorem cell23_7350165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_7350165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350165 prefixEnd_7350165 := by exact prefixLift 7350165
  have htrace : WordTrace (prefixWord ++ tailWord_7350165) baseStart_7350165 baseEnd_7350165 := by
    simpa [prefixWord, tailWord_7350165, baseEnd_7350165] using wordTrace_append hprefix tailTrace_7350165
  have hstable : (prefixWord ++ tailWord_7350165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350165).length < 2 ^ (prefixWord ++ tailWord_7350165).sum := by decide
  have hdescent : baseEnd_7350165 < baseStart_7350165 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350175 : List Nat := [1, 1, 2, 5, 4, 1, 2, 1, 2, 4]
def baseStart_7350175 : Nat := 118140960795 + 7350175 * 2 ^ 59
def prefixEnd_7350175 : Nat := 4983230072969 + 3 ^ 40 * 7350175 * 2
def baseEnd_7350175 : Nat := 1258057556553628380069889

theorem tailTrace_7350175 : CollatzResearch.WordTrace tailWord_7350175 prefixEnd_7350175 1258057556553628380069889 := by
  unfold tailWord_7350175
  simp only [CollatzResearch.WordTrace]
  refine ⟨268082906146578759794779979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178721937431052506529853319 268082906146578759794779979)
  ·
    refine ⟨402124359219868139692169969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268082906146578759794779979 402124359219868139692169969)
    ·
      refine ⟨301593269414901104769127477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402124359219868139692169969 301593269414901104769127477)
      ·
        refine ⟨28274369007646978572105701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301593269414901104769127477 28274369007646978572105701)
        ·
          refine ⟨5301444188933808482269819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28274369007646978572105701 5301444188933808482269819)
          ·
            refine ⟨7952166283400712723404729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301444188933808482269819 7952166283400712723404729)
            ·
              refine ⟨5964124712550534542553547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952166283400712723404729 5964124712550534542553547)
              ·
                refine ⟨8946187068825801813830321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964124712550534542553547 8946187068825801813830321)
                ·
                  refine ⟨6709640301619351360372741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946187068825801813830321 6709640301619351360372741)
                  ·
                    refine ⟨1258057556553628380069889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709640301619351360372741 1258057556553628380069889)
                    ·
                      rfl

theorem cell23_7350175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 2, 4].length) (baseStart_7350175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350175 prefixEnd_7350175 := by exact prefixLift 7350175
  have htrace : WordTrace (prefixWord ++ tailWord_7350175) baseStart_7350175 baseEnd_7350175 := by
    simpa [prefixWord, tailWord_7350175, baseEnd_7350175] using wordTrace_append hprefix tailTrace_7350175
  have hstable : (prefixWord ++ tailWord_7350175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350175).length < 2 ^ (prefixWord ++ tailWord_7350175).sum := by decide
  have hdescent : baseEnd_7350175 < baseStart_7350175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350207 : List Nat := [1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5]
def baseStart_7350207 : Nat := 118140960795 + 7350207 * 2 ^ 59
def prefixEnd_7350207 : Nat := 4983230072969 + 3 ^ 40 * 7350207 * 2
def baseEnd_7350207 : Nat := 3774189101041829015009519

theorem tailTrace_7350207 : CollatzResearch.WordTrace tailWord_7350207 prefixEnd_7350207 3774189101041829015009519 := by
  unfold tailWord_7350207
  simp only [CollatzResearch.WordTrace]
  refine ⟨268084073282462829259944875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178722715521641886173296583 268084073282462829259944875)
  ·
    refine ⟨402126109923694243889917313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268084073282462829259944875 402126109923694243889917313)
    ·
      refine ⟨301594582442770682917437985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402126109923694243889917313 301594582442770682917437985)
      ·
        refine ⟨226195936832078012188078489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301594582442770682917437985 226195936832078012188078489)
        ·
          refine ⟨169646952624058509141058867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226195936832078012188078489 169646952624058509141058867)
          ·
            refine ⟨254470428936087763711588301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169646952624058509141058867 254470428936087763711588301)
            ·
              refine ⟨95426410851032911391845613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254470428936087763711588301 95426410851032911391845613)
              ·
                refine ⟨35784904069137341771942105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95426410851032911391845613 35784904069137341771942105)
                ·
                  refine ⟨26838678051853006328956579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35784904069137341771942105 26838678051853006328956579)
                  ·
                    refine ⟨40258017077779509493434869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26838678051853006328956579 40258017077779509493434869)
                    ·
                      refine ⟨3774189101041829015009519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40258017077779509493434869 3774189101041829015009519)
                      ·
                        rfl

theorem cell23_7350207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_7350207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350207 prefixEnd_7350207 := by exact prefixLift 7350207
  have htrace : WordTrace (prefixWord ++ tailWord_7350207) baseStart_7350207 baseEnd_7350207 := by
    simpa [prefixWord, tailWord_7350207, baseEnd_7350207] using wordTrace_append hprefix tailTrace_7350207
  have hstable : (prefixWord ++ tailWord_7350207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350207).length < 2 ^ (prefixWord ++ tailWord_7350207).sum := by decide
  have hdescent : baseEnd_7350207 < baseStart_7350207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350208 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2]
def baseStart_7350208 : Nat := 118140960795 + 7350208 * 2 ^ 59
def prefixEnd_7350208 : Nat := 4983230072969 + 3 ^ 40 * 7350208 * 2
def baseEnd_7350208 : Nat := 3774189614522483511097015

theorem tailTrace_7350208 : CollatzResearch.WordTrace tailWord_7350208 prefixEnd_7350208 3774189614522483511097015 := by
  unfold tailWord_7350208
  simp only [CollatzResearch.WordTrace]
  refine ⟨134042054877729603215365639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178722739836972804287154185 134042054877729603215365639)
  ·
    refine ⟨201063082316594404823048459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134042054877729603215365639 201063082316594404823048459)
    ·
      refine ⟨301594623474891607234572689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201063082316594404823048459 301594623474891607234572689)
      ·
        refine ⟨226195967606168705425929517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301594623474891607234572689 226195967606168705425929517)
        ·
          refine ⟨84823487852313264534723569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226195967606168705425929517 84823487852313264534723569)
          ·
            refine ⟨63617615889234948401042677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84823487852313264534723569 63617615889234948401042677)
            ·
              refine ⟨5964151489615776412597751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63617615889234948401042677 5964151489615776412597751)
              ·
                refine ⟨8946227234423664618896627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964151489615776412597751 8946227234423664618896627)
                ·
                  refine ⟨13419340851635496928344941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946227234423664618896627 13419340851635496928344941)
                  ·
                    refine ⟨5032252819363311348129353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13419340851635496928344941 5032252819363311348129353)
                    ·
                      refine ⟨3774189614522483511097015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032252819363311348129353 3774189614522483511097015)
                      ·
                        rfl

theorem cell23_7350208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 1, 3, 2].length) (baseStart_7350208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350208 prefixEnd_7350208 := by exact prefixLift 7350208
  have htrace : WordTrace (prefixWord ++ tailWord_7350208) baseStart_7350208 baseEnd_7350208 := by
    simpa [prefixWord, tailWord_7350208, baseEnd_7350208] using wordTrace_append hprefix tailTrace_7350208
  have hstable : (prefixWord ++ tailWord_7350208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350208).length < 2 ^ (prefixWord ++ tailWord_7350208).sum := by decide
  have hdescent : baseEnd_7350208 < baseStart_7350208 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350217 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 4]
def baseStart_7350217 : Nat := 118140960795 + 7350217 * 2 ^ 59
def prefixEnd_7350217 : Nat := 4983230072969 + 3 ^ 40 * 7350217 * 2
def baseEnd_7350217 : Nat := 3774194235848373975884473

theorem tailTrace_7350217 : CollatzResearch.WordTrace tailWord_7350217 prefixEnd_7350217 3774194235848373975884473 := by
  unfold tailWord_7350217
  simp only [CollatzResearch.WordTrace]
  refine ⟨268084438012426600967808905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178722958674951067311872603 268084438012426600967808905)
  ·
    refine ⟨201063328509319950725856679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268084438012426600967808905 201063328509319950725856679)
    ·
      refine ⟨301594992763979926088785019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201063328509319950725856679 301594992763979926088785019)
      ·
        refine ⟨452392489145969889133177529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301594992763979926088785019 452392489145969889133177529)
        ·
          refine ⟨339294366859477416849883147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 452392489145969889133177529 339294366859477416849883147)
          ·
            refine ⟨508941550289216125274824721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339294366859477416849883147 508941550289216125274824721)
            ·
              refine ⟨381706162716912093956118541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508941550289216125274824721 381706162716912093956118541)
              ·
                refine ⟨143139811018842035233544453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 381706162716912093956118541 143139811018842035233544453)
                ·
                  refine ⟨26838714566032881606289585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 143139811018842035233544453 26838714566032881606289585)
                  ·
                    refine ⟨20129035924524661204717189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26838714566032881606289585 20129035924524661204717189)
                    ·
                      refine ⟨3774194235848373975884473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20129035924524661204717189 3774194235848373975884473)
                      ·
                        rfl

theorem cell23_7350217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 2, 4].length) (baseStart_7350217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350217 prefixEnd_7350217 := by exact prefixLift 7350217
  have htrace : WordTrace (prefixWord ++ tailWord_7350217) baseStart_7350217 baseEnd_7350217 := by
    simpa [prefixWord, tailWord_7350217, baseEnd_7350217] using wordTrace_append hprefix tailTrace_7350217
  have hstable : (prefixWord ++ tailWord_7350217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350217).length < 2 ^ (prefixWord ++ tailWord_7350217).sum := by decide
  have hdescent : baseEnd_7350217 < baseStart_7350217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350267 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5]
def baseStart_7350267 : Nat := 118140960795 + 7350267 * 2 ^ 59
def prefixEnd_7350267 : Nat := 4983230072969 + 3 ^ 40 * 7350267 * 2
def baseEnd_7350267 : Nat := 3774219909881098780259243

theorem tailTrace_7350267 : CollatzResearch.WordTrace tailWord_7350267 prefixEnd_7350267 3774219909881098780259243 := by
  unfold tailWord_7350267
  simp only [CollatzResearch.WordTrace]
  refine ⟨268086261662245459507129055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178724174441496973004752703 268086261662245459507129055)
  ·
    refine ⟨402129392493368189260693583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268086261662245459507129055 402129392493368189260693583)
    ·
      refine ⟨603194088740052283891040375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402129392493368189260693583 603194088740052283891040375)
      ·
        refine ⟨904791133110078425836560563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603194088740052283891040375 904791133110078425836560563)
        ·
          refine ⟨1357186699665117638754840845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904791133110078425836560563 1357186699665117638754840845)
          ·
            refine ⟨508945012374419114533065317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1357186699665117638754840845 508945012374419114533065317)
            ·
              refine ⟨95427189820203583974949747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 508945012374419114533065317 95427189820203583974949747)
              ·
                refine ⟨143140784730305375962424621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95427189820203583974949747 143140784730305375962424621)
                ·
                  refine ⟨53677794273864515985909233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143140784730305375962424621 53677794273864515985909233)
                  ·
                    refine ⟨40258345705398386989431925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53677794273864515985909233 40258345705398386989431925)
                    ·
                      refine ⟨3774219909881098780259243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40258345705398386989431925 3774219909881098780259243)
                      ·
                        rfl

theorem cell23_7350267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 5].length) (baseStart_7350267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350267 prefixEnd_7350267 := by exact prefixLift 7350267
  have htrace : WordTrace (prefixWord ++ tailWord_7350267) baseStart_7350267 baseEnd_7350267 := by
    simpa [prefixWord, tailWord_7350267, baseEnd_7350267] using wordTrace_append hprefix tailTrace_7350267
  have hstable : (prefixWord ++ tailWord_7350267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350267).length < 2 ^ (prefixWord ++ tailWord_7350267).sum := by decide
  have hdescent : baseEnd_7350267 < baseStart_7350267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350312 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 5]
def baseStart_7350312 : Nat := 118140960795 + 7350312 * 2 ^ 59
def prefixEnd_7350312 : Nat := 4983230072969 + 3 ^ 40 * 7350312 * 2
def baseEnd_7350312 : Nat := 419360335167839011577393

theorem tailTrace_7350312 : CollatzResearch.WordTrace tailWord_7350312 prefixEnd_7350312 419360335167839011577393 := by
  unfold tailWord_7350312
  simp only [CollatzResearch.WordTrace]
  refine ⟨134043951473541216096258595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178725268631388288128344793 134043951473541216096258595)
  ·
    refine ⟨201065927210311824144387893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134043951473541216096258595 201065927210311824144387893)
    ·
      refine ⟨18849930675966733513536365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201065927210311824144387893 18849930675966733513536365)
      ·
        refine ⟨7068724003487525067576137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18849930675966733513536365 7068724003487525067576137)
        ·
          refine ⟨5301543002615643800682103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7068724003487525067576137 5301543002615643800682103)
          ·
            refine ⟨7952314503923465701023155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301543002615643800682103 7952314503923465701023155)
            ·
              refine ⟨11928471755885198551534733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952314503923465701023155 11928471755885198551534733)
              ·
                refine ⟨4473176908456949456825525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11928471755885198551534733 4473176908456949456825525)
                ·
                  refine ⟨419360335167839011577393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4473176908456949456825525 419360335167839011577393)
                  ·
                    rfl

theorem cell23_7350312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 5].length) (baseStart_7350312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350312 prefixEnd_7350312 := by exact prefixLift 7350312
  have htrace : WordTrace (prefixWord ++ tailWord_7350312) baseStart_7350312 baseEnd_7350312 := by
    simpa [prefixWord, tailWord_7350312, baseEnd_7350312] using wordTrace_append hprefix tailTrace_7350312
  have hstable : (prefixWord ++ tailWord_7350312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350312).length < 2 ^ (prefixWord ++ tailWord_7350312).sum := by decide
  have hdescent : baseEnd_7350312 < baseStart_7350312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350344 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_7350344 : Nat := 118140960795 + 7350344 * 2 ^ 59
def prefixEnd_7350344 : Nat := 4983230072969 + 3 ^ 40 * 7350344 * 2
def baseEnd_7350344 : Nat := 3774259447891494978996389

theorem tailTrace_7350344 : CollatzResearch.WordTrace tailWord_7350344 prefixEnd_7350344 3774259447891494978996389 := by
  unfold tailWord_7350344
  simp only [CollatzResearch.WordTrace]
  refine ⟨134044535041483250828841043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178726046721977667771788057 134044535041483250828841043)
  ·
    refine ⟨201066802562224876243261565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134044535041483250828841043 201066802562224876243261565)
    ·
      refine ⟨75400050960834328591223087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201066802562224876243261565 75400050960834328591223087)
      ·
        refine ⟨113100076441251492886834631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75400050960834328591223087 113100076441251492886834631)
        ·
          refine ⟨169650114661877239330251947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113100076441251492886834631 169650114661877239330251947)
          ·
            refine ⟨254475171992815858995377921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169650114661877239330251947 254475171992815858995377921)
            ·
              refine ⟨190856378994611894246533441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254475171992815858995377921 190856378994611894246533441)
              ·
                refine ⟨143142284245958920684900081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190856378994611894246533441 143142284245958920684900081)
                ·
                  refine ⟨107356713184469190513675061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143142284245958920684900081 107356713184469190513675061)
                  ·
                    refine ⟨10064691861043986610657037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107356713184469190513675061 10064691861043986610657037)
                    ·
                      refine ⟨3774259447891494978996389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064691861043986610657037 3774259447891494978996389)
                      ·
                        rfl

theorem cell23_7350344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_7350344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350344 prefixEnd_7350344 := by exact prefixLift 7350344
  have htrace : WordTrace (prefixWord ++ tailWord_7350344) baseStart_7350344 baseEnd_7350344 := by
    simpa [prefixWord, tailWord_7350344, baseEnd_7350344] using wordTrace_append hprefix tailTrace_7350344
  have hstable : (prefixWord ++ tailWord_7350344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350344).length < 2 ^ (prefixWord ++ tailWord_7350344).sum := by decide
  have hdescent : baseEnd_7350344 < baseStart_7350344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350361 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 3]
def baseStart_7350361 : Nat := 118140960795 + 7350361 * 2 ^ 59
def prefixEnd_7350361 : Nat := 4983230072969 + 3 ^ 40 * 7350361 * 2
def baseEnd_7350361 : Nat := 3774268177062621412483811

theorem tailTrace_7350361 : CollatzResearch.WordTrace tailWord_7350361 prefixEnd_7350361 3774268177062621412483811 := by
  unfold tailWord_7350361
  simp only [CollatzResearch.WordTrace]
  refine ⟨268089690123904913561050937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178726460082603275707367291 268089690123904913561050937)
  ·
    refine ⟨201067267592928685170788203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268089690123904913561050937 201067267592928685170788203)
    ·
      refine ⟨301600901389393027756182305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201067267592928685170788203 301600901389393027756182305)
      ·
        refine ⟨226200676042044770817136729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301600901389393027756182305 226200676042044770817136729)
        ·
          refine ⟨169650507031533578112852547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226200676042044770817136729 169650507031533578112852547)
          ·
            refine ⟨254475760547300367169278821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169650507031533578112852547 254475760547300367169278821)
            ·
              refine ⟨47714205102618818844239779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254475760547300367169278821 47714205102618818844239779)
              ·
                refine ⟨71571307653928228266359669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47714205102618818844239779 71571307653928228266359669)
                ·
                  refine ⟨6709810092555771399971219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71571307653928228266359669 6709810092555771399971219)
                  ·
                    refine ⟨10064715138833657099956829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6709810092555771399971219 10064715138833657099956829)
                    ·
                      refine ⟨3774268177062621412483811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064715138833657099956829 3774268177062621412483811)
                      ·
                        rfl

theorem cell23_7350361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 3].length) (baseStart_7350361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350361 prefixEnd_7350361 := by exact prefixLift 7350361
  have htrace : WordTrace (prefixWord ++ tailWord_7350361) baseStart_7350361 baseEnd_7350361 := by
    simpa [prefixWord, tailWord_7350361, baseEnd_7350361] using wordTrace_append hprefix tailTrace_7350361
  have hstable : (prefixWord ++ tailWord_7350361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350361).length < 2 ^ (prefixWord ++ tailWord_7350361).sum := by decide
  have hdescent : baseEnd_7350361 < baseStart_7350361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350365 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7350365 : Nat := 118140960795 + 7350365 * 2 ^ 59
def prefixEnd_7350365 : Nat := 4983230072969 + 3 ^ 40 * 7350365 * 2
def baseEnd_7350365 : Nat := 3774270230985239396833793

theorem tailTrace_7350365 : CollatzResearch.WordTrace tailWord_7350365 prefixEnd_7350365 3774270230985239396833793 := by
  unfold tailWord_7350365
  simp only [CollatzResearch.WordTrace]
  refine ⟨268089836015890422244196549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178726557343926948162797699 268089836015890422244196549)
  ·
    refine ⟨50266844252979454170786853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 268089836015890422244196549 50266844252979454170786853)
    ·
      refine ⟨9425033297433647657022535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50266844252979454170786853 9425033297433647657022535)
      ·
        refine ⟨14137549946150471485533803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425033297433647657022535 14137549946150471485533803)
        ·
          refine ⟨21206324919225707228300705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137549946150471485533803 21206324919225707228300705)
          ·
            refine ⟨15904743689419280421225529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21206324919225707228300705 15904743689419280421225529)
            ·
              refine ⟨11928557767064460315919147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15904743689419280421225529 11928557767064460315919147)
              ·
                refine ⟨17892836650596690473878721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11928557767064460315919147 17892836650596690473878721)
                ·
                  refine ⟨13419627487947517855409041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17892836650596690473878721 13419627487947517855409041)
                  ·
                    refine ⟨10064720615960638391556781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13419627487947517855409041 10064720615960638391556781)
                    ·
                      refine ⟨3774270230985239396833793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064720615960638391556781 3774270230985239396833793)
                      ·
                        rfl

theorem cell23_7350365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7350365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350365 prefixEnd_7350365 := by exact prefixLift 7350365
  have htrace : WordTrace (prefixWord ++ tailWord_7350365) baseStart_7350365 baseEnd_7350365 := by
    simpa [prefixWord, tailWord_7350365, baseEnd_7350365] using wordTrace_append hprefix tailTrace_7350365
  have hstable : (prefixWord ++ tailWord_7350365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350365).length < 2 ^ (prefixWord ++ tailWord_7350365).sum := by decide
  have hdescent : baseEnd_7350365 < baseStart_7350365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350371 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 1, 5, 2]
def baseStart_7350371 : Nat := 118140960795 + 7350371 * 2 ^ 59
def prefixEnd_7350371 : Nat := 4983230072969 + 3 ^ 40 * 7350371 * 2
def baseEnd_7350371 : Nat := 3774273311869166373358765

theorem tailTrace_7350371 : CollatzResearch.WordTrace tailWord_7350371 prefixEnd_7350371 3774273311869166373358765 := by
  unfold tailWord_7350371
  simp only [CollatzResearch.WordTrace]
  refine ⟨268090054853868685268914967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178726703235912456845943311 268090054853868685268914967)
  ·
    refine ⟨402135082280803027903372451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268090054853868685268914967 402135082280803027903372451)
    ·
      refine ⟨603202623421204541855058677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402135082280803027903372451 603202623421204541855058677)
      ·
        refine ⟨56550245945737925798911751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 603202623421204541855058677 56550245945737925798911751)
        ·
          refine ⟨84825368918606888698367627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56550245945737925798911751 84825368918606888698367627)
          ·
            refine ⟨127238053377910333047551441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84825368918606888698367627 127238053377910333047551441)
            ·
              refine ⟨95428540033432749785663581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127238053377910333047551441 95428540033432749785663581)
              ·
                refine ⟨35785702512537281169623843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95428540033432749785663581 35785702512537281169623843)
                ·
                  refine ⟨53678553768805921754435765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35785702512537281169623843 53678553768805921754435765)
                  ·
                    refine ⟨5032364415825555164478353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53678553768805921754435765 5032364415825555164478353)
                    ·
                      refine ⟨3774273311869166373358765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032364415825555164478353 3774273311869166373358765)
                      ·
                        rfl

theorem cell23_7350371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_7350371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350371 prefixEnd_7350371 := by exact prefixLift 7350371
  have htrace : WordTrace (prefixWord ++ tailWord_7350371) baseStart_7350371 baseEnd_7350371 := by
    simpa [prefixWord, tailWord_7350371, baseEnd_7350371] using wordTrace_append hprefix tailTrace_7350371
  have hstable : (prefixWord ++ tailWord_7350371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350371).length < 2 ^ (prefixWord ++ tailWord_7350371).sum := by decide
  have hdescent : baseEnd_7350371 < baseStart_7350371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350418 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_7350418 : Nat := 118140960795 + 7350418 * 2 ^ 59
def prefixEnd_7350418 : Nat := 4983230072969 + 3 ^ 40 * 7350418 * 2
def baseEnd_7350418 : Nat := 3774297445459927689471049

theorem tailTrace_7350418 : CollatzResearch.WordTrace tailWord_7350418 prefixEnd_7350418 3774297445459927689471049 := by
  unfold tailWord_7350418
  simp only [CollatzResearch.WordTrace]
  refine ⟨67022942271174603073968977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178727846056465608197250605 67022942271174603073968977)
  ·
    refine ⟨50267206703380952305476733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67022942271174603073968977 50267206703380952305476733)
    ·
      refine ⟨18850202513767857114553775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50267206703380952305476733 18850202513767857114553775)
      ·
        refine ⟨28275303770651785671830663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18850202513767857114553775 28275303770651785671830663)
        ·
          refine ⟨42412955655977678507745995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28275303770651785671830663 42412955655977678507745995)
          ·
            refine ⟨63619433483966517761618993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42412955655977678507745995 63619433483966517761618993)
            ·
              refine ⟨47714575112974888321214245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63619433483966517761618993 47714575112974888321214245)
              ·
                refine ⟨8946482833682791560227671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47714575112974888321214245 8946482833682791560227671)
                ·
                  refine ⟨13419724250524187340341507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946482833682791560227671 13419724250524187340341507)
                  ·
                    refine ⟨20129586375786281010512261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13419724250524187340341507 20129586375786281010512261)
                    ·
                      refine ⟨3774297445459927689471049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20129586375786281010512261 3774297445459927689471049)
                      ·
                        rfl

theorem cell23_7350418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_7350418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350418 prefixEnd_7350418 := by exact prefixLift 7350418
  have htrace : WordTrace (prefixWord ++ tailWord_7350418) baseStart_7350418 baseEnd_7350418 := by
    simpa [prefixWord, tailWord_7350418, baseEnd_7350418] using wordTrace_append hprefix tailTrace_7350418
  have hstable : (prefixWord ++ tailWord_7350418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350418).length < 2 ^ (prefixWord ++ tailWord_7350418).sum := by decide
  have hdescent : baseEnd_7350418 < baseStart_7350418 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350421 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_7350421 : Nat := 118140960795 + 7350421 * 2 ^ 59
def prefixEnd_7350421 : Nat := 4983230072969 + 3 ^ 40 * 7350421 * 2
def baseEnd_7350421 : Nat := 3774298985901891177733535

theorem tailTrace_7350421 : CollatzResearch.WordTrace tailWord_7350421 prefixEnd_7350421 3774298985901891177733535 := by
  unfold tailWord_7350421
  simp only [CollatzResearch.WordTrace]
  refine ⟨268091878503687543808235117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178727919002458362538823411 268091878503687543808235117)
  ·
    refine ⟨100534454438882828928088169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268091878503687543808235117 100534454438882828928088169)
    ·
      refine ⟨75400840829162121696066127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100534454438882828928088169 75400840829162121696066127)
      ·
        refine ⟨113101261243743182544099191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75400840829162121696066127 113101261243743182544099191)
        ·
          refine ⟨169651891865614773816148787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113101261243743182544099191 169651891865614773816148787)
          ·
            refine ⟨254477837798422160724223181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169651891865614773816148787 254477837798422160724223181)
            ·
              refine ⟨95429189174408310271583693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254477837798422160724223181 95429189174408310271583693)
              ·
                refine ⟨35785945940403116351843885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95429189174408310271583693 35785945940403116351843885)
                ·
                  refine ⟨13419729727651168631941457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35785945940403116351843885 13419729727651168631941457)
                  ·
                    refine ⟨10064797295738376473956093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13419729727651168631941457 10064797295738376473956093)
                    ·
                      refine ⟨3774298985901891177733535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10064797295738376473956093 3774298985901891177733535)
                      ·
                        rfl

theorem cell23_7350421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_7350421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350421 prefixEnd_7350421 := by exact prefixLift 7350421
  have htrace : WordTrace (prefixWord ++ tailWord_7350421) baseStart_7350421 baseEnd_7350421 := by
    simpa [prefixWord, tailWord_7350421, baseEnd_7350421] using wordTrace_append hprefix tailTrace_7350421
  have hstable : (prefixWord ++ tailWord_7350421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350421).length < 2 ^ (prefixWord ++ tailWord_7350421).sum := by decide
  have hdescent : baseEnd_7350421 < baseStart_7350421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350445 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 2, 4]
def baseStart_7350445 : Nat := 118140960795 + 7350445 * 2 ^ 59
def prefixEnd_7350445 : Nat := 4983230072969 + 3 ^ 40 * 7350445 * 2
def baseEnd_7350445 : Nat := 1258103769812533027944475

theorem tailTrace_7350445 : CollatzResearch.WordTrace tailWord_7350445 prefixEnd_7350445 1258103769812533027944475 := by
  unfold tailWord_7350445
  simp only [CollatzResearch.WordTrace]
  refine ⟨268092753855600595907108789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178728502570400397271405859 268092753855600595907108789)
  ·
    refine ⟨25133695673962555866291449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 268092753855600595907108789 25133695673962555866291449)
    ·
      refine ⟨18850271755471916899718587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25133695673962555866291449 18850271755471916899718587)
      ·
        refine ⟨28275407633207875349577881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18850271755471916899718587 28275407633207875349577881)
        ·
          refine ⟨21206555724905906512183411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28275407633207875349577881 21206555724905906512183411)
          ·
            refine ⟨31809833587358859768275117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21206555724905906512183411 31809833587358859768275117)
            ·
              refine ⟨11928687595259572413103169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31809833587358859768275117 11928687595259572413103169)
              ·
                refine ⟨8946515696444679309827377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11928687595259572413103169 8946515696444679309827377)
                ·
                  refine ⟨6709886772333509482370533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946515696444679309827377 6709886772333509482370533)
                  ·
                    refine ⟨1258103769812533027944475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709886772333509482370533 1258103769812533027944475)
                    ·
                      rfl

theorem cell23_7350445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_7350445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350445 prefixEnd_7350445 := by exact prefixLift 7350445
  have htrace : WordTrace (prefixWord ++ tailWord_7350445) baseStart_7350445 baseEnd_7350445 := by
    simpa [prefixWord, tailWord_7350445, baseEnd_7350445] using wordTrace_append hprefix tailTrace_7350445
  have hstable : (prefixWord ++ tailWord_7350445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350445).length < 2 ^ (prefixWord ++ tailWord_7350445).sum := by decide
  have hdescent : baseEnd_7350445 < baseStart_7350445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350462 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 2, 4]
def baseStart_7350462 : Nat := 118140960795 + 7350462 * 2 ^ 59
def prefixEnd_7350462 : Nat := 4983230072969 + 3 ^ 40 * 7350462 * 2
def baseEnd_7350462 : Nat := 1258106679536241839106949

theorem tailTrace_7350462 : CollatzResearch.WordTrace tailWord_7350462 prefixEnd_7350462 1258106679536241839106949 := by
  unfold tailWord_7350462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33511671737067375976309705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178728915931026005206985093 33511671737067375976309705)
  ·
    refine ⟨25133753802800531982232279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33511671737067375976309705 25133753802800531982232279)
    ·
      refine ⟨37700630704200797973348419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25133753802800531982232279 37700630704200797973348419)
      ·
        refine ⟨56550946056301196960022629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37700630704200797973348419 56550946056301196960022629)
        ·
          refine ⟨10603302385556474430004243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56550946056301196960022629 10603302385556474430004243)
          ·
            refine ⟨15904953578334711645006365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603302385556474430004243 15904953578334711645006365)
            ·
              refine ⟨5964357591875516866877387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15904953578334711645006365 5964357591875516866877387)
              ·
                refine ⟨8946536387813275300316081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964357591875516866877387 8946536387813275300316081)
                ·
                  refine ⟨6709902290859956475237061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8946536387813275300316081 6709902290859956475237061)
                  ·
                    refine ⟨1258106679536241839106949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709902290859956475237061 1258106679536241839106949)
                    ·
                      rfl

theorem cell23_7350462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_7350462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350462 prefixEnd_7350462 := by exact prefixLift 7350462
  have htrace : WordTrace (prefixWord ++ tailWord_7350462) baseStart_7350462 baseEnd_7350462 := by
    simpa [prefixWord, tailWord_7350462, baseEnd_7350462] using wordTrace_append hprefix tailTrace_7350462
  have hstable : (prefixWord ++ tailWord_7350462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350462).length < 2 ^ (prefixWord ++ tailWord_7350462).sum := by decide
  have hdescent : baseEnd_7350462 < baseStart_7350462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350486 : List Nat := [5, 2, 1, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_7350486 : Nat := 118140960795 + 7350486 * 2 ^ 59
def prefixEnd_7350486 : Nat := 4983230072969 + 3 ^ 40 * 7350486 * 2
def baseEnd_7350486 : Nat := 3774332362144433423420737

theorem tailTrace_7350486 : CollatzResearch.WordTrace tailWord_7350486 prefixEnd_7350486 3774332362144433423420737 := by
  unfold tailWord_7350486
  simp only [CollatzResearch.WordTrace]
  refine ⟨16755890578028253744334457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178729499498968039939567541 16755890578028253744334457)
  ·
    refine ⟨12566917933521190308250843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16755890578028253744334457 12566917933521190308250843)
    ·
      refine ⟨18850376900281785462376265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12566917933521190308250843 18850376900281785462376265)
      ·
        refine ⟨14137782675211339096782199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18850376900281785462376265 14137782675211339096782199)
        ·
          refine ⟨21206674012817008645173299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137782675211339096782199 21206674012817008645173299)
          ·
            refine ⟨31810011019225512967759949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21206674012817008645173299 31810011019225512967759949)
            ·
              refine ⟨11928754132209567362909981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31810011019225512967759949 11928754132209567362909981)
              ·
                refine ⟨4473282799578587761091243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11928754132209567362909981 4473282799578587761091243)
                ·
                  refine ⟨6709924199367881641636865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473282799578587761091243 6709924199367881641636865)
                  ·
                    refine ⟨5032443149525911231227649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6709924199367881641636865 5032443149525911231227649)
                    ·
                      refine ⟨3774332362144433423420737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032443149525911231227649 3774332362144433423420737)
                      ·
                        rfl

theorem cell23_7350486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_7350486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350486 prefixEnd_7350486 := by exact prefixLift 7350486
  have htrace : WordTrace (prefixWord ++ tailWord_7350486) baseStart_7350486 baseEnd_7350486 := by
    simpa [prefixWord, tailWord_7350486, baseEnd_7350486] using wordTrace_append hprefix tailTrace_7350486
  have hstable : (prefixWord ++ tailWord_7350486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350486).length < 2 ^ (prefixWord ++ tailWord_7350486).sum := by decide
  have hdescent : baseEnd_7350486 < baseStart_7350486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350565 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 5]
def baseStart_7350565 : Nat := 118140960795 + 7350565 * 2 ^ 59
def prefixEnd_7350565 : Nat := 4983230072969 + 3 ^ 40 * 7350565 * 2
def baseEnd_7350565 : Nat := 419374769679570957148097

theorem tailTrace_7350565 : CollatzResearch.WordTrace tailWord_7350565 prefixEnd_7350565 419374769679570957148097 := by
  unfold tailWord_7350565
  simp only [CollatzResearch.WordTrace]
  refine ⟨268097130615165856401477149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178731420410110570934318099 268097130615165856401477149)
  ·
    refine ⟨100536423980687196150553931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268097130615165856401477149 100536423980687196150553931)
    ·
      refine ⟨150804635971030794225830897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100536423980687196150553931 150804635971030794225830897)
      ·
        refine ⟨113103476978273095669373173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150804635971030794225830897 113103476978273095669373173)
        ·
          refine ⟨10603450966713102719003735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113103476978273095669373173 10603450966713102719003735)
          ·
            refine ⟨15905176450069654078505603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603450966713102719003735 15905176450069654078505603)
            ·
              refine ⟨23857764675104481117758405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15905176450069654078505603 23857764675104481117758405)
              ·
                refine ⟨4473330876582090209579701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23857764675104481117758405 4473330876582090209579701)
                ·
                  refine ⟨419374769679570957148097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4473330876582090209579701 419374769679570957148097)
                  ·
                    rfl

theorem cell23_7350565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 5].length) (baseStart_7350565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350565 prefixEnd_7350565 := by exact prefixLift 7350565
  have htrace : WordTrace (prefixWord ++ tailWord_7350565) baseStart_7350565 baseEnd_7350565 := by
    simpa [prefixWord, tailWord_7350565, baseEnd_7350565] using wordTrace_append hprefix tailTrace_7350565
  have hstable : (prefixWord ++ tailWord_7350565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350565).length < 2 ^ (prefixWord ++ tailWord_7350565).sum := by decide
  have hdescent : baseEnd_7350565 < baseStart_7350565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350618 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3]
def baseStart_7350618 : Nat := 118140960795 + 7350618 * 2 ^ 59
def prefixEnd_7350618 : Nat := 4983230072969 + 3 ^ 40 * 7350618 * 2
def baseEnd_7350618 : Nat := 3774400141590826906970129

theorem tailTrace_7350618 : CollatzResearch.WordTrace tailWord_7350618 prefixEnd_7350618 3774400141590826906970129 := by
  unfold tailWord_7350618
  simp only [CollatzResearch.WordTrace]
  refine ⟨67024765920993461613289127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178732709122649230968771005 67024765920993461613289127)
  ·
    refine ⟨100537148881490192419933691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67024765920993461613289127 100537148881490192419933691)
    ·
      refine ⟨150805723322235288629900537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100537148881490192419933691 150805723322235288629900537)
      ·
        refine ⟨113104292491676466472425403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150805723322235288629900537 113104292491676466472425403)
        ·
          refine ⟨169656438737514699708638105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113104292491676466472425403 169656438737514699708638105)
          ·
            refine ⟨127242329053136024781478579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169656438737514699708638105 127242329053136024781478579)
            ·
              refine ⟨190863493579704037172217869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127242329053136024781478579 190863493579704037172217869)
              ·
                refine ⟨71573810092389013939581701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190863493579704037172217869 71573810092389013939581701)
                ·
                  refine ⟨13420089392322940113671569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71573810092389013939581701 13420089392322940113671569)
                  ·
                    refine ⟨10065067044242205085253677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13420089392322940113671569 10065067044242205085253677)
                    ·
                      refine ⟨3774400141590826906970129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10065067044242205085253677 3774400141590826906970129)
                      ·
                        rfl

theorem cell23_7350618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 2, 3].length) (baseStart_7350618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350618 prefixEnd_7350618 := by exact prefixLift 7350618
  have htrace : WordTrace (prefixWord ++ tailWord_7350618) baseStart_7350618 baseEnd_7350618 := by
    simpa [prefixWord, tailWord_7350618, baseEnd_7350618] using wordTrace_append hprefix tailTrace_7350618
  have hstable : (prefixWord ++ tailWord_7350618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350618).length < 2 ^ (prefixWord ++ tailWord_7350618).sum := by decide
  have hdescent : baseEnd_7350618 < baseStart_7350618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350641 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_7350641 : Nat := 118140960795 + 7350641 * 2 ^ 59
def prefixEnd_7350641 : Nat := 4983230072969 + 3 ^ 40 * 7350641 * 2
def baseEnd_7350641 : Nat := 3774411951645880316982523

theorem tailTrace_7350641 : CollatzResearch.WordTrace tailWord_7350641 prefixEnd_7350641 3774411951645880316982523 := by
  unfold tailWord_7350641
  simp only [CollatzResearch.WordTrace]
  refine ⟨268099902562890521381243777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178733268375260347587495851 268099902562890521381243777)
  ·
    refine ⟨201074926922167891035932833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268099902562890521381243777 201074926922167891035932833)
    ·
      refine ⟨150806195191625918276949625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201074926922167891035932833 150806195191625918276949625)
      ·
        refine ⟨113104646393719438707712219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150806195191625918276949625 113104646393719438707712219)
        ·
          refine ⟨169656969590579158061568329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113104646393719438707712219 169656969590579158061568329)
          ·
            refine ⟨127242727192934368546176247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169656969590579158061568329 127242727192934368546176247)
            ·
              refine ⟨190864090789401552819264371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127242727192934368546176247 190864090789401552819264371)
              ·
                refine ⟨286296136184102329228896557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190864090789401552819264371 286296136184102329228896557)
                ·
                  refine ⟨107361051069038373460836209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 286296136184102329228896557 107361051069038373460836209)
                  ·
                    refine ⟨80520788301778780095627157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107361051069038373460836209 80520788301778780095627157)
                    ·
                      refine ⟨3774411951645880316982523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80520788301778780095627157 3774411951645880316982523)
                      ·
                        rfl

theorem cell23_7350641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_7350641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350641 prefixEnd_7350641 := by exact prefixLift 7350641
  have htrace : WordTrace (prefixWord ++ tailWord_7350641) baseStart_7350641 baseEnd_7350641 := by
    simpa [prefixWord, tailWord_7350641, baseEnd_7350641] using wordTrace_append hprefix tailTrace_7350641
  have hstable : (prefixWord ++ tailWord_7350641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350641).length < 2 ^ (prefixWord ++ tailWord_7350641).sum := by decide
  have hdescent : baseEnd_7350641 < baseStart_7350641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350659 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 1, 4]
def baseStart_7350659 : Nat := 118140960795 + 7350659 * 2 ^ 59
def prefixEnd_7350659 : Nat := 4983230072969 + 3 ^ 40 * 7350659 * 2
def baseEnd_7350659 : Nat := 1258140398099220415519147

theorem tailTrace_7350659 : CollatzResearch.WordTrace tailWord_7350659 prefixEnd_7350659 1258140398099220415519147 := by
  unfold tailWord_7350659
  simp only [CollatzResearch.WordTrace]
  refine ⟨268100559076825310455399031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178733706051216873636932687 268100559076825310455399031)
  ·
    refine ⟨402150838615237965683098547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268100559076825310455399031 402150838615237965683098547)
    ·
      refine ⟨603226257922856948524647821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402150838615237965683098547 603226257922856948524647821)
      ·
        refine ⟨226209846721071355696742933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 603226257922856948524647821 226209846721071355696742933)
        ·
          refine ⟨10603586565050219798284825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 226209846721071355696742933 10603586565050219798284825)
          ·
            refine ⟨7952689923787664848713619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10603586565050219798284825 7952689923787664848713619)
            ·
              refine ⟨11929034885681497273070429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952689923787664848713619 11929034885681497273070429)
              ·
                refine ⟨4473388082130561477401411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11929034885681497273070429 4473388082130561477401411)
                ·
                  refine ⟨6710082123195842216102117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473388082130561477401411 6710082123195842216102117)
                  ·
                    refine ⟨1258140398099220415519147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710082123195842216102117 1258140398099220415519147)
                    ·
                      rfl

theorem cell23_7350659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 4].length) (baseStart_7350659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350659 prefixEnd_7350659 := by exact prefixLift 7350659
  have htrace : WordTrace (prefixWord ++ tailWord_7350659) baseStart_7350659 baseEnd_7350659 := by
    simpa [prefixWord, tailWord_7350659, baseEnd_7350659] using wordTrace_append hprefix tailTrace_7350659
  have hstable : (prefixWord ++ tailWord_7350659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350659).length < 2 ^ (prefixWord ++ tailWord_7350659).sum := by decide
  have hdescent : baseEnd_7350659 < baseStart_7350659 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350676 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 1, 4]
def baseStart_7350676 : Nat := 118140960795 + 7350676 * 2 ^ 59
def prefixEnd_7350676 : Nat := 4983230072969 + 3 ^ 40 * 7350676 * 2
def baseEnd_7350676 : Nat := 1258143307822929226681621

theorem tailTrace_7350676 : CollatzResearch.WordTrace tailWord_7350676 prefixEnd_7350676 1258143307822929226681621 := by
  unfold tailWord_7350676
  simp only [CollatzResearch.WordTrace]
  refine ⟨134050589558881861179383941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178734119411842481572511921 134050589558881861179383941)
  ·
    refine ⟨25134485542290348971134489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134050589558881861179383941 25134485542290348971134489)
    ·
      refine ⟨18850864156717761728350867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25134485542290348971134489 18850864156717761728350867)
      ·
        refine ⟨28276296235076642592526301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18850864156717761728350867 28276296235076642592526301)
        ·
          refine ⟨10603611088153740972197363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28276296235076642592526301 10603611088153740972197363)
          ·
            refine ⟨15905416632230611458296045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603611088153740972197363 15905416632230611458296045)
            ·
              refine ⟨5964531237086479296861017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15905416632230611458296045 5964531237086479296861017)
              ·
                refine ⟨4473398427814859472645763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5964531237086479296861017 4473398427814859472645763)
                ·
                  refine ⟨6710097641722289208968645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473398427814859472645763 6710097641722289208968645)
                  ·
                    refine ⟨1258143307822929226681621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710097641722289208968645 1258143307822929226681621)
                    ·
                      rfl

theorem cell23_7350676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_7350676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350676 prefixEnd_7350676 := by exact prefixLift 7350676
  have htrace : WordTrace (prefixWord ++ tailWord_7350676) baseStart_7350676 baseEnd_7350676 := by
    simpa [prefixWord, tailWord_7350676, baseEnd_7350676] using wordTrace_append hprefix tailTrace_7350676
  have hstable : (prefixWord ++ tailWord_7350676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350676).length < 2 ^ (prefixWord ++ tailWord_7350676).sum := by decide
  have hdescent : baseEnd_7350676 < baseStart_7350676 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350682 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3]
def baseStart_7350682 : Nat := 118140960795 + 7350682 * 2 ^ 59
def prefixEnd_7350682 : Nat := 4983230072969 + 3 ^ 40 * 7350682 * 2
def baseEnd_7350682 : Nat := 3774433004352714656569835

theorem tailTrace_7350682 : CollatzResearch.WordTrace tailWord_7350682 prefixEnd_7350682 3774433004352714656569835 := by
  unfold tailWord_7350682
  simp only [CollatzResearch.WordTrace]
  refine ⟨67025349488935496345871575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178734265303827990255657533 67025349488935496345871575)
  ·
    refine ⟨100538024233403244518807363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67025349488935496345871575 100538024233403244518807363)
    ·
      refine ⟨150807036350104866778211045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100538024233403244518807363 150807036350104866778211045)
      ·
        refine ⟨28276319315644662520914571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150807036350104866778211045 28276319315644662520914571)
        ·
          refine ⟨42414478973466993781371857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28276319315644662520914571 42414478973466993781371857)
          ·
            refine ⟨31810859230100245336028893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42414478973466993781371857 31810859230100245336028893)
            ·
              refine ⟨11929072211287592001010835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31810859230100245336028893 11929072211287592001010835)
              ·
                refine ⟨17893608316931388001516253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929072211287592001010835 17893608316931388001516253)
                ·
                  refine ⟨6710103118849270500568595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17893608316931388001516253 6710103118849270500568595)
                  ·
                    refine ⟨10065154678273905750852893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6710103118849270500568595 10065154678273905750852893)
                    ·
                      refine ⟨3774433004352714656569835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10065154678273905750852893 3774433004352714656569835)
                      ·
                        rfl

theorem cell23_7350682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_7350682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350682 prefixEnd_7350682 := by exact prefixLift 7350682
  have htrace : WordTrace (prefixWord ++ tailWord_7350682) baseStart_7350682 baseEnd_7350682 := by
    simpa [prefixWord, tailWord_7350682, baseEnd_7350682] using wordTrace_append hprefix tailTrace_7350682
  have hstable : (prefixWord ++ tailWord_7350682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350682).length < 2 ^ (prefixWord ++ tailWord_7350682).sum := by decide
  have hdescent : baseEnd_7350682 < baseStart_7350682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350689 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 6]
def baseStart_7350689 : Nat := 118140960795 + 7350689 * 2 ^ 59
def prefixEnd_7350689 : Nat := 4983230072969 + 3 ^ 40 * 7350689 * 2
def baseEnd_7350689 : Nat := 419381844301921792131367

theorem tailTrace_7350689 : CollatzResearch.WordTrace tailWord_7350689 prefixEnd_7350689 419381844301921792131367 := by
  unfold tailWord_7350689
  simp only [CollatzResearch.WordTrace]
  refine ⟨268101653266716625578991121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178734435511144417052660747 268101653266716625578991121)
  ·
    refine ⟨201076239950037469184243341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268101653266716625578991121 201076239950037469184243341)
    ·
      refine ⟨75403589981264050944091253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201076239950037469184243341 75403589981264050944091253)
      ·
        refine ⟨7069086560743504776008555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75403589981264050944091253 7069086560743504776008555)
        ·
          refine ⟨10603629841115257164012833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7069086560743504776008555 10603629841115257164012833)
          ·
            refine ⟨7952722380836442873009625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10603629841115257164012833 7952722380836442873009625)
            ·
              refine ⟨5964541785627332154757219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952722380836442873009625 5964541785627332154757219)
              ·
                refine ⟨8946812678440998232135829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964541785627332154757219 8946812678440998232135829)
                ·
                  refine ⟨419381844301921792131367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8946812678440998232135829 419381844301921792131367)
                  ·
                    rfl

theorem cell23_7350689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 6].length) (baseStart_7350689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350689 prefixEnd_7350689 := by exact prefixLift 7350689
  have htrace : WordTrace (prefixWord ++ tailWord_7350689) baseStart_7350689 baseEnd_7350689 := by
    simpa [prefixWord, tailWord_7350689, baseEnd_7350689] using wordTrace_append hprefix tailTrace_7350689
  have hstable : (prefixWord ++ tailWord_7350689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350689).length < 2 ^ (prefixWord ++ tailWord_7350689).sum := by decide
  have hdescent : baseEnd_7350689 < baseStart_7350689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350705 : List Nat := [1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7350705 : Nat := 118140960795 + 7350705 * 2 ^ 59
def prefixEnd_7350705 : Nat := 4983230072969 + 3 ^ 40 * 7350705 * 2
def baseEnd_7350705 : Nat := 3774444814407768066582229

theorem tailTrace_7350705 : CollatzResearch.WordTrace tailWord_7350705 prefixEnd_7350705 3774444814407768066582229 := by
  unfold tailWord_7350705
  simp only [CollatzResearch.WordTrace]
  refine ⟨268102236834658660311573569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178734824556439106874382379 268102236834658660311573569)
  ·
    refine ⟨201076677625993995233680177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268102236834658660311573569 201076677625993995233680177)
    ·
      refine ⟨150807508219495496425260133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201076677625993995233680177 150807508219495496425260133)
      ·
        refine ⟨28276407791155405579736275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150807508219495496425260133 28276407791155405579736275)
        ·
          refine ⟨42414611686733108369604413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28276407791155405579736275 42414611686733108369604413)
          ·
            refine ⟨15905479382524915638601655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42414611686733108369604413 15905479382524915638601655)
            ·
              refine ⟨23858219073787373457902483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15905479382524915638601655 23858219073787373457902483)
              ·
                refine ⟨35787328610681060186853725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23858219073787373457902483 35787328610681060186853725)
                ·
                  refine ⟨13420248229005397570070147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35787328610681060186853725 13420248229005397570070147)
                  ·
                    refine ⟨20130372343508096355105221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13420248229005397570070147 20130372343508096355105221)
                    ·
                      refine ⟨3774444814407768066582229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20130372343508096355105221 3774444814407768066582229)
                      ·
                        rfl

theorem cell23_7350705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7350705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350705 prefixEnd_7350705 := by exact prefixLift 7350705
  have htrace : WordTrace (prefixWord ++ tailWord_7350705) baseStart_7350705 baseEnd_7350705 := by
    simpa [prefixWord, tailWord_7350705, baseEnd_7350705] using wordTrace_append hprefix tailTrace_7350705
  have hstable : (prefixWord ++ tailWord_7350705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350705).length < 2 ^ (prefixWord ++ tailWord_7350705).sum := by decide
  have hdescent : baseEnd_7350705 < baseStart_7350705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350709 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_7350709 : Nat := 118140960795 + 7350709 * 2 ^ 59
def prefixEnd_7350709 : Nat := 4983230072969 + 3 ^ 40 * 7350709 * 2
def baseEnd_7350709 : Nat := 3774446868330386050932211

theorem tailTrace_7350709 : CollatzResearch.WordTrace tailWord_7350709 prefixEnd_7350709 3774446868330386050932211 := by
  unfold tailWord_7350709
  simp only [CollatzResearch.WordTrace]
  refine ⟨268102382726644168994719181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178734921817762779329812787 268102382726644168994719181)
  ·
    refine ⟨100538393522491563373019693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268102382726644168994719181 100538393522491563373019693)
    ·
      refine ⟨37701897570934336264882385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100538393522491563373019693 37701897570934336264882385)
      ·
        refine ⟨28276423178200752198661789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37701897570934336264882385 28276423178200752198661789)
        ·
          refine ⟨10603658691825282074498171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28276423178200752198661789 10603658691825282074498171)
          ·
            refine ⟨15905488037737923111747257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603658691825282074498171 15905488037737923111747257)
            ·
              refine ⟨11929116028303442333810443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15905488037737923111747257 11929116028303442333810443)
              ·
                refine ⟨17893674042455163500715665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929116028303442333810443 17893674042455163500715665)
                ·
                  refine ⟨13420255531841372625536749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17893674042455163500715665 13420255531841372625536749)
                  ·
                    refine ⟨5032595824440514734576281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13420255531841372625536749 5032595824440514734576281)
                    ·
                      refine ⟨3774446868330386050932211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032595824440514734576281 3774446868330386050932211)
                      ·
                        rfl

theorem cell23_7350709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_7350709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350709 prefixEnd_7350709 := by exact prefixLift 7350709
  have htrace : WordTrace (prefixWord ++ tailWord_7350709) baseStart_7350709 baseEnd_7350709 := by
    simpa [prefixWord, tailWord_7350709, baseEnd_7350709] using wordTrace_append hprefix tailTrace_7350709
  have hstable : (prefixWord ++ tailWord_7350709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350709).length < 2 ^ (prefixWord ++ tailWord_7350709).sum := by decide
  have hdescent : baseEnd_7350709 < baseStart_7350709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350742 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_7350742 : Nat := 118140960795 + 7350742 * 2 ^ 59
def prefixEnd_7350742 : Nat := 4983230072969 + 3 ^ 40 * 7350742 * 2
def baseEnd_7350742 : Nat := 3774463813191984421819559

theorem tailTrace_7350742 : CollatzResearch.WordTrace tailWord_7350742 prefixEnd_7350742 3774463813191984421819559 := by
  unfold tailWord_7350742
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756474145970288476916905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178735724223683077087113653 16756474145970288476916905)
  ·
    refine ⟨12567355609477716357687679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16756474145970288476916905 12567355609477716357687679)
    ·
      refine ⟨18851033414216574536531519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567355609477716357687679 18851033414216574536531519)
      ·
        refine ⟨28276550121324861804797279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851033414216574536531519 28276550121324861804797279)
        ·
          refine ⟨42414825181987292707195919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28276550121324861804797279 42414825181987292707195919)
          ·
            refine ⟨63622237772980939060793879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42414825181987292707195919 63622237772980939060793879)
            ·
              refine ⟨95433356659471408591190819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63622237772980939060793879 95433356659471408591190819)
              ·
                refine ⟨143150034989207112886786229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95433356659471408591190819 143150034989207112886786229)
                ·
                  refine ⟨13420315780238166833136209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143150034989207112886786229 13420315780238166833136209)
                  ·
                    refine ⟨10065236835178625124852157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13420315780238166833136209 10065236835178625124852157)
                    ·
                      refine ⟨3774463813191984421819559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10065236835178625124852157 3774463813191984421819559)
                      ·
                        rfl

theorem cell23_7350742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_7350742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350742 prefixEnd_7350742 := by exact prefixLift 7350742
  have htrace : WordTrace (prefixWord ++ tailWord_7350742) baseStart_7350742 baseEnd_7350742 := by
    simpa [prefixWord, tailWord_7350742, baseEnd_7350742] using wordTrace_append hprefix tailTrace_7350742
  have hstable : (prefixWord ++ tailWord_7350742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350742).length < 2 ^ (prefixWord ++ tailWord_7350742).sum := by decide
  have hdescent : baseEnd_7350742 < baseStart_7350742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350768 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_7350768 : Nat := 118140960795 + 7350768 * 2 ^ 59
def prefixEnd_7350768 : Nat := 4983230072969 + 3 ^ 40 * 7350768 * 2
def baseEnd_7350768 : Nat := 3774477163689001320094439

theorem tailTrace_7350768 : CollatzResearch.WordTrace tailWord_7350768 prefixEnd_7350768 3774477163689001320094439 := by
  unfold tailWord_7350768
  simp only [CollatzResearch.WordTrace]
  refine ⟨134052267316715211035558479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178736356422286948047411305 134052267316715211035558479)
  ·
    refine ⟨201078400975072816553337719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134052267316715211035558479 201078400975072816553337719)
    ·
      refine ⟨301617601462609224830006579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201078400975072816553337719 301617601462609224830006579)
      ·
        refine ⟨452426402193913837245009869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301617601462609224830006579 452426402193913837245009869)
        ·
          refine ⟨169659900822717688966878701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 452426402193913837245009869 169659900822717688966878701)
          ·
            refine ⟨63622462808519133362579513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169659900822717688966878701 63622462808519133362579513)
            ·
              refine ⟨47716847106389350021934635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63622462808519133362579513 47716847106389350021934635)
              ·
                refine ⟨71575270659584025032901953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47716847106389350021934635 71575270659584025032901953)
                ·
                  refine ⟨53681452994688018774676465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71575270659584025032901953 53681452994688018774676465)
                  ·
                    refine ⟨40261089746016014081007349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53681452994688018774676465 40261089746016014081007349)
                    ·
                      refine ⟨3774477163689001320094439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40261089746016014081007349 3774477163689001320094439)
                      ·
                        rfl

theorem cell23_7350768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_7350768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350768 prefixEnd_7350768 := by exact prefixLift 7350768
  have htrace : WordTrace (prefixWord ++ tailWord_7350768) baseStart_7350768 baseEnd_7350768 := by
    simpa [prefixWord, tailWord_7350768, baseEnd_7350768] using wordTrace_append hprefix tailTrace_7350768
  have hstable : (prefixWord ++ tailWord_7350768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350768).length < 2 ^ (prefixWord ++ tailWord_7350768).sum := by decide
  have hdescent : baseEnd_7350768 < baseStart_7350768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350773 : List Nat := [1, 3, 5, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7350773 : Nat := 118140960795 + 7350773 * 2 ^ 59
def prefixEnd_7350773 : Nat := 4983230072969 + 3 ^ 40 * 7350773 * 2
def baseEnd_7350773 : Nat := 3774479731092273800531917

theorem tailTrace_7350773 : CollatzResearch.WordTrace tailWord_7350773 prefixEnd_7350773 3774479731092273800531917 := by
  unfold tailWord_7350773
  simp only [CollatzResearch.WordTrace]
  refine ⟨268104716998412307925048973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178736477998941538616699315 268104716998412307925048973)
  ·
    refine ⟨100539268874404615471893365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268104716998412307925048973 100539268874404615471893365)
    ·
      refine ⟨9425556456975432700490003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100539268874404615471893365 9425556456975432700490003)
      ·
        refine ⟨14138334685463149050735005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425556456975432700490003 14138334685463149050735005)
        ·
          refine ⟨5301875507048680894025627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14138334685463149050735005 5301875507048680894025627)
          ·
            refine ⟨7952813260573021341038441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301875507048680894025627 7952813260573021341038441)
            ·
              refine ⟨5964609945429766005778831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952813260573021341038441 5964609945429766005778831)
              ·
                refine ⟨8946914918144649008668247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964609945429766005778831 8946914918144649008668247)
                ·
                  refine ⟨13420372377216973513002371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946914918144649008668247 13420372377216973513002371)
                  ·
                    refine ⟨20130558565825460269503557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13420372377216973513002371 20130558565825460269503557)
                    ·
                      refine ⟨3774479731092273800531917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20130558565825460269503557 3774479731092273800531917)
                      ·
                        rfl

theorem cell23_7350773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7350773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350773 prefixEnd_7350773 := by exact prefixLift 7350773
  have htrace : WordTrace (prefixWord ++ tailWord_7350773) baseStart_7350773 baseEnd_7350773 := by
    simpa [prefixWord, tailWord_7350773, baseEnd_7350773] using wordTrace_append hprefix tailTrace_7350773
  have hstable : (prefixWord ++ tailWord_7350773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350773).length < 2 ^ (prefixWord ++ tailWord_7350773).sum := by decide
  have hdescent : baseEnd_7350773 < baseStart_7350773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350778 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_7350778 : Nat := 118140960795 + 7350778 * 2 ^ 59
def prefixEnd_7350778 : Nat := 4983230072969 + 3 ^ 40 * 7350778 * 2
def baseEnd_7350778 : Nat := 3774482298495546280969393

theorem tailTrace_7350778 : CollatzResearch.WordTrace tailWord_7350778 prefixEnd_7350778 3774482298495546280969393 := by
  unfold tailWord_7350778
  simp only [CollatzResearch.WordTrace]
  refine ⟨67026224840848548444745247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178736599575596129185987325 67026224840848548444745247)
  ·
    refine ⟨100539337261272822667117871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67026224840848548444745247 100539337261272822667117871)
    ·
      refine ⟨150809005891909234000676807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100539337261272822667117871 150809005891909234000676807)
      ·
        refine ⟨226213508837863851001015211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150809005891909234000676807 226213508837863851001015211)
        ·
          refine ⟨339320263256795776501522817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226213508837863851001015211 339320263256795776501522817)
          ·
            refine ⟨254490197442596832376142113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339320263256795776501522817 254490197442596832376142113)
            ·
              refine ⟨190867648081947624282106585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254490197442596832376142113 190867648081947624282106585)
              ·
                refine ⟨143150736061460718211579939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190867648081947624282106585 143150736061460718211579939)
                ·
                  refine ⟨214726104092191077317369909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143150736061460718211579939 214726104092191077317369909)
                  ·
                    refine ⟨20130572258642913498503429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214726104092191077317369909 20130572258642913498503429)
                    ·
                      refine ⟨3774482298495546280969393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20130572258642913498503429 3774482298495546280969393)
                      ·
                        rfl

theorem cell23_7350778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_7350778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350778 prefixEnd_7350778 := by exact prefixLift 7350778
  have htrace : WordTrace (prefixWord ++ tailWord_7350778) baseStart_7350778 baseEnd_7350778 := by
    simpa [prefixWord, tailWord_7350778, baseEnd_7350778] using wordTrace_append hprefix tailTrace_7350778
  have hstable : (prefixWord ++ tailWord_7350778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350778).length < 2 ^ (prefixWord ++ tailWord_7350778).sum := by decide
  have hdescent : baseEnd_7350778 < baseStart_7350778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350790 : List Nat := [6, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7350790 : Nat := 118140960795 + 7350790 * 2 ^ 59
def prefixEnd_7350790 : Nat := 4983230072969 + 3 ^ 40 * 7350790 * 2
def baseEnd_7350790 : Nat := 3774488460263400234019339

theorem tailTrace_7350790 : CollatzResearch.WordTrace tailWord_7350790 prefixEnd_7350790 3774488460263400234019339 := by
  unfold tailWord_7350790
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378291782479709994638057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178736891359567146552278549 8378291782479709994638057)
  ·
    refine ⟨6283718836859782495978543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8378291782479709994638057 6283718836859782495978543)
    ·
      refine ⟨9425578255289673743967815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283718836859782495978543 9425578255289673743967815)
      ·
        refine ⟨14138367382934510615951723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425578255289673743967815 14138367382934510615951723)
        ·
          refine ⟨21207551074401765923927585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14138367382934510615951723 21207551074401765923927585)
          ·
            refine ⟨15905663305801324442945689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21207551074401765923927585 15905663305801324442945689)
            ·
              refine ⟨11929247479350993332209267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15905663305801324442945689 11929247479350993332209267)
              ·
                refine ⟨17893871219026489998313901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929247479350993332209267 17893871219026489998313901)
                ·
                  refine ⟨6710201707134933749367713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17893871219026489998313901 6710201707134933749367713)
                  ·
                    refine ⟨5032651280351200312025785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6710201707134933749367713 5032651280351200312025785)
                    ·
                      refine ⟨3774488460263400234019339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032651280351200312025785 3774488460263400234019339)
                      ·
                        rfl

theorem cell23_7350790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7350790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350790 prefixEnd_7350790 := by exact prefixLift 7350790
  have htrace : WordTrace (prefixWord ++ tailWord_7350790) baseStart_7350790 baseEnd_7350790 := by
    simpa [prefixWord, tailWord_7350790, baseEnd_7350790] using wordTrace_append hprefix tailTrace_7350790
  have hstable : (prefixWord ++ tailWord_7350790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350790).length < 2 ^ (prefixWord ++ tailWord_7350790).sum := by decide
  have hdescent : baseEnd_7350790 < baseStart_7350790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350816 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2]
def baseStart_7350816 : Nat := 118140960795 + 7350816 * 2 ^ 59
def prefixEnd_7350816 : Nat := 4983230072969 + 3 ^ 40 * 7350816 * 2
def baseEnd_7350816 : Nat := 3774501810760417132294219

theorem tailTrace_7350816 : CollatzResearch.WordTrace tailWord_7350816 prefixEnd_7350816 3774501810760417132294219 := by
  unfold tailWord_7350816
  simp only [CollatzResearch.WordTrace]
  refine ⟨134053142668628263134432151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178737523558171017512576201 134053142668628263134432151)
  ·
    refine ⟨201079714002942394701648227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134053142668628263134432151 201079714002942394701648227)
    ·
      refine ⟨301619571004413592052472341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201079714002942394701648227 301619571004413592052472341)
      ·
        refine ⟨14138417390831887127459641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 301619571004413592052472341 14138417390831887127459641)
        ·
          refine ⟨10603813043123915345594731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14138417390831887127459641 10603813043123915345594731)
          ·
            refine ⟨15905719564685873018392097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603813043123915345594731 15905719564685873018392097)
            ·
              refine ⟨11929289673514404763794073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15905719564685873018392097 11929289673514404763794073)
              ·
                refine ⟨8946967255135803572845555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11929289673514404763794073 8946967255135803572845555)
                ·
                  refine ⟨13420450882703705359268333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946967255135803572845555 13420450882703705359268333)
                  ·
                    refine ⟨5032669081013889509725625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13420450882703705359268333 5032669081013889509725625)
                    ·
                      refine ⟨3774501810760417132294219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032669081013889509725625 3774501810760417132294219)
                      ·
                        rfl

theorem cell23_7350816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_7350816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350816 prefixEnd_7350816 := by exact prefixLift 7350816
  have htrace : WordTrace (prefixWord ++ tailWord_7350816) baseStart_7350816 baseEnd_7350816 := by
    simpa [prefixWord, tailWord_7350816, baseEnd_7350816] using wordTrace_append hprefix tailTrace_7350816
  have hstable : (prefixWord ++ tailWord_7350816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350816).length < 2 ^ (prefixWord ++ tailWord_7350816).sum := by decide
  have hdescent : baseEnd_7350816 < baseStart_7350816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7350942 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_7350942 : Nat := 118140960795 + 7350942 * 2 ^ 59
def prefixEnd_7350942 : Nat := 4983230072969 + 3 ^ 40 * 7350942 * 2
def baseEnd_7350942 : Nat := 419396278813653737702071

theorem tailTrace_7350942 : CollatzResearch.WordTrace tailWord_7350942 prefixEnd_7350942 419396278813653737702071 := by
  unfold tailWord_7350942
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513860116850006223493885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178740587289866699858634053 33513860116850006223493885)
  ·
    refine ⟨12567697543818752333810207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33513860116850006223493885 12567697543818752333810207)
    ·
      refine ⟨18851546315728128500715311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567697543818752333810207 18851546315728128500715311)
      ·
        refine ⟨28277319473592192751072967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851546315728128500715311 28277319473592192751072967)
        ·
          refine ⟨42415979210388289126609451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28277319473592192751072967 42415979210388289126609451)
          ·
            refine ⟨63623968815582433689914177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42415979210388289126609451 63623968815582433689914177)
            ·
              refine ⟨47717976611686825267435633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63623968815582433689914177 47717976611686825267435633)
              ·
                refine ⟨35788482458765118950576725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47717976611686825267435633 35788482458765118950576725)
                ·
                  refine ⟨419396278813653737702071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35788482458765118950576725 419396278813653737702071)
                  ·
                    rfl

theorem cell23_7350942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_7350942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7350942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7350942 prefixEnd_7350942 := by exact prefixLift 7350942
  have htrace : WordTrace (prefixWord ++ tailWord_7350942) baseStart_7350942 baseEnd_7350942 := by
    simpa [prefixWord, tailWord_7350942, baseEnd_7350942] using wordTrace_append hprefix tailTrace_7350942
  have hstable : (prefixWord ++ tailWord_7350942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7350942).length < 2 ^ (prefixWord ++ tailWord_7350942).sum := by decide
  have hdescent : baseEnd_7350942 < baseStart_7350942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7350942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351002 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 6, 4]
def baseStart_7351002 : Nat := 118140960795 + 7351002 * 2 ^ 59
def prefixEnd_7351002 : Nat := 4983230072969 + 3 ^ 40 * 7351002 * 2
def baseEnd_7351002 : Nat := 1258199106054051134856121

theorem tailTrace_7351002 : CollatzResearch.WordTrace tailWord_7351002 prefixEnd_7351002 1258199106054051134856121 := by
  unfold tailWord_7351002
  simp only [CollatzResearch.WordTrace]
  refine ⟨67028267328645670008783815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178742046209721786690090173 67028267328645670008783815)
  ·
    refine ⟨100542400992968505013175723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67028267328645670008783815 100542400992968505013175723)
    ·
      refine ⟨150813601489452757519763585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100542400992968505013175723 150813601489452757519763585)
      ·
        refine ⟨113110201117089568139822689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150813601489452757519763585 113110201117089568139822689)
        ·
          refine ⟨84832650837817176104867017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113110201117089568139822689 84832650837817176104867017)
          ·
            refine ⟨63624488128362882078650263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84832650837817176104867017 63624488128362882078650263)
            ·
              refine ⟨95436732192544323117975395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63624488128362882078650263 95436732192544323117975395)
              ·
                refine ⟨143155098288816484676963093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95436732192544323117975395 143155098288816484676963093)
                ·
                  refine ⟨6710395232288272719232645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 143155098288816484676963093 6710395232288272719232645)
                  ·
                    refine ⟨1258199106054051134856121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710395232288272719232645 1258199106054051134856121)
                    ·
                      rfl

theorem cell23_7351002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 4].length) (baseStart_7351002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351002 prefixEnd_7351002 := by exact prefixLift 7351002
  have htrace : WordTrace (prefixWord ++ tailWord_7351002) baseStart_7351002 baseEnd_7351002 := by
    simpa [prefixWord, tailWord_7351002, baseEnd_7351002] using wordTrace_append hprefix tailTrace_7351002
  have hstable : (prefixWord ++ tailWord_7351002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351002).length < 2 ^ (prefixWord ++ tailWord_7351002).sum := by decide
  have hdescent : baseEnd_7351002 < baseStart_7351002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351009 : List Nat := [1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_7351009 : Nat := 118140960795 + 7351009 * 2 ^ 59
def prefixEnd_7351009 : Nat := 4983230072969 + 3 ^ 40 * 7351009 * 2
def baseEnd_7351009 : Nat := 3774600912526734877180831

theorem tailTrace_7351009 : CollatzResearch.WordTrace tailWord_7351009 prefixEnd_7351009 3774600912526734877180831 := by
  unfold tailWord_7351009
  simp only [CollatzResearch.WordTrace]
  refine ⟨268113324625557320230640081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178742216417038213487093387 268113324625557320230640081)
  ·
    refine ⟨201084993469167990172980061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268113324625557320230640081 201084993469167990172980061)
    ·
      refine ⟨75406872550937996314867523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201084993469167990172980061 75406872550937996314867523)
      ·
        refine ⟨113110308826406994472301285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75406872550937996314867523 113110308826406994472301285)
        ·
          refine ⟨21208182904951311463556491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113110308826406994472301285 21208182904951311463556491)
          ·
            refine ⟨31812274357426967195334737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21208182904951311463556491 31812274357426967195334737)
            ·
              refine ⟨23859205768070225396501053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31812274357426967195334737 23859205768070225396501053)
              ·
                refine ⟨8947202163026334523687895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23859205768070225396501053 8947202163026334523687895)
                ·
                  refine ⟨13420803244539501785531843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947202163026334523687895 13420803244539501785531843)
                  ·
                    refine ⟨20131204866809252678297765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13420803244539501785531843 20131204866809252678297765)
                    ·
                      refine ⟨3774600912526734877180831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20131204866809252678297765 3774600912526734877180831)
                      ·
                        rfl

theorem cell23_7351009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_7351009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351009 prefixEnd_7351009 := by exact prefixLift 7351009
  have htrace : WordTrace (prefixWord ++ tailWord_7351009) baseStart_7351009 baseEnd_7351009 := by
    simpa [prefixWord, tailWord_7351009, baseEnd_7351009] using wordTrace_append hprefix tailTrace_7351009
  have hstable : (prefixWord ++ tailWord_7351009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351009).length < 2 ^ (prefixWord ++ tailWord_7351009).sum := by decide
  have hdescent : baseEnd_7351009 < baseStart_7351009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351012 : List Nat := [2, 3, 1, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_7351012 : Nat := 118140960795 + 7351012 * 2 ^ 59
def prefixEnd_7351012 : Nat := 4983230072969 + 3 ^ 40 * 7351012 * 2
def baseEnd_7351012 : Nat := 3774602452968698365443317

theorem tailTrace_7351012 : CollatzResearch.WordTrace tailWord_7351012 prefixEnd_7351012 3774602452968698365443317 := by
  unfold tailWord_7351012
  simp only [CollatzResearch.WordTrace]
  refine ⟨134056717022273225871499645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178742289363030967828666193 134056717022273225871499645)
  ·
    refine ⟨50271268883352459701812367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134056717022273225871499645 50271268883352459701812367)
    ·
      refine ⟨75406903325028689552718551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50271268883352459701812367 75406903325028689552718551)
      ·
        refine ⟨113110354987543034329077827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75406903325028689552718551 113110354987543034329077827)
        ·
          refine ⟨169665532481314551493616741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113110354987543034329077827 169665532481314551493616741)
          ·
            refine ⟨31812287340246478405053139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169665532481314551493616741 31812287340246478405053139)
            ·
              refine ⟨47718431010369717607579709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31812287340246478405053139 47718431010369717607579709)
              ·
                refine ⟨17894411628888644102842391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47718431010369717607579709 17894411628888644102842391)
                ·
                  refine ⟨26841617443332966154263587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17894411628888644102842391 26841617443332966154263587)
                  ·
                    refine ⟨40262426164999449231395381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26841617443332966154263587 40262426164999449231395381)
                    ·
                      refine ⟨3774602452968698365443317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40262426164999449231395381 3774602452968698365443317)
                      ·
                        rfl

theorem cell23_7351012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_7351012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351012 prefixEnd_7351012 := by exact prefixLift 7351012
  have htrace : WordTrace (prefixWord ++ tailWord_7351012) baseStart_7351012 baseEnd_7351012 := by
    simpa [prefixWord, tailWord_7351012, baseEnd_7351012] using wordTrace_append hprefix tailTrace_7351012
  have hstable : (prefixWord ++ tailWord_7351012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351012).length < 2 ^ (prefixWord ++ tailWord_7351012).sum := by decide
  have hdescent : baseEnd_7351012 < baseStart_7351012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351022 : List Nat := [4, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_7351022 : Nat := 118140960795 + 7351022 * 2 ^ 59
def prefixEnd_7351022 : Nat := 4983230072969 + 3 ^ 40 * 7351022 * 2
def baseEnd_7351022 : Nat := 3774607587775243326318271

theorem tailTrace_7351022 : CollatzResearch.WordTrace tailWord_7351022 prefixEnd_7351022 3774607587775243326318271 := by
  unfold tailWord_7351022
  simp only [CollatzResearch.WordTrace]
  refine ⟨33514224846813777931357915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178742532516340148967242213 33514224846813777931357915)
  ·
    refine ⟨50271337270220666897036873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33514224846813777931357915 50271337270220666897036873)
    ·
      refine ⟨37703502952665500172777655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50271337270220666897036873 37703502952665500172777655)
      ·
        refine ⟨56555254428998250259166483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37703502952665500172777655 56555254428998250259166483)
        ·
          refine ⟨84832881643497375388749725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56555254428998250259166483 84832881643497375388749725)
          ·
            refine ⟨31812330616311515770781147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84832881643497375388749725 31812330616311515770781147)
            ·
              refine ⟨47718495924467273656171721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31812330616311515770781147 47718495924467273656171721)
              ·
                refine ⟨35788871943350455242128791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47718495924467273656171721 35788871943350455242128791)
                ·
                  refine ⟨53683307915025682863193187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35788871943350455242128791 53683307915025682863193187)
                  ·
                    refine ⟨80524961872538524294789781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53683307915025682863193187 80524961872538524294789781)
                    ·
                      refine ⟨3774607587775243326318271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80524961872538524294789781 3774607587775243326318271)
                      ·
                        rfl

theorem cell23_7351022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_7351022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351022 prefixEnd_7351022 := by exact prefixLift 7351022
  have htrace : WordTrace (prefixWord ++ tailWord_7351022) baseStart_7351022 baseEnd_7351022 := by
    simpa [prefixWord, tailWord_7351022, baseEnd_7351022] using wordTrace_append hprefix tailTrace_7351022
  have hstable : (prefixWord ++ tailWord_7351022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351022).length < 2 ^ (prefixWord ++ tailWord_7351022).sum := by decide
  have hdescent : baseEnd_7351022 < baseStart_7351022 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351036 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 2, 4]
def baseStart_7351036 : Nat := 118140960795 + 7351036 * 2 ^ 59
def prefixEnd_7351036 : Nat := 4983230072969 + 3 ^ 40 * 7351036 * 2
def baseEnd_7351036 : Nat := 1258204925501468757181069

theorem tailTrace_7351036 : CollatzResearch.WordTrace tailWord_7351036 prefixEnd_7351036 1258204925501468757181069 := by
  unfold tailWord_7351036
  simp only [CollatzResearch.WordTrace]
  refine ⟨134057154698229751920936481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178742872930973002561248641 134057154698229751920936481)
  ·
    refine ⟨100542866023672313940702361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134057154698229751920936481 100542866023672313940702361)
    ·
      refine ⟨75407149517754235455526771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100542866023672313940702361 75407149517754235455526771)
      ·
        refine ⟨113110724276631353183290157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75407149517754235455526771 113110724276631353183290157)
        ·
          refine ⟨42416521603736757443733809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113110724276631353183290157 42416521603736757443733809)
          ·
            refine ⟨31812391202802568082800357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42416521603736757443733809 31812391202802568082800357)
            ·
              refine ⟨5964823350525481515525067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31812391202802568082800357 5964823350525481515525067)
              ·
                refine ⟨8947235025788222273287601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964823350525481515525067 8947235025788222273287601)
                ·
                  refine ⟨6710426269341166704965701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8947235025788222273287601 6710426269341166704965701)
                  ·
                    refine ⟨1258204925501468757181069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710426269341166704965701 1258204925501468757181069)
                    ·
                      rfl

theorem cell23_7351036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_7351036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351036 prefixEnd_7351036 := by exact prefixLift 7351036
  have htrace : WordTrace (prefixWord ++ tailWord_7351036) baseStart_7351036 baseEnd_7351036 := by
    simpa [prefixWord, tailWord_7351036, baseEnd_7351036] using wordTrace_append hprefix tailTrace_7351036
  have hstable : (prefixWord ++ tailWord_7351036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351036).length < 2 ^ (prefixWord ++ tailWord_7351036).sum := by decide
  have hdescent : baseEnd_7351036 < baseStart_7351036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351063 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 1, 2, 3]
def baseStart_7351063 : Nat := 118140960795 + 7351063 * 2 ^ 59
def prefixEnd_7351063 : Nat := 4983230072969 + 3 ^ 40 * 7351063 * 2
def baseEnd_7351063 : Nat := 3774628640482077665905583

theorem tailTrace_7351063 : CollatzResearch.WordTrace tailWord_7351063 prefixEnd_7351063 3774628640482077665905583 := by
  unfold tailWord_7351063
  simp only [CollatzResearch.WordTrace]
  refine ⟨268115294167361687453105843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178743529444907791635403895 268115294167361687453105843)
  ·
    refine ⟨402172941251042531179658765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268115294167361687453105843 402172941251042531179658765)
    ·
      refine ⟨150814852969140949192372037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402172941251042531179658765 150814852969140949192372037)
      ·
        refine ⟨28277784931713927973569757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150814852969140949192372037 28277784931713927973569757)
        ·
          refine ⟨10604169349392722990088659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28277784931713927973569757 10604169349392722990088659)
          ·
            refine ⟨15906254024089084485132989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10604169349392722990088659 15906254024089084485132989)
            ·
              refine ⟨5964845259033406681924871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15906254024089084485132989 5964845259033406681924871)
              ·
                refine ⟨8947267888550110022887307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964845259033406681924871 8947267888550110022887307)
                ·
                  refine ⟨13420901832825165034330961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947267888550110022887307 13420901832825165034330961)
                  ·
                    refine ⟨10065676374618873775748221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13420901832825165034330961 10065676374618873775748221)
                    ·
                      refine ⟨3774628640482077665905583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10065676374618873775748221 3774628640482077665905583)
                      ·
                        rfl

theorem cell23_7351063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_7351063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351063 prefixEnd_7351063 := by exact prefixLift 7351063
  have htrace : WordTrace (prefixWord ++ tailWord_7351063) baseStart_7351063 baseEnd_7351063 := by
    simpa [prefixWord, tailWord_7351063, baseEnd_7351063] using wordTrace_append hprefix tailTrace_7351063
  have hstable : (prefixWord ++ tailWord_7351063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351063).length < 2 ^ (prefixWord ++ tailWord_7351063).sum := by decide
  have hdescent : baseEnd_7351063 < baseStart_7351063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351112 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_7351112 : Nat := 118140960795 + 7351112 * 2 ^ 59
def prefixEnd_7351112 : Nat := 4983230072969 + 3 ^ 40 * 7351112 * 2
def baseEnd_7351112 : Nat := 3774653801034147974192857

theorem tailTrace_7351112 : CollatzResearch.WordTrace tailWord_7351112 prefixEnd_7351112 3774653801034147974192857 := by
  unfold tailWord_7351112
  simp only [CollatzResearch.WordTrace]
  refine ⟨134058540672092084410819795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178744720896122779214426393 134058540672092084410819795)
  ·
    refine ⟨201087811008138126616229693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134058540672092084410819795 201087811008138126616229693)
    ·
      refine ⟨75407929128051797481086135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201087811008138126616229693 75407929128051797481086135)
      ·
        refine ⟨113111893692077696221629203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75407929128051797481086135 113111893692077696221629203)
        ·
          refine ⟨169667840538116544332443805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113111893692077696221629203 169667840538116544332443805)
          ·
            refine ⟨63625440201793704124666427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169667840538116544332443805 63625440201793704124666427)
            ·
              refine ⟨95438160302690556186999641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63625440201793704124666427 95438160302690556186999641)
              ·
                refine ⟨71578620227017917140249731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95438160302690556186999641 71578620227017917140249731)
                ·
                  refine ⟨107367930340526875710374597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71578620227017917140249731 107367930340526875710374597)
                  ·
                    refine ⟨20131486938848789195695237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107367930340526875710374597 20131486938848789195695237)
                    ·
                      refine ⟨3774653801034147974192857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20131486938848789195695237 3774653801034147974192857)
                      ·
                        rfl

theorem cell23_7351112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_7351112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351112 prefixEnd_7351112 := by exact prefixLift 7351112
  have htrace : WordTrace (prefixWord ++ tailWord_7351112) baseStart_7351112 baseEnd_7351112 := by
    simpa [prefixWord, tailWord_7351112, baseEnd_7351112] using wordTrace_append hprefix tailTrace_7351112
  have hstable : (prefixWord ++ tailWord_7351112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351112).length < 2 ^ (prefixWord ++ tailWord_7351112).sum := by decide
  have hdescent : baseEnd_7351112 < baseStart_7351112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351116 : List Nat := [2, 2, 1, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_7351116 : Nat := 118140960795 + 7351116 * 2 ^ 59
def prefixEnd_7351116 : Nat := 4983230072969 + 3 ^ 40 * 7351116 * 2
def baseEnd_7351116 : Nat := 3774655854956765958542839

theorem tailTrace_7351116 : CollatzResearch.WordTrace tailWord_7351116 prefixEnd_7351116 3774655854956765958542839 := by
  unfold tailWord_7351116
  simp only [CollatzResearch.WordTrace]
  refine ⟨134058613618084838752392601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178744818157446451669856801 134058613618084838752392601)
  ·
    refine ⟨100543960213563629064294451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134058613618084838752392601 100543960213563629064294451)
    ·
      refine ⟨150815940320345443596441677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100543960213563629064294451 150815940320345443596441677)
      ·
        refine ⟨56555977620129541348665629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150815940320345443596441677 56555977620129541348665629)
        ·
          refine ⟨21208491607548578005749611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56555977620129541348665629 21208491607548578005749611)
          ·
            refine ⟨31812737411322867008624417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21208491607548578005749611 31812737411322867008624417)
            ·
              refine ⟨23859553058492150256468313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31812737411322867008624417 23859553058492150256468313)
              ·
                refine ⟨17894664793869112692351235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23859553058492150256468313 17894664793869112692351235)
                ·
                  refine ⟨26841997190803669038526853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17894664793869112692351235 26841997190803669038526853)
                  ·
                    refine ⟨5032874473275687944723785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26841997190803669038526853 5032874473275687944723785)
                    ·
                      refine ⟨3774655854956765958542839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032874473275687944723785 3774655854956765958542839)
                      ·
                        rfl

theorem cell23_7351116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_7351116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351116 prefixEnd_7351116 := by exact prefixLift 7351116
  have htrace : WordTrace (prefixWord ++ tailWord_7351116) baseStart_7351116 baseEnd_7351116 := by
    simpa [prefixWord, tailWord_7351116, baseEnd_7351116] using wordTrace_append hprefix tailTrace_7351116
  have hstable : (prefixWord ++ tailWord_7351116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351116).length < 2 ^ (prefixWord ++ tailWord_7351116).sum := by decide
  have hdescent : baseEnd_7351116 < baseStart_7351116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351122 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 9]
def baseStart_7351122 : Nat := 118140960795 + 7351122 * 2 ^ 59
def prefixEnd_7351122 : Nat := 4983230072969 + 3 ^ 40 * 7351122 * 2
def baseEnd_7351122 : Nat := 419406548426743659451979

theorem tailTrace_7351122 : CollatzResearch.WordTrace tailWord_7351122 prefixEnd_7351122 419406548426743659451979 := by
  unfold tailWord_7351122
  simp only [CollatzResearch.WordTrace]
  refine ⟨67029361518536985132375905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178744964049431960353002413 67029361518536985132375905)
  ·
    refine ⟨50272021138902738849281929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67029361518536985132375905 50272021138902738849281929)
    ·
      refine ⟨37704015854177054136961447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50272021138902738849281929 37704015854177054136961447)
      ·
        refine ⟨56556023781265581205442171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37704015854177054136961447 56556023781265581205442171)
        ·
          refine ⟨84834035671898371808163257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56556023781265581205442171 84834035671898371808163257)
          ·
            refine ⟨63625526753923778856122443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84834035671898371808163257 63625526753923778856122443)
            ·
              refine ⟨95438290130885668284183665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63625526753923778856122443 95438290130885668284183665)
              ·
                refine ⟨71578717598164251213137749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95438290130885668284183665 71578717598164251213137749)
                ·
                  refine ⟨419406548426743659451979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71578717598164251213137749 419406548426743659451979)
                  ·
                    rfl

theorem cell23_7351122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 9].length) (baseStart_7351122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351122 prefixEnd_7351122 := by exact prefixLift 7351122
  have htrace : WordTrace (prefixWord ++ tailWord_7351122) baseStart_7351122 baseEnd_7351122 := by
    simpa [prefixWord, tailWord_7351122, baseEnd_7351122] using wordTrace_append hprefix tailTrace_7351122
  have hstable : (prefixWord ++ tailWord_7351122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351122).length < 2 ^ (prefixWord ++ tailWord_7351122).sum := by decide
  have hdescent : baseEnd_7351122 < baseStart_7351122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351139 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 7]
def baseStart_7351139 : Nat := 118140960795 + 7351139 * 2 ^ 59
def prefixEnd_7351139 : Nat := 4983230072969 + 3 ^ 40 * 7351139 * 2
def baseEnd_7351139 : Nat := 419407518334646596506137

theorem tailTrace_7351139 : CollatzResearch.WordTrace tailWord_7351139 prefixEnd_7351139 419407518334646596506137 := by
  unfold tailWord_7351139
  simp only [CollatzResearch.WordTrace]
  refine ⟨268118066115086352432872471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178745377410057568288581647 268118066115086352432872471)
  ·
    refine ⟨402177099172629528649308707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268118066115086352432872471 402177099172629528649308707)
    ·
      refine ⟨603265648758944292973963061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 402177099172629528649308707 603265648758944292973963061)
      ·
        refine ⟨56556154571151027466309037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 603265648758944292973963061 56556154571151027466309037)
        ·
          refine ⟨21208557964181635299865889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56556154571151027466309037 21208557964181635299865889)
          ·
            refine ⟨15906418473136226474899417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21208557964181635299865889 15906418473136226474899417)
            ·
              refine ⟨11929813854852169856174563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15906418473136226474899417 11929813854852169856174563)
              ·
                refine ⟨17894720782278254784261845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929813854852169856174563 17894720782278254784261845)
                ·
                  refine ⟨419407518334646596506137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17894720782278254784261845 419407518334646596506137)
                  ·
                    rfl

theorem cell23_7351139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 7].length) (baseStart_7351139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351139 prefixEnd_7351139 := by exact prefixLift 7351139
  have htrace : WordTrace (prefixWord ++ tailWord_7351139) baseStart_7351139 baseEnd_7351139 := by
    simpa [prefixWord, tailWord_7351139, baseEnd_7351139] using wordTrace_append hprefix tailTrace_7351139
  have hstable : (prefixWord ++ tailWord_7351139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351139).length < 2 ^ (prefixWord ++ tailWord_7351139).sum := by decide
  have hdescent : baseEnd_7351139 < baseStart_7351139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351150 : List Nat := [4, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_7351150 : Nat := 118140960795 + 7351150 * 2 ^ 59
def prefixEnd_7351150 : Nat := 4983230072969 + 3 ^ 40 * 7351150 * 2
def baseEnd_7351150 : Nat := 3774673313299018825517683

theorem tailTrace_7351150 : CollatzResearch.WordTrace tailWord_7351150 prefixEnd_7351150 3774673313299018825517683 := by
  unfold tailWord_7351150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33514808414755812663940363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178745644878697667541015269 33514808414755812663940363)
  ·
    refine ⟨50272212622133718995910545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33514808414755812663940363 50272212622133718995910545)
    ·
      refine ⟨37704159466600289246932909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50272212622133718995910545 37704159466600289246932909)
      ·
        refine ⟨14139059799975108467599841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37704159466600289246932909 14139059799975108467599841)
        ·
          refine ⟨10604294849981331350699881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14139059799975108467599841 10604294849981331350699881)
          ·
            refine ⟨7953221137485998513024911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10604294849981331350699881 7953221137485998513024911)
            ·
              refine ⟨11929831706228997769537367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953221137485998513024911 11929831706228997769537367)
              ·
                refine ⟨17894747559343496654306051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929831706228997769537367 17894747559343496654306051)
                ·
                  refine ⟨26842121339015244981459077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17894747559343496654306051 26842121339015244981459077)
                  ·
                    refine ⟨5032897751065358434023577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26842121339015244981459077 5032897751065358434023577)
                    ·
                      refine ⟨3774673313299018825517683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032897751065358434023577 3774673313299018825517683)
                      ·
                        rfl

theorem cell23_7351150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_7351150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351150 prefixEnd_7351150 := by exact prefixLift 7351150
  have htrace : WordTrace (prefixWord ++ tailWord_7351150) baseStart_7351150 baseEnd_7351150 := by
    simpa [prefixWord, tailWord_7351150, baseEnd_7351150] using wordTrace_append hprefix tailTrace_7351150
  have hstable : (prefixWord ++ tailWord_7351150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351150).length < 2 ^ (prefixWord ++ tailWord_7351150).sum := by decide
  have hdescent : baseEnd_7351150 < baseStart_7351150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351152 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_7351152 : Nat := 118140960795 + 7351152 * 2 ^ 59
def prefixEnd_7351152 : Nat := 4983230072969 + 3 ^ 40 * 7351152 * 2
def baseEnd_7351152 : Nat := 1258224780086775939230891

theorem tailTrace_7351152 : CollatzResearch.WordTrace tailWord_7351152 prefixEnd_7351152 1258224780086775939230891 := by
  unfold tailWord_7351152
  simp only [CollatzResearch.WordTrace]
  refine ⟨134059270132019627826547855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178745693509359503768730473 134059270132019627826547855)
  ·
    refine ⟨201088905198029441739821783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134059270132019627826547855 201088905198029441739821783)
    ·
      refine ⟨301633357797044162609732675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201088905198029441739821783 301633357797044162609732675)
      ·
        refine ⟨452450036695566243914599013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301633357797044162609732675 452450036695566243914599013)
        ·
          refine ⟨84834381880418670733987315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 452450036695566243914599013 84834381880418670733987315)
          ·
            refine ⟨127251572820628006100980973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84834381880418670733987315 127251572820628006100980973)
            ·
              refine ⟨47719339807735502287867865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127251572820628006100980973 47719339807735502287867865)
              ·
                refine ⟨35789504855801626715900899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47719339807735502287867865 35789504855801626715900899)
                ·
                  refine ⟨53684257283702440073851349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35789504855801626715900899 53684257283702440073851349)
                  ·
                    refine ⟨1258224780086775939230891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53684257283702440073851349 1258224780086775939230891)
                    ·
                      rfl

theorem cell23_7351152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_7351152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351152 prefixEnd_7351152 := by exact prefixLift 7351152
  have htrace : WordTrace (prefixWord ++ tailWord_7351152) baseStart_7351152 baseEnd_7351152 := by
    simpa [prefixWord, tailWord_7351152, baseEnd_7351152] using wordTrace_append hprefix tailTrace_7351152
  have hstable : (prefixWord ++ tailWord_7351152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351152).length < 2 ^ (prefixWord ++ tailWord_7351152).sum := by decide
  have hdescent : baseEnd_7351152 < baseStart_7351152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351159 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 2, 5, 2]
def baseStart_7351159 : Nat := 118140960795 + 7351159 * 2 ^ 59
def prefixEnd_7351159 : Nat := 4983230072969 + 3 ^ 40 * 7351159 * 2
def baseEnd_7351159 : Nat := 3774677934624909290305141

theorem tailTrace_7351159 : CollatzResearch.WordTrace tailWord_7351159 prefixEnd_7351159 3774677934624909290305141 := by
  unfold tailWord_7351159
  simp only [CollatzResearch.WordTrace]
  refine ⟨268118795575013895848600531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178745863716675930565733687 268118795575013895848600531)
  ·
    refine ⟨402178193362520843772900797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268118795575013895848600531 402178193362520843772900797)
    ·
      refine ⟨150816822510945316414837799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 402178193362520843772900797 150816822510945316414837799)
      ·
        refine ⟨226225233766417974622256699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150816822510945316414837799 226225233766417974622256699)
        ·
          refine ⟨339337850649626961933385049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226225233766417974622256699 339337850649626961933385049)
          ·
            refine ⟨254503387987220221450038787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339337850649626961933385049 254503387987220221450038787)
            ·
              refine ⟨381755081980830332175058181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254503387987220221450038787 381755081980830332175058181)
              ·
                refine ⟨71579077871405687282823409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381755081980830332175058181 71579077871405687282823409)
                ·
                  refine ⟨53684308403554265462117557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71579077871405687282823409 53684308403554265462117557)
                  ·
                    refine ⟨5032903912833212387073521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53684308403554265462117557 5032903912833212387073521)
                    ·
                      refine ⟨3774677934624909290305141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5032903912833212387073521 3774677934624909290305141)
                      ·
                        rfl

theorem cell23_7351159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 5, 2].length) (baseStart_7351159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351159 prefixEnd_7351159 := by exact prefixLift 7351159
  have htrace : WordTrace (prefixWord ++ tailWord_7351159) baseStart_7351159 baseEnd_7351159 := by
    simpa [prefixWord, tailWord_7351159, baseEnd_7351159] using wordTrace_append hprefix tailTrace_7351159
  have hstable : (prefixWord ++ tailWord_7351159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351159).length < 2 ^ (prefixWord ++ tailWord_7351159).sum := by decide
  have hdescent : baseEnd_7351159 < baseStart_7351159 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351162 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_7351162 : Nat := 118140960795 + 7351162 * 2 ^ 59
def prefixEnd_7351162 : Nat := 4983230072969 + 3 ^ 40 * 7351162 * 2
def baseEnd_7351162 : Nat := 3774679475066872778567627

theorem tailTrace_7351162 : CollatzResearch.WordTrace tailWord_7351162 prefixEnd_7351162 3774679475066872778567627 := by
  unfold tailWord_7351162
  simp only [CollatzResearch.WordTrace]
  refine ⟨67029726248500756840239935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178745936662668684907306493 67029726248500756840239935)
  ·
    refine ⟨100544589372751135260359903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67029726248500756840239935 100544589372751135260359903)
    ·
      refine ⟨150816884059126702890539855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100544589372751135260359903 150816884059126702890539855)
      ·
        refine ⟨226225326088690054335809783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150816884059126702890539855 226225326088690054335809783)
        ·
          refine ⟨339337989133035081503714675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226225326088690054335809783 339337989133035081503714675)
          ·
            refine ⟨509006983699552622255572013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 339337989133035081503714675 509006983699552622255572013)
            ·
              refine ⟨190877618887332233345839505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 509006983699552622255572013 190877618887332233345839505)
              ·
                refine ⟨143158214165499175009379629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190877618887332233345839505 143158214165499175009379629)
                ·
                  refine ⟨53684330312062190628517361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 143158214165499175009379629 53684330312062190628517361)
                  ·
                    refine ⟨40263247734046642971388021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53684330312062190628517361 40263247734046642971388021)
                    ·
                      refine ⟨3774679475066872778567627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40263247734046642971388021 3774679475066872778567627)
                      ·
                        rfl

theorem cell23_7351162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_7351162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351162 prefixEnd_7351162 := by exact prefixLift 7351162
  have htrace : WordTrace (prefixWord ++ tailWord_7351162) baseStart_7351162 baseEnd_7351162 := by
    simpa [prefixWord, tailWord_7351162, baseEnd_7351162] using wordTrace_append hprefix tailTrace_7351162
  have hstable : (prefixWord ++ tailWord_7351162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351162).length < 2 ^ (prefixWord ++ tailWord_7351162).sum := by decide
  have hdescent : baseEnd_7351162 < baseStart_7351162 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351189 : List Nat := [1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_7351189 : Nat := 118140960795 + 7351189 * 2 ^ 59
def prefixEnd_7351189 : Nat := 4983230072969 + 3 ^ 40 * 7351189 * 2
def baseEnd_7351189 : Nat := 3774693339044544172930003

theorem tailTrace_7351189 : CollatzResearch.WordTrace tailWord_7351189 prefixEnd_7351189 3774693339044544172930003 := by
  unfold tailWord_7351189
  simp only [CollatzResearch.WordTrace]
  refine ⟨268119889764905210972192621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178746593176603473981461747 268119889764905210972192621)
  ·
    refine ⟨100544958661839454114572233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268119889764905210972192621 100544958661839454114572233)
    ·
      refine ⟨75408718996379590585929175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100544958661839454114572233 75408718996379590585929175)
      ·
        refine ⟨113113078494569385878893763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75408718996379590585929175 113113078494569385878893763)
        ·
          refine ⟨169669617741854078818340645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113113078494569385878893763 169669617741854078818340645)
          ·
            refine ⟨31813053326597639778438871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169669617741854078818340645 31813053326597639778438871)
            ·
              refine ⟨47719579989896459667658307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31813053326597639778438871 47719579989896459667658307)
              ·
                refine ⟨71579369984844689501487461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47719579989896459667658307 71579369984844689501487461)
                ·
                  refine ⟨13421131872158379281528899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71579369984844689501487461 13421131872158379281528899)
                  ·
                    refine ⟨20131697808237568922293349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13421131872158379281528899 20131697808237568922293349)
                    ·
                      refine ⟨3774693339044544172930003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20131697808237568922293349 3774693339044544172930003)
                      ·
                        rfl

theorem cell23_7351189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_7351189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351189 prefixEnd_7351189 := by exact prefixLift 7351189
  have htrace : WordTrace (prefixWord ++ tailWord_7351189) baseStart_7351189 baseEnd_7351189 := by
    simpa [prefixWord, tailWord_7351189, baseEnd_7351189] using wordTrace_append hprefix tailTrace_7351189
  have hstable : (prefixWord ++ tailWord_7351189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351189).length < 2 ^ (prefixWord ++ tailWord_7351189).sum := by decide
  have hdescent : baseEnd_7351189 < baseStart_7351189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351190 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 7]
def baseStart_7351190 : Nat := 118140960795 + 7351190 * 2 ^ 59
def prefixEnd_7351190 : Nat := 4983230072969 + 3 ^ 40 * 7351190 * 2
def baseEnd_7351190 : Nat := 419410428058355407668611

theorem tailTrace_7351190 : CollatzResearch.WordTrace tailWord_7351190 prefixEnd_7351190 419410428058355407668611 := by
  unfold tailWord_7351190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757495389868849258936189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178746617491934392095319349 16757495389868849258936189)
  ·
    refine ⟨6284060771200818472101071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16757495389868849258936189 6284060771200818472101071)
    ·
      refine ⟨9426091156801227708151607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6284060771200818472101071 9426091156801227708151607)
      ·
        refine ⟨14139136735201841562227411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9426091156801227708151607 14139136735201841562227411)
        ·
          refine ⟨21208705102802762343341117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14139136735201841562227411 21208705102802762343341117)
          ·
            refine ⟨7953264413551035878752919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21208705102802762343341117 7953264413551035878752919)
            ·
              refine ⟨11929896620326553818129379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953264413551035878752919 11929896620326553818129379)
              ·
                refine ⟨17894844930489830727194069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929896620326553818129379 17894844930489830727194069)
                ·
                  refine ⟨419410428058355407668611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17894844930489830727194069 419410428058355407668611)
                  ·
                    rfl

theorem cell23_7351190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_7351190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351190 prefixEnd_7351190 := by exact prefixLift 7351190
  have htrace : WordTrace (prefixWord ++ tailWord_7351190) baseStart_7351190 baseEnd_7351190 := by
    simpa [prefixWord, tailWord_7351190, baseEnd_7351190] using wordTrace_append hprefix tailTrace_7351190
  have hstable : (prefixWord ++ tailWord_7351190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351190).length < 2 ^ (prefixWord ++ tailWord_7351190).sum := by decide
  have hdescent : baseEnd_7351190 < baseStart_7351190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351196 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_7351196 : Nat := 118140960795 + 7351196 * 2 ^ 59
def prefixEnd_7351196 : Nat := 4983230072969 + 3 ^ 40 * 7351196 * 2
def baseEnd_7351196 : Nat := 3774696933409125645542471

theorem tailTrace_7351196 : CollatzResearch.WordTrace tailWord_7351196 prefixEnd_7351196 3774696933409125645542471 := by
  unfold tailWord_7351196
  simp only [CollatzResearch.WordTrace]
  refine ⟨134060072537939925583848721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178746763383919900778464961 134060072537939925583848721)
  ·
    refine ⟨100545054403454944187886541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134060072537939925583848721 100545054403454944187886541)
    ·
      refine ⟨37704395401295604070457453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100545054403454944187886541 37704395401295604070457453)
      ·
        refine ⟨14139148275485851526421545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37704395401295604070457453 14139148275485851526421545)
        ·
          refine ⟨10604361206614388644816159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14139148275485851526421545 10604361206614388644816159)
          ·
            refine ⟨15906541809921582967224239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10604361206614388644816159 15906541809921582967224239)
            ·
              refine ⟨23859812714882374450836359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15906541809921582967224239 23859812714882374450836359)
              ·
                refine ⟨35789719072323561676254539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23859812714882374450836359 35789719072323561676254539)
                ·
                  refine ⟨53684578608485342514381809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35789719072323561676254539 53684578608485342514381809)
                  ·
                    refine ⟨40263433956364006885786357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53684578608485342514381809 40263433956364006885786357)
                    ·
                      refine ⟨3774696933409125645542471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40263433956364006885786357 3774696933409125645542471)
                      ·
                        rfl

theorem cell23_7351196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_7351196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351196 prefixEnd_7351196 := by exact prefixLift 7351196
  have htrace : WordTrace (prefixWord ++ tailWord_7351196) baseStart_7351196 baseEnd_7351196 := by
    simpa [prefixWord, tailWord_7351196, baseEnd_7351196] using wordTrace_append hprefix tailTrace_7351196
  have hstable : (prefixWord ++ tailWord_7351196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351196).length < 2 ^ (prefixWord ++ tailWord_7351196).sum := by decide
  have hdescent : baseEnd_7351196 < baseStart_7351196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351209 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 3]
def baseStart_7351209 : Nat := 118140960795 + 7351209 * 2 ^ 59
def prefixEnd_7351209 : Nat := 4983230072969 + 3 ^ 40 * 7351209 * 2
def baseEnd_7351209 : Nat := 3774703608657634094679911

theorem tailTrace_7351209 : CollatzResearch.WordTrace tailWord_7351209 prefixEnd_7351209 3774703608657634094679911 := by
  unfold tailWord_7351209
  simp only [CollatzResearch.WordTrace]
  refine ⟨268120619224832754387920681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178747079483221836258613787 268120619224832754387920681)
  ·
    refine ⟨201090464418624565790940511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268120619224832754387920681 201090464418624565790940511)
    ·
      refine ⟨301635696627936848686410767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201090464418624565790940511 301635696627936848686410767)
      ·
        refine ⟨452453544941905273029616151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301635696627936848686410767 452453544941905273029616151)
        ·
          refine ⟨678680317412857909544424227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 452453544941905273029616151 678680317412857909544424227)
          ·
            refine ⟨1018020476119286864316636341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678680317412857909544424227 1018020476119286864316636341)
            ·
              refine ⟨95439419636183143529684657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1018020476119286864316636341 95439419636183143529684657)
              ·
                refine ⟨71579564727137357647263493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95439419636183143529684657 71579564727137357647263493)
                ·
                  refine ⟨13421168386338254558861905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71579564727137357647263493 13421168386338254558861905)
                  ·
                    refine ⟨10065876289753690919146429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421168386338254558861905 10065876289753690919146429)
                    ·
                      refine ⟨3774703608657634094679911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10065876289753690919146429 3774703608657634094679911)
                      ·
                        rfl

theorem cell23_7351209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 2, 3].length) (baseStart_7351209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351209 prefixEnd_7351209 := by exact prefixLift 7351209
  have htrace : WordTrace (prefixWord ++ tailWord_7351209) baseStart_7351209 baseEnd_7351209 := by
    simpa [prefixWord, tailWord_7351209, baseEnd_7351209] using wordTrace_append hprefix tailTrace_7351209
  have hstable : (prefixWord ++ tailWord_7351209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351209).length < 2 ^ (prefixWord ++ tailWord_7351209).sum := by decide
  have hdescent : baseEnd_7351209 < baseStart_7351209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351226 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3]
def baseStart_7351226 : Nat := 118140960795 + 7351226 * 2 ^ 59
def prefixEnd_7351226 : Nat := 4983230072969 + 3 ^ 40 * 7351226 * 2
def baseEnd_7351226 : Nat := 3774712337828760528167333

theorem tailTrace_7351226 : CollatzResearch.WordTrace tailWord_7351226 prefixEnd_7351226 3774712337828760528167333 := by
  unfold tailWord_7351226
  simp only [CollatzResearch.WordTrace]
  refine ⟨67030309816442791572822383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178747492843847444194193021 67030309816442791572822383)
  ·
    refine ⟨100545464724664187359233575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67030309816442791572822383 100545464724664187359233575)
    ·
      refine ⟨150818197086996281038850363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100545464724664187359233575 150818197086996281038850363)
      ·
        refine ⟨226227295630494421558275545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150818197086996281038850363 226227295630494421558275545)
        ·
          refine ⟨169670471722870816168706659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226227295630494421558275545 169670471722870816168706659)
          ·
            refine ⟨254505707584306224253059989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169670471722870816168706659 254505707584306224253059989)
            ·
              refine ⟨11929955043014354261862187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 254505707584306224253059989 11929955043014354261862187)
              ·
                refine ⟨17894932564521531392793281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929955043014354261862187 17894932564521531392793281)
                ·
                  refine ⟨13421199423391148544594961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17894932564521531392793281 13421199423391148544594961)
                  ·
                    refine ⟨10065899567543361408446221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421199423391148544594961 10065899567543361408446221)
                    ·
                      refine ⟨3774712337828760528167333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10065899567543361408446221 3774712337828760528167333)
                      ·
                        rfl

theorem cell23_7351226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3].length) (baseStart_7351226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351226 prefixEnd_7351226 := by exact prefixLift 7351226
  have htrace : WordTrace (prefixWord ++ tailWord_7351226) baseStart_7351226 baseEnd_7351226 := by
    simpa [prefixWord, tailWord_7351226, baseEnd_7351226] using wordTrace_append hprefix tailTrace_7351226
  have hstable : (prefixWord ++ tailWord_7351226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351226).length < 2 ^ (prefixWord ++ tailWord_7351226).sum := by decide
  have hdescent : baseEnd_7351226 < baseStart_7351226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351246 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 6]
def baseStart_7351246 : Nat := 118140960795 + 7351246 * 2 ^ 59
def prefixEnd_7351246 : Nat := 4983230072969 + 3 ^ 40 * 7351246 * 2
def baseEnd_7351246 : Nat := 419413623049094494435249

theorem tailTrace_7351246 : CollatzResearch.WordTrace tailWord_7351246 prefixEnd_7351246 419413623049094494435249 := by
  unfold tailWord_7351246
  simp only [CollatzResearch.WordTrace]
  refine ⟨33515246090712338713377199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178747979150465806471345061 33515246090712338713377199)
  ·
    refine ⟨50272869136068508070065799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33515246090712338713377199 50272869136068508070065799)
    ·
      refine ⟨75409303704102762105098699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50272869136068508070065799 75409303704102762105098699)
      ·
        refine ⟨113113955556154143157648049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75409303704102762105098699 113113955556154143157648049)
        ·
          refine ⟨84835466667115607368236037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113113955556154143157648049 84835466667115607368236037)
          ·
            refine ⟨15906650000084176381544257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84835466667115607368236037 15906650000084176381544257)
            ·
              refine ⟨11929987500063132286158193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15906650000084176381544257 11929987500063132286158193)
              ·
                refine ⟨8947490625047349214618645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11929987500063132286158193 8947490625047349214618645)
                ·
                  refine ⟨419413623049094494435249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8947490625047349214618645 419413623049094494435249)
                  ·
                    rfl

theorem cell23_7351246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_7351246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351246 prefixEnd_7351246 := by exact prefixLift 7351246
  have htrace : WordTrace (prefixWord ++ tailWord_7351246) baseStart_7351246 baseEnd_7351246 := by
    simpa [prefixWord, tailWord_7351246, baseEnd_7351246] using wordTrace_append hprefix tailTrace_7351246
  have hstable : (prefixWord ++ tailWord_7351246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351246).length < 2 ^ (prefixWord ++ tailWord_7351246).sum := by decide
  have hdescent : baseEnd_7351246 < baseStart_7351246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351250 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 1, 4]
def baseStart_7351250 : Nat := 118140960795 + 7351250 * 2 ^ 59
def prefixEnd_7351250 : Nat := 4983230072969 + 3 ^ 40 * 7351250 * 2
def baseEnd_7351250 : Nat := 1258241553788156144755741

theorem tailTrace_7351250 : CollatzResearch.WordTrace tailWord_7351250 prefixEnd_7351250 1258241553788156144755741 := by
  unfold tailWord_7351250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67030528654421054597540801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178748076411789478926775469 67030528654421054597540801)
  ·
    refine ⟨50272896490815790948155601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67030528654421054597540801 50272896490815790948155601)
    ·
      refine ⟨37704672368111843211116701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50272896490815790948155601 37704672368111843211116701)
      ·
        refine ⟨14139252138041941204168763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37704672368111843211116701 14139252138041941204168763)
        ·
          refine ⟨21208878207062911806253145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14139252138041941204168763 21208878207062911806253145)
          ·
            refine ⟨15906658655297183854689859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21208878207062911806253145 15906658655297183854689859)
            ·
              refine ⟨23859987982945775782034789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15906658655297183854689859 23859987982945775782034789)
              ·
                refine ⟨4473747746802332959131523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23859987982945775782034789 4473747746802332959131523)
                ·
                  refine ⟨6710621620203499438697285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4473747746802332959131523 6710621620203499438697285)
                  ·
                    refine ⟨1258241553788156144755741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6710621620203499438697285 1258241553788156144755741)
                    ·
                      rfl

theorem cell23_7351250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_7351250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351250 prefixEnd_7351250 := by exact prefixLift 7351250
  have htrace : WordTrace (prefixWord ++ tailWord_7351250) baseStart_7351250 baseEnd_7351250 := by
    simpa [prefixWord, tailWord_7351250, baseEnd_7351250] using wordTrace_append hprefix tailTrace_7351250
  have hstable : (prefixWord ++ tailWord_7351250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351250).length < 2 ^ (prefixWord ++ tailWord_7351250).sum := by decide
  have hdescent : baseEnd_7351250 < baseStart_7351250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351289 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 1, 6]
def baseStart_7351289 : Nat := 118140960795 + 7351289 * 2 ^ 59
def prefixEnd_7351289 : Nat := 4983230072969 + 3 ^ 40 * 7351289 * 2
def baseEnd_7351289 : Nat := 1258248229036664593893181

theorem tailTrace_7351289 : CollatzResearch.WordTrace tailWord_7351289 prefixEnd_7351289 1258248229036664593893181 := by
  unfold tailWord_7351289
  simp only [CollatzResearch.WordTrace]
  refine ⟨268123537064542928050832921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178749024709695285367221947 268123537064542928050832921)
  ·
    refine ⟨201092652798407196038124691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 268123537064542928050832921 201092652798407196038124691)
    ·
      refine ⟨301638979197610794057187037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201092652798407196038124691 301638979197610794057187037)
      ·
        refine ⟨113114617199104047771445139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301638979197610794057187037 113114617199104047771445139)
        ·
          refine ⟨169671925798656071657167709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113114617199104047771445139 169671925798656071657167709)
          ·
            refine ⟨63626972174496026871437891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169671925798656071657167709 63626972174496026871437891)
            ·
              refine ⟨95440458261744040307156837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63626972174496026871437891 95440458261744040307156837)
              ·
                refine ⟨17895085924077007557591907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95440458261744040307156837 17895085924077007557591907)
                ·
                  refine ⟨26842628886115511336387861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17895085924077007557591907 26842628886115511336387861)
                  ·
                    refine ⟨1258248229036664593893181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26842628886115511336387861 1258248229036664593893181)
                    ·
                      rfl

theorem cell23_7351289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 6].length) (baseStart_7351289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351289 prefixEnd_7351289 := by exact prefixLift 7351289
  have htrace : WordTrace (prefixWord ++ tailWord_7351289) baseStart_7351289 baseEnd_7351289 := by
    simpa [prefixWord, tailWord_7351289, baseEnd_7351289] using wordTrace_append hprefix tailTrace_7351289
  have hstable : (prefixWord ++ tailWord_7351289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351289).length < 2 ^ (prefixWord ++ tailWord_7351289).sum := by decide
  have hdescent : baseEnd_7351289 < baseStart_7351289 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351330 : List Nat := [3, 3, 1, 1, 1, 3, 2, 2, 3, 2, 2]
def baseStart_7351330 : Nat := 118140960795 + 7351330 * 2 ^ 59
def prefixEnd_7351330 : Nat := 4983230072969 + 3 ^ 40 * 7351330 * 2
def baseEnd_7351330 : Nat := 3774765739816828121266855

theorem tailTrace_7351330 : CollatzResearch.WordTrace tailWord_7351330 prefixEnd_7351330 3774765739816828121266855 := by
  unfold tailWord_7351330
  simp only [CollatzResearch.WordTrace]
  refine ⟨67031258114348598013268861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178750021638262928035383629 67031258114348598013268861)
  ·
    refine ⟨25136721792880724254975823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67031258114348598013268861 25136721792880724254975823)
    ·
      refine ⟨37705082689321086382463735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25136721792880724254975823 37705082689321086382463735)
      ·
        refine ⟨56557624033981629573695603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37705082689321086382463735 56557624033981629573695603)
        ·
          refine ⟨84836436050972444360543405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56557624033981629573695603 84836436050972444360543405)
          ·
            refine ⟨31813663519114666635203777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84836436050972444360543405 31813663519114666635203777)
            ·
              refine ⟨23860247639335999976402833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31813663519114666635203777 23860247639335999976402833)
              ·
                refine ⟨17895185729501999982302125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23860247639335999976402833 17895185729501999982302125)
                ·
                  refine ⟨6710694648563249993363297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17895185729501999982302125 6710694648563249993363297)
                  ·
                    refine ⟨5033020986422437495022473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6710694648563249993363297 5033020986422437495022473)
                    ·
                      refine ⟨3774765739816828121266855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5033020986422437495022473 3774765739816828121266855)
                      ·
                        rfl

theorem cell23_7351330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_7351330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351330 prefixEnd_7351330 := by exact prefixLift 7351330
  have htrace : WordTrace (prefixWord ++ tailWord_7351330) baseStart_7351330 baseEnd_7351330 := by
    simpa [prefixWord, tailWord_7351330, baseEnd_7351330] using wordTrace_append hprefix tailTrace_7351330
  have hstable : (prefixWord ++ tailWord_7351330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351330).length < 2 ^ (prefixWord ++ tailWord_7351330).sum := by decide
  have hdescent : baseEnd_7351330 < baseStart_7351330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351333 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_7351333 : Nat := 118140960795 + 7351333 * 2 ^ 59
def prefixEnd_7351333 : Nat := 4983230072969 + 3 ^ 40 * 7351333 * 2
def baseEnd_7351333 : Nat := 3774767280258791609529341

theorem tailTrace_7351333 : CollatzResearch.WordTrace tailWord_7351333 prefixEnd_7351333 3774767280258791609529341 := by
  unfold tailWord_7351333
  simp only [CollatzResearch.WordTrace]
  refine ⟨268125141876383523565434653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178750094584255682376956435 268125141876383523565434653)
  ·
    refine ⟨100546928203643821337037995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268125141876383523565434653 100546928203643821337037995)
    ·
      refine ⟨150820392305465732005556993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100546928203643821337037995 150820392305465732005556993)
      ·
        refine ⟨113115294229099299004167745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150820392305465732005556993 113115294229099299004167745)
        ·
          refine ⟨84836470671824474253125809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113115294229099299004167745 84836470671824474253125809)
          ·
            refine ⟨63627353003868355689844357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84836470671824474253125809 63627353003868355689844357)
            ·
              refine ⟨11930128688225316691845817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63627353003868355689844357 11930128688225316691845817)
              ·
                refine ⟨8947596516168987518884363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11930128688225316691845817 8947596516168987518884363)
                ·
                  refine ⟨13421394774253481278326545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947596516168987518884363 13421394774253481278326545)
                  ·
                    refine ⟨10066046080690110958744909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421394774253481278326545 10066046080690110958744909)
                    ·
                      refine ⟨3774767280258791609529341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066046080690110958744909 3774767280258791609529341)
                      ·
                        rfl

theorem cell23_7351333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_7351333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351333 prefixEnd_7351333 := by exact prefixLift 7351333
  have htrace : WordTrace (prefixWord ++ tailWord_7351333) baseStart_7351333 baseEnd_7351333 := by
    simpa [prefixWord, tailWord_7351333, baseEnd_7351333] using wordTrace_append hprefix tailTrace_7351333
  have hstable : (prefixWord ++ tailWord_7351333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351333).length < 2 ^ (prefixWord ++ tailWord_7351333).sum := by decide
  have hdescent : baseEnd_7351333 < baseStart_7351333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351346 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3]
def baseStart_7351346 : Nat := 118140960795 + 7351346 * 2 ^ 59
def prefixEnd_7351346 : Nat := 4983230072969 + 3 ^ 40 * 7351346 * 2
def baseEnd_7351346 : Nat := 3774773955507300058666781

theorem tailTrace_7351346 : CollatzResearch.WordTrace tailWord_7351346 prefixEnd_7351346 3774773955507300058666781 := by
  unfold tailWord_7351346
  simp only [CollatzResearch.WordTrace]
  refine ⟨67031404006334106696414473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178750410683557617857105261 67031404006334106696414473)
  ·
    refine ⟨50273553004750580022310855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67031404006334106696414473 50273553004750580022310855)
    ·
      refine ⟨75410329507125870033466283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50273553004750580022310855 75410329507125870033466283)
      ·
        refine ⟨113115494260688805050199425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75410329507125870033466283 113115494260688805050199425)
        ·
          refine ⟨84836620695516603787649569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113115494260688805050199425 84836620695516603787649569)
          ·
            refine ⟨63627465521637452840737177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84836620695516603787649569 63627465521637452840737177)
            ·
              refine ⟨47720599141228089630552883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63627465521637452840737177 47720599141228089630552883)
              ·
                refine ⟨71580898711842134445829325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47720599141228089630552883 71580898711842134445829325)
                ·
                  refine ⟨26842837016940800417185997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71580898711842134445829325 26842837016940800417185997)
                  ·
                    refine ⟨10066063881352800156444749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26842837016940800417185997 10066063881352800156444749)
                    ·
                      refine ⟨3774773955507300058666781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066063881352800156444749 3774773955507300058666781)
                      ·
                        rfl

theorem cell23_7351346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_7351346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351346 prefixEnd_7351346 := by exact prefixLift 7351346
  have htrace : WordTrace (prefixWord ++ tailWord_7351346) baseStart_7351346 baseEnd_7351346 := by
    simpa [prefixWord, tailWord_7351346, baseEnd_7351346] using wordTrace_append hprefix tailTrace_7351346
  have hstable : (prefixWord ++ tailWord_7351346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351346).length < 2 ^ (prefixWord ++ tailWord_7351346).sum := by decide
  have hdescent : baseEnd_7351346 < baseStart_7351346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351349 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 9]
def baseStart_7351349 : Nat := 118140960795 + 7351349 * 2 ^ 59
def prefixEnd_7351349 : Nat := 4983230072969 + 3 ^ 40 * 7351349 * 2
def baseEnd_7351349 : Nat := 1258258498649754515643089

theorem tailTrace_7351349 : CollatzResearch.WordTrace tailWord_7351349 prefixEnd_7351349 1258258498649754515643089 := by
  unfold tailWord_7351349
  simp only [CollatzResearch.WordTrace]
  refine ⟨268125725444325558298017101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178750483629550372198678067 268125725444325558298017101)
  ·
    refine ⟨100547147041622084361756413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 268125725444325558298017101 100547147041622084361756413)
    ·
      refine ⟨37705180140608281635658655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100547147041622084361756413 37705180140608281635658655)
      ·
        refine ⟨56557770210912422453487983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37705180140608281635658655 56557770210912422453487983)
        ·
          refine ⟨84836655316368633680231975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56557770210912422453487983 84836655316368633680231975)
          ·
            refine ⟨127254982974552950520347963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84836655316368633680231975 127254982974552950520347963)
            ·
              refine ⟨190882474461829425780521945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127254982974552950520347963 190882474461829425780521945)
              ·
                refine ⟨143161855846372069335391459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190882474461829425780521945 143161855846372069335391459)
                ·
                  refine ⟨214742783769558104003087189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 143161855846372069335391459 214742783769558104003087189)
                  ·
                    refine ⟨1258258498649754515643089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 214742783769558104003087189 1258258498649754515643089)
                    ·
                      rfl

theorem cell23_7351349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_7351349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351349 prefixEnd_7351349 := by exact prefixLift 7351349
  have htrace : WordTrace (prefixWord ++ tailWord_7351349) baseStart_7351349 baseEnd_7351349 := by
    simpa [prefixWord, tailWord_7351349, baseEnd_7351349] using wordTrace_append hprefix tailTrace_7351349
  have hstable : (prefixWord ++ tailWord_7351349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351349).length < 2 ^ (prefixWord ++ tailWord_7351349).sum := by decide
  have hdescent : baseEnd_7351349 < baseStart_7351349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351350 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_7351350 : Nat := 118140960795 + 7351350 * 2 ^ 59
def prefixEnd_7351350 : Nat := 4983230072969 + 3 ^ 40 * 7351350 * 2
def baseEnd_7351350 : Nat := 3774776009429918043016763

theorem tailTrace_7351350 : CollatzResearch.WordTrace tailWord_7351350 prefixEnd_7351350 3774776009429918043016763 := by
  unfold tailWord_7351350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757860119832620966800219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178750507944881290312535669 16757860119832620966800219)
  ·
    refine ⟨25136790179748931450200329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16757860119832620966800219 25136790179748931450200329)
    ·
      refine ⟨18852592634811698587650247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25136790179748931450200329 18852592634811698587650247)
      ·
        refine ⟨28278888952217547881475371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18852592634811698587650247 28278888952217547881475371)
        ·
          refine ⟨42418333428326321822213057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28278888952217547881475371 42418333428326321822213057)
          ·
            refine ⟨31813750071244741366659793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42418333428326321822213057 31813750071244741366659793)
            ·
              refine ⟨23860312553433556024994845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31813750071244741366659793 23860312553433556024994845)
              ·
                refine ⟨8947617207537583509373067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23860312553433556024994845 8947617207537583509373067)
                ·
                  refine ⟨13421425811306375264059601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8947617207537583509373067 13421425811306375264059601)
                  ·
                    refine ⟨10066069358479781448044701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13421425811306375264059601 10066069358479781448044701)
                    ·
                      refine ⟨3774776009429918043016763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10066069358479781448044701 3774776009429918043016763)
                      ·
                        rfl

theorem cell23_7351350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_7351350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351350 prefixEnd_7351350 := by exact prefixLift 7351350
  have htrace : WordTrace (prefixWord ++ tailWord_7351350) baseStart_7351350 baseEnd_7351350 := by
    simpa [prefixWord, tailWord_7351350, baseEnd_7351350] using wordTrace_append hprefix tailTrace_7351350
  have hstable : (prefixWord ++ tailWord_7351350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351350).length < 2 ^ (prefixWord ++ tailWord_7351350).sum := by decide
  have hdescent : baseEnd_7351350 < baseStart_7351350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7351359 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_7351359 : Nat := 118140960795 + 7351359 * 2 ^ 59
def prefixEnd_7351359 : Nat := 4983230072969 + 3 ^ 40 * 7351359 * 2
def baseEnd_7351359 : Nat := 3774780630755808507804221

theorem tailTrace_7351359 : CollatzResearch.WordTrace tailWord_7351359 prefixEnd_7351359 3774780630755808507804221 := by
  unfold tailWord_7351359
  simp only [CollatzResearch.WordTrace]
  refine ⟨268126090174289330005881131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178750726782859553337254087 268126090174289330005881131)
  ·
    refine ⟨402189135261433995008821697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 268126090174289330005881131 402189135261433995008821697)
    ·
      refine ⟨301641851446075496256616273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 402189135261433995008821697 301641851446075496256616273)
      ·
        refine ⟨226231388584556622192462205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301641851446075496256616273 226231388584556622192462205)
        ·
          refine ⟨84836770719208733322173327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226231388584556622192462205 84836770719208733322173327)
          ·
            refine ⟨127255156078813099983259991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84836770719208733322173327 127255156078813099983259991)
            ·
              refine ⟨190882734118219649974889987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127255156078813099983259991 190882734118219649974889987)
              ·
                refine ⟨286324101177329474962334981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190882734118219649974889987 286324101177329474962334981)
                ·
                  refine ⟨53685768970749276555437809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 286324101177329474962334981 53685768970749276555437809)
                  ·
                    refine ⟨40264326728061957416578357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53685768970749276555437809 40264326728061957416578357)
                    ·
                      refine ⟨3774780630755808507804221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40264326728061957416578357 3774780630755808507804221)
                      ·
                        rfl

theorem cell23_7351359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_7351359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7351359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7351359 prefixEnd_7351359 := by exact prefixLift 7351359
  have htrace : WordTrace (prefixWord ++ tailWord_7351359) baseStart_7351359 baseEnd_7351359 := by
    simpa [prefixWord, tailWord_7351359, baseEnd_7351359] using wordTrace_append hprefix tailTrace_7351359
  have hstable : (prefixWord ++ tailWord_7351359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7351359).length < 2 ^ (prefixWord ++ tailWord_7351359).sum := by decide
  have hdescent : baseEnd_7351359 < baseStart_7351359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7351359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
