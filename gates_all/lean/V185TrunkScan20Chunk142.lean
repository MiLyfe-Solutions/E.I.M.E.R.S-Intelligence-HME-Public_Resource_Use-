import V185TrunkScan20Chunk141

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_863565 : List Nat := [1, 6, 1, 3, 2, 1, 2, 4]
def baseStart_863565 : Nat := 118140960795 + 863565 * 2 ^ 59
def prefixEnd_863565 : Nat := 4983230072969 + 3 ^ 40 * 863565 * 2
def baseEnd_863565 : Nat := 131384865600005639012161

theorem tailTrace_863565 : CollatzResearch.WordTrace tailWord_863565 prefixEnd_863565 131384865600005639012161 := by
  unfold tailWord_863565
  simp only [CollatzResearch.WordTrace]
  refine ⟨31496803116458965005216149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20997868744305976670144099 31496803116458965005216149)
  ·
    refine ⟨1476412646084013984619507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31496803116458965005216149 1476412646084013984619507)
    ·
      refine ⟨2214618969126020976929261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1476412646084013984619507 2214618969126020976929261)
      ·
        refine ⟨830482113422257866348473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2214618969126020976929261 830482113422257866348473)
        ·
          refine ⟨622861585066693399761355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830482113422257866348473 622861585066693399761355)
          ·
            refine ⟨934292377600040099642033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622861585066693399761355 934292377600040099642033)
            ·
              refine ⟨700719283200030074731525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934292377600040099642033 700719283200030074731525)
              ·
                refine ⟨131384865600005639012161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700719283200030074731525 131384865600005639012161)
                ·
                  rfl

theorem cell20_863565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 4].length) (baseStart_863565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863565 prefixEnd_863565 := by exact prefixLift 863565
  have htrace : WordTrace (prefixWord ++ tailWord_863565) baseStart_863565 baseEnd_863565 := by
    simpa [prefixWord, tailWord_863565, baseEnd_863565] using wordTrace_append hprefix tailTrace_863565
  have hstable : (prefixWord ++ tailWord_863565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863565).length < 2 ^ (prefixWord ++ tailWord_863565).sum := by decide
  have hdescent : baseEnd_863565 < baseStart_863565 := by decide
  rcases family_descends (prefixWord ++ tailWord_863565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863573 : List Nat := [1, 3, 2, 2, 3, 2, 1, 6]
def baseStart_863573 : Nat := 118140960795 + 863573 * 2 ^ 59
def prefixEnd_863573 : Nat := 4983230072969 + 3 ^ 40 * 863573 * 2
def baseEnd_863573 : Nat := 131386082739334814923261

theorem tailTrace_863573 : CollatzResearch.WordTrace tailWord_863573 prefixEnd_863573 131386082739334814923261 := by
  unfold tailWord_863573
  simp only [CollatzResearch.WordTrace]
  refine ⟨31497094900429982371507373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20998063266953321581004915 31497094900429982371507373)
  ·
    refine ⟨11811410587661243389315265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31497094900429982371507373 11811410587661243389315265)
    ·
      refine ⟨8858557940745932541986449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11811410587661243389315265 8858557940745932541986449)
      ·
        refine ⟨6643918455559449406489837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8858557940745932541986449 6643918455559449406489837)
        ·
          refine ⟨2491469420834793527433689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6643918455559449406489837 2491469420834793527433689)
          ·
            refine ⟨1868602065626095145575267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2491469420834793527433689 1868602065626095145575267)
            ·
              refine ⟨2802903098439142718362901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1868602065626095145575267 2802903098439142718362901)
              ·
                refine ⟨131386082739334814923261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2802903098439142718362901 131386082739334814923261)
                ·
                  rfl

theorem cell20_863573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 6].length) (baseStart_863573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863573 prefixEnd_863573 := by exact prefixLift 863573
  have htrace : WordTrace (prefixWord ++ tailWord_863573) baseStart_863573 baseEnd_863573 := by
    simpa [prefixWord, tailWord_863573, baseEnd_863573] using wordTrace_append hprefix tailTrace_863573
  have hstable : (prefixWord ++ tailWord_863573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863573).length < 2 ^ (prefixWord ++ tailWord_863573).sum := by decide
  have hdescent : baseEnd_863573 < baseStart_863573 := by decide
  rcases family_descends (prefixWord ++ tailWord_863573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863687 : List Nat := [1, 1, 4, 1, 1, 3, 5, 4]
def baseStart_863687 : Nat := 118140960795 + 863687 * 2 ^ 59
def prefixEnd_863687 : Nat := 4983230072969 + 3 ^ 40 * 863687 * 2
def baseEnd_863687 : Nat := 131403426974775571656439

theorem tailTrace_863687 : CollatzResearch.WordTrace tailWord_863687 prefixEnd_863687 131403426974775571656439 := by
  unfold tailWord_863687
  simp only [CollatzResearch.WordTrace]
  refine ⟨31501252822016979841157315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21000835214677986560771543 31501252822016979841157315)
  ·
    refine ⟨47251879233025469761735973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31501252822016979841157315 47251879233025469761735973)
    ·
      refine ⟨8859727356192275580325495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47251879233025469761735973 8859727356192275580325495)
      ·
        refine ⟨13289591034288413370488243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8859727356192275580325495 13289591034288413370488243)
        ·
          refine ⟨19934386551432620055732365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13289591034288413370488243 19934386551432620055732365)
          ·
            refine ⟨7475394956787232520899637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19934386551432620055732365 7475394956787232520899637)
            ·
              refine ⟨700818277198803048834341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7475394956787232520899637 700818277198803048834341)
              ·
                refine ⟨131403426974775571656439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 700818277198803048834341 131403426974775571656439)
                ·
                  rfl

theorem cell20_863687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 4].length) (baseStart_863687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863687 prefixEnd_863687 := by exact prefixLift 863687
  have htrace : WordTrace (prefixWord ++ tailWord_863687) baseStart_863687 baseEnd_863687 := by
    simpa [prefixWord, tailWord_863687, baseEnd_863687] using wordTrace_append hprefix tailTrace_863687
  have hstable : (prefixWord ++ tailWord_863687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863687).length < 2 ^ (prefixWord ++ tailWord_863687).sum := by decide
  have hdescent : baseEnd_863687 < baseStart_863687 := by decide
  rcases family_descends (prefixWord ++ tailWord_863687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863701 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 6]
def baseStart_863701 : Nat := 118140960795 + 863701 * 2 ^ 59
def prefixEnd_863701 : Nat := 4983230072969 + 3 ^ 40 * 863701 * 2
def baseEnd_863701 : Nat := 394216670905804888502593

theorem tailTrace_863701 : CollatzResearch.WordTrace tailWord_863701 prefixEnd_863701 394216670905804888502593 := by
  unfold tailWord_863701
  simp only [CollatzResearch.WordTrace]
  refine ⟨31501763443966260232166957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21001175629310840154777971 31501763443966260232166957)
  ·
    refine ⟨11813161291487347587062609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31501763443966260232166957 11813161291487347587062609)
    ·
      refine ⟨8859870968615510690296957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11813161291487347587062609 8859870968615510690296957)
      ·
        refine ⟨3322451613230816508861359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8859870968615510690296957 3322451613230816508861359)
        ·
          refine ⟨4983677419846224763292039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3322451613230816508861359 4983677419846224763292039)
          ·
            refine ⟨7475516129769337144938059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4983677419846224763292039 7475516129769337144938059)
            ·
              refine ⟨11213274194654005717407089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7475516129769337144938059 11213274194654005717407089)
              ·
                refine ⟨8409955645990504288055317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11213274194654005717407089 8409955645990504288055317)
                ·
                  refine ⟨394216670905804888502593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8409955645990504288055317 394216670905804888502593)
                  ·
                    rfl

theorem cell20_863701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_863701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863701 prefixEnd_863701 := by exact prefixLift 863701
  have htrace : WordTrace (prefixWord ++ tailWord_863701) baseStart_863701 baseEnd_863701 := by
    simpa [prefixWord, tailWord_863701, baseEnd_863701] using wordTrace_append hprefix tailTrace_863701
  have hstable : (prefixWord ++ tailWord_863701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863701).length < 2 ^ (prefixWord ++ tailWord_863701).sum := by decide
  have hdescent : baseEnd_863701 < baseStart_863701 := by decide
  rcases family_descends (prefixWord ++ tailWord_863701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863753 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 7]
def baseStart_863753 : Nat := 118140960795 + 863753 * 2 ^ 59
def prefixEnd_863753 : Nat := 4983230072969 + 3 ^ 40 * 863753 * 2
def baseEnd_863753 : Nat := 394240405122723818769047

theorem tailTrace_863753 : CollatzResearch.WordTrace tailWord_863753 prefixEnd_863753 394240405122723818769047 := by
  unfold tailWord_863753
  simp only [CollatzResearch.WordTrace]
  refine ⟨31503660039777873113059913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21002440026518582075373275 31503660039777873113059913)
  ·
    refine ⟨23627745029833404834794935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31503660039777873113059913 23627745029833404834794935)
    ·
      refine ⟨35441617544750107252192403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23627745029833404834794935 35441617544750107252192403)
      ·
        refine ⟨53162426317125160878288605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35441617544750107252192403 53162426317125160878288605)
        ·
          refine ⟨19935909868921935329358227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53162426317125160878288605 19935909868921935329358227)
          ·
            refine ⟨29903864803382902994037341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19935909868921935329358227 29903864803382902994037341)
            ·
              refine ⟨11213949301268588622764003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29903864803382902994037341 11213949301268588622764003)
              ·
                refine ⟨16820923951902882934146005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11213949301268588622764003 16820923951902882934146005)
                ·
                  refine ⟨394240405122723818769047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16820923951902882934146005 394240405122723818769047)
                  ·
                    rfl

theorem cell20_863753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_863753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863753 prefixEnd_863753 := by exact prefixLift 863753
  have htrace : WordTrace (prefixWord ++ tailWord_863753) baseStart_863753 baseEnd_863753 := by
    simpa [prefixWord, tailWord_863753, baseEnd_863753] using wordTrace_append hprefix tailTrace_863753
  have hstable : (prefixWord ++ tailWord_863753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863753).length < 2 ^ (prefixWord ++ tailWord_863753).sum := by decide
  have hdescent : baseEnd_863753 < baseStart_863753 := by decide
  rcases family_descends (prefixWord ++ tailWord_863753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863770 : List Nat := [3, 1, 1, 3, 1, 1, 1, 6, 3]
def baseStart_863770 : Nat := 118140960795 + 863770 * 2 ^ 59
def prefixEnd_863770 : Nat := 4983230072969 + 3 ^ 40 * 863770 * 2
def baseEnd_863770 : Nat := 394248164385947315202311

theorem tailTrace_863770 : CollatzResearch.WordTrace tailWord_863770 prefixEnd_863770 394248164385947315202311 := by
  unfold tailWord_863770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7876070020179071254107191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21002853387144190010952509 7876070020179071254107191)
  ·
    refine ⟨11814105030268606881160787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7876070020179071254107191 11814105030268606881160787)
    ·
      refine ⟨17721157545402910321741181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11814105030268606881160787 17721157545402910321741181)
      ·
        refine ⟨6645434079526091370652943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17721157545402910321741181 6645434079526091370652943)
        ·
          refine ⟨9968151119289137055979415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6645434079526091370652943 9968151119289137055979415)
          ·
            refine ⟨14952226678933705583969123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9968151119289137055979415 14952226678933705583969123)
            ·
              refine ⟨22428340018400558375953685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14952226678933705583969123 22428340018400558375953685)
              ·
                refine ⟨1051328438362526173872829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22428340018400558375953685 1051328438362526173872829)
                ·
                  refine ⟨394248164385947315202311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051328438362526173872829 394248164385947315202311)
                  ·
                    rfl

theorem cell20_863770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_863770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863770 prefixEnd_863770 := by exact prefixLift 863770
  have htrace : WordTrace (prefixWord ++ tailWord_863770) baseStart_863770 baseEnd_863770 := by
    simpa [prefixWord, tailWord_863770, baseEnd_863770] using wordTrace_append hprefix tailTrace_863770
  have hstable : (prefixWord ++ tailWord_863770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863770).length < 2 ^ (prefixWord ++ tailWord_863770).sum := by decide
  have hdescent : baseEnd_863770 < baseStart_863770 := by decide
  rcases family_descends (prefixWord ++ tailWord_863770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863867 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 5]
def baseStart_863867 : Nat := 118140960795 + 863867 * 2 ^ 59
def prefixEnd_863867 : Nat := 4983230072969 + 3 ^ 40 * 863867 * 2
def baseEnd_863867 : Nat := 394292437829046088968581

theorem tailTrace_863867 : CollatzResearch.WordTrace tailWord_863867 prefixEnd_863867 394292437829046088968581 := by
  unfold tailWord_863867
  simp only [CollatzResearch.WordTrace]
  refine ⟨31507817961364870582709855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21005211974243247055139903 31507817961364870582709855)
  ·
    refine ⟨47261726942047305874064783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31507817961364870582709855 47261726942047305874064783)
    ·
      refine ⟨70892590413070958811097175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47261726942047305874064783 70892590413070958811097175)
      ·
        refine ⟨106338885619606438216645763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70892590413070958811097175 106338885619606438216645763)
        ·
          refine ⟨159508328429409657324968645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106338885619606438216645763 159508328429409657324968645)
          ·
            refine ⟨29907811580514310748431621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 159508328429409657324968645 29907811580514310748431621)
            ·
              refine ⟨5607714671346433265330929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29907811580514310748431621 5607714671346433265330929)
              ·
                refine ⟨4205786003509824948998197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5607714671346433265330929 4205786003509824948998197)
                ·
                  refine ⟨394292437829046088968581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4205786003509824948998197 394292437829046088968581)
                  ·
                    rfl

theorem cell20_863867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_863867 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863867 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863867 prefixEnd_863867 := by exact prefixLift 863867
  have htrace : WordTrace (prefixWord ++ tailWord_863867) baseStart_863867 baseEnd_863867 := by
    simpa [prefixWord, tailWord_863867, baseEnd_863867] using wordTrace_append hprefix tailTrace_863867
  have hstable : (prefixWord ++ tailWord_863867).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863867).length < 2 ^ (prefixWord ++ tailWord_863867).sum := by decide
  have hdescent : baseEnd_863867 < baseStart_863867 := by decide
  rcases family_descends (prefixWord ++ tailWord_863867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863938 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 4]
def baseStart_863938 : Nat := 118140960795 + 863938 * 2 ^ 59
def prefixEnd_863938 : Nat := 4983230072969 + 3 ^ 40 * 863938 * 2
def baseEnd_863938 : Nat := 394324844163685397601625

theorem tailTrace_863938 : CollatzResearch.WordTrace tailWord_863938 prefixEnd_863938 394324844163685397601625 := by
  unfold tailWord_863938
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877601886026912427136117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21006938362738433139029645 7877601886026912427136117)
  ·
    refine ⟨738525176815023040044011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7877601886026912427136117 738525176815023040044011)
    ·
      refine ⟨1107787765222534560066017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738525176815023040044011 1107787765222534560066017)
      ·
        refine ⟨830840823916900920049513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1107787765222534560066017 830840823916900920049513)
        ·
          refine ⟨623130617937675690037135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 830840823916900920049513 623130617937675690037135)
          ·
            refine ⟨934695926906513535055703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623130617937675690037135 934695926906513535055703)
            ·
              refine ⟨1402043890359770302583555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934695926906513535055703 1402043890359770302583555)
              ·
                refine ⟨2103065835539655453875333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402043890359770302583555 2103065835539655453875333)
                ·
                  refine ⟨394324844163685397601625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103065835539655453875333 394324844163685397601625)
                  ·
                    rfl

theorem cell20_863938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_863938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863938 prefixEnd_863938 := by exact prefixLift 863938
  have htrace : WordTrace (prefixWord ++ tailWord_863938) baseStart_863938 baseEnd_863938 := by
    simpa [prefixWord, tailWord_863938, baseEnd_863938] using wordTrace_append hprefix tailTrace_863938
  have hstable : (prefixWord ++ tailWord_863938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863938).length < 2 ^ (prefixWord ++ tailWord_863938).sum := by decide
  have hdescent : baseEnd_863938 < baseStart_863938 := by decide
  rcases family_descends (prefixWord ++ tailWord_863938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863942 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_863942 : Nat := 118140960795 + 863942 * 2 ^ 59
def prefixEnd_863942 : Nat := 4983230072969 + 3 ^ 40 * 863942 * 2
def baseEnd_863942 : Nat := 394326669872679161468275

theorem tailTrace_863942 : CollatzResearch.WordTrace tailWord_863942 prefixEnd_863942 394326669872679161468275 := by
  unfold tailWord_863942
  simp only [CollatzResearch.WordTrace]
  refine ⟨984704794877911199740315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21007035624062105594460053 984704794877911199740315)
  ·
    refine ⟨1477057192316866799610473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984704794877911199740315 1477057192316866799610473)
    ·
      refine ⟨1107792894237650099707855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1477057192316866799610473 1107792894237650099707855)
      ·
        refine ⟨1661689341356475149561783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107792894237650099707855 1661689341356475149561783)
        ·
          refine ⟨2492534012034712724342675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661689341356475149561783 2492534012034712724342675)
          ·
            refine ⟨3738801018052069086514013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492534012034712724342675 3738801018052069086514013)
            ·
              refine ⟨1402050381769525907442755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3738801018052069086514013 1402050381769525907442755)
              ·
                refine ⟨2103075572654288861164133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1402050381769525907442755 2103075572654288861164133)
                ·
                  refine ⟨394326669872679161468275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103075572654288861164133 394326669872679161468275)
                  ·
                    rfl

theorem cell20_863942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_863942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863942 prefixEnd_863942 := by exact prefixLift 863942
  have htrace : WordTrace (prefixWord ++ tailWord_863942) baseStart_863942 baseEnd_863942 := by
    simpa [prefixWord, tailWord_863942, baseEnd_863942] using wordTrace_append hprefix tailTrace_863942
  have hstable : (prefixWord ++ tailWord_863942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863942).length < 2 ^ (prefixWord ++ tailWord_863942).sum := by decide
  have hdescent : baseEnd_863942 < baseStart_863942 := by decide
  rcases family_descends (prefixWord ++ tailWord_863942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863943 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 5]
def baseStart_863943 : Nat := 118140960795 + 863943 * 2 ^ 59
def prefixEnd_863943 : Nat := 4983230072969 + 3 ^ 40 * 863943 * 2
def baseEnd_863943 : Nat := 394327126299927602434937

theorem tailTrace_863943 : CollatzResearch.WordTrace tailWord_863943 prefixEnd_863943 394327126299927602434937 := by
  unfold tailWord_863943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31510589909089535562476483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21007059939393023708317655 31510589909089535562476483)
  ·
    refine ⟨47265884863634303343714725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31510589909089535562476483 47265884863634303343714725)
    ·
      refine ⟨8862353411931431876946511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47265884863634303343714725 8862353411931431876946511)
      ·
        refine ⟨13293530117897147815419767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8862353411931431876946511 13293530117897147815419767)
        ·
          refine ⟨19940295176845721723129651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13293530117897147815419767 19940295176845721723129651)
          ·
            refine ⟨29910442765268582584694477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19940295176845721723129651 29910442765268582584694477)
            ·
              refine ⟨11216416036975718469260429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29910442765268582584694477 11216416036975718469260429)
              ·
                refine ⟨4206156013865894425972661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11216416036975718469260429 4206156013865894425972661)
                ·
                  refine ⟨394327126299927602434937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206156013865894425972661 394327126299927602434937)
                  ·
                    rfl

theorem cell20_863943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_863943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863943 prefixEnd_863943 := by exact prefixLift 863943
  have htrace : WordTrace (prefixWord ++ tailWord_863943) baseStart_863943 baseEnd_863943 := by
    simpa [prefixWord, tailWord_863943, baseEnd_863943] using wordTrace_append hprefix tailTrace_863943
  have hstable : (prefixWord ++ tailWord_863943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863943).length < 2 ^ (prefixWord ++ tailWord_863943).sum := by decide
  have hdescent : baseEnd_863943 < baseStart_863943 := by decide
  rcases family_descends (prefixWord ++ tailWord_863943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863956 : List Nat := [2, 4, 1, 3, 1, 1, 4, 1, 3]
def baseStart_863956 : Nat := 118140960795 + 863956 * 2 ^ 59
def prefixEnd_863956 : Nat := 4983230072969 + 3 ^ 40 * 863956 * 2
def baseEnd_863956 : Nat := 394333059854157335001551

theorem tailTrace_863956 : CollatzResearch.WordTrace tailWord_863956 prefixEnd_863956 394333059854157335001551 := by
  unfold tailWord_863956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755532029021219391349861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21007376038694959188466481 15755532029021219391349861)
  ·
    refine ⟨2954162255441478635878099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15755532029021219391349861 2954162255441478635878099)
    ·
      refine ⟨4431243383162217953817149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2954162255441478635878099 4431243383162217953817149)
      ·
        refine ⟨1661716268685831732681431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4431243383162217953817149 1661716268685831732681431)
        ·
          refine ⟨2492574403028747599022147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1661716268685831732681431 2492574403028747599022147)
          ·
            refine ⟨3738861604543121398533221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492574403028747599022147 3738861604543121398533221)
            ·
              refine ⟨701036550851835262224979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3738861604543121398533221 701036550851835262224979)
              ·
                refine ⟨1051554826277752893337469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701036550851835262224979 1051554826277752893337469)
                ·
                  refine ⟨394333059854157335001551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051554826277752893337469 394333059854157335001551)
                  ·
                    rfl

theorem cell20_863956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 1, 3].length) (baseStart_863956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863956 prefixEnd_863956 := by exact prefixLift 863956
  have htrace : WordTrace (prefixWord ++ tailWord_863956) baseStart_863956 baseEnd_863956 := by
    simpa [prefixWord, tailWord_863956, baseEnd_863956] using wordTrace_append hprefix tailTrace_863956
  have hstable : (prefixWord ++ tailWord_863956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863956).length < 2 ^ (prefixWord ++ tailWord_863956).sum := by decide
  have hdescent : baseEnd_863956 < baseStart_863956 := by decide
  rcases family_descends (prefixWord ++ tailWord_863956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_863960 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 3]
def baseStart_863960 : Nat := 118140960795 + 863960 * 2 ^ 59
def prefixEnd_863960 : Nat := 4983230072969 + 3 ^ 40 * 863960 * 2
def baseEnd_863960 : Nat := 394334885563151098868201

theorem tailTrace_863960 : CollatzResearch.WordTrace tailWord_863960 prefixEnd_863960 394334885563151098868201 := by
  unfold tailWord_863960
  simp only [CollatzResearch.WordTrace]
  refine ⟨15755604975013973732922667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21007473300018631643896889 15755604975013973732922667)
  ·
    refine ⟨23633407462520960599384001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15755604975013973732922667 23633407462520960599384001)
    ·
      refine ⟨17725055596890720449538001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23633407462520960599384001 17725055596890720449538001)
      ·
        refine ⟨13293791697668040337153501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17725055596890720449538001 13293791697668040337153501)
        ·
          refine ⟨4985171886625515126432563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13293791697668040337153501 4985171886625515126432563)
          ·
            refine ⟨7477757829938272689648845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4985171886625515126432563 7477757829938272689648845)
            ·
              refine ⟨2804159186226852258618317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7477757829938272689648845 2804159186226852258618317)
              ·
                refine ⟨1051559694835069596981869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2804159186226852258618317 1051559694835069596981869)
                ·
                  refine ⟨394334885563151098868201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051559694835069596981869 394334885563151098868201)
                  ·
                    rfl

theorem cell20_863960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 3].length) (baseStart_863960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_863960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_863960 prefixEnd_863960 := by exact prefixLift 863960
  have htrace : WordTrace (prefixWord ++ tailWord_863960) baseStart_863960 baseEnd_863960 := by
    simpa [prefixWord, tailWord_863960, baseEnd_863960] using wordTrace_append hprefix tailTrace_863960
  have hstable : (prefixWord ++ tailWord_863960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_863960).length < 2 ^ (prefixWord ++ tailWord_863960).sum := by decide
  have hdescent : baseEnd_863960 < baseStart_863960 := by decide
  rcases family_descends (prefixWord ++ tailWord_863960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864001 : List Nat := [1, 2, 4, 1, 1, 1, 6, 2, 2]
def baseStart_864001 : Nat := 118140960795 + 864001 * 2 ^ 59
def prefixEnd_864001 : Nat := 4983230072969 + 3 ^ 40 * 864001 * 2
def baseEnd_864001 : Nat := 394353599080337178501367

theorem tailTrace_864001 : CollatzResearch.WordTrace tailWord_864001 prefixEnd_864001 394353599080337178501367 := by
  unfold tailWord_864001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31512705342879411468087857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21008470228586274312058571 31512705342879411468087857)
  ·
    refine ⟨23634529007159558601065893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31512705342879411468087857 23634529007159558601065893)
    ·
      refine ⟨4431474188842417237699855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23634529007159558601065893 4431474188842417237699855)
      ·
        refine ⟨6647211283263625856549783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431474188842417237699855 6647211283263625856549783)
        ·
          refine ⟨9970816924895438784824675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647211283263625856549783 9970816924895438784824675)
          ·
            refine ⟨14956225387343158177237013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970816924895438784824675 14956225387343158177237013)
            ·
              refine ⟨701073065031710539557985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14956225387343158177237013 701073065031710539557985)
              ·
                refine ⟨525804798773782904668489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 701073065031710539557985 525804798773782904668489)
                ·
                  refine ⟨394353599080337178501367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525804798773782904668489 394353599080337178501367)
                  ·
                    rfl

theorem cell20_864001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 6, 2, 2].length) (baseStart_864001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864001 prefixEnd_864001 := by exact prefixLift 864001
  have htrace : WordTrace (prefixWord ++ tailWord_864001) baseStart_864001 baseEnd_864001 := by
    simpa [prefixWord, tailWord_864001, baseEnd_864001] using wordTrace_append hprefix tailTrace_864001
  have hstable : (prefixWord ++ tailWord_864001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864001).length < 2 ^ (prefixWord ++ tailWord_864001).sum := by decide
  have hdescent : baseEnd_864001 < baseStart_864001 := by decide
  rcases family_descends (prefixWord ++ tailWord_864001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864012 : List Nat := [2, 2, 1, 2, 2, 1, 5, 5]
def baseStart_864012 : Nat := 118140960795 + 864012 * 2 ^ 59
def prefixEnd_864012 : Nat := 4983230072969 + 3 ^ 40 * 864012 * 2
def baseEnd_864012 : Nat := 131452873260023343044885

theorem tailTrace_864012 : CollatzResearch.WordTrace tailWord_864012 prefixEnd_864012 131452873260023343044885 := by
  unfold tailWord_864012
  simp only [CollatzResearch.WordTrace]
  refine ⟨15756553272919780173369145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21008737697226373564492193 15756553272919780173369145)
  ·
    refine ⟨11817414954689835130026859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15756553272919780173369145 11817414954689835130026859)
    ·
      refine ⟨17726122432034752695040289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11817414954689835130026859 17726122432034752695040289)
      ·
        refine ⟨13294591824026064521280217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17726122432034752695040289 13294591824026064521280217)
        ·
          refine ⟨9970943868019548390960163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13294591824026064521280217 9970943868019548390960163)
          ·
            refine ⟨14956415802029322586440245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9970943868019548390960163 14956415802029322586440245)
            ·
              refine ⟨1402163981440248992478773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14956415802029322586440245 1402163981440248992478773)
              ·
                refine ⟨131452873260023343044885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1402163981440248992478773 131452873260023343044885)
                ·
                  rfl

theorem cell20_864012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_864012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864012 prefixEnd_864012 := by exact prefixLift 864012
  have htrace : WordTrace (prefixWord ++ tailWord_864012) baseStart_864012 baseEnd_864012 := by
    simpa [prefixWord, tailWord_864012, baseEnd_864012] using wordTrace_append hprefix tailTrace_864012
  have hstable : (prefixWord ++ tailWord_864012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864012).length < 2 ^ (prefixWord ++ tailWord_864012).sum := by decide
  have hdescent : baseEnd_864012 < baseStart_864012 := by decide
  rcases family_descends (prefixWord ++ tailWord_864012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864050 : List Nat := [3, 2, 1, 1, 3, 3, 7]
def baseStart_864050 : Nat := 118140960795 + 864050 * 2 ^ 59
def prefixEnd_864050 : Nat := 4983230072969 + 3 ^ 40 * 864050 * 2
def baseEnd_864050 : Nat := 43819551557278976207537

theorem tailTrace_864050 : CollatzResearch.WordTrace tailWord_864050 prefixEnd_864050 43819551557278976207537 := by
  unfold tailWord_864050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878623129925473209155401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21009661679801261891081069 7878623129925473209155401)
  ·
    refine ⟨5908967347444104906866551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7878623129925473209155401 5908967347444104906866551)
    ·
      refine ⟨8863451021166157360299827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5908967347444104906866551 8863451021166157360299827)
      ·
        refine ⟨13295176531749236040449741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863451021166157360299827 13295176531749236040449741)
        ·
          refine ⟨4985691199405963515168653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13295176531749236040449741 4985691199405963515168653)
          ·
            refine ⟨1869634199777236318188245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4985691199405963515168653 1869634199777236318188245)
            ·
              refine ⟨43819551557278976207537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1869634199777236318188245 43819551557278976207537)
              ·
                rfl

theorem cell20_864050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 7].length) (baseStart_864050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864050 prefixEnd_864050 := by exact prefixLift 864050
  have htrace : WordTrace (prefixWord ++ tailWord_864050) baseStart_864050 baseEnd_864050 := by
    simpa [prefixWord, tailWord_864050, baseEnd_864050] using wordTrace_append hprefix tailTrace_864050
  have hstable : (prefixWord ++ tailWord_864050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864050).length < 2 ^ (prefixWord ++ tailWord_864050).sum := by decide
  have hdescent : baseEnd_864050 < baseStart_864050 := by decide
  rcases family_descends (prefixWord ++ tailWord_864050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864060 : List Nat := [2, 2, 2, 2, 1, 1, 4, 4, 2]
def baseStart_864060 : Nat := 118140960795 + 864060 * 2 ^ 59
def prefixEnd_864060 : Nat := 4983230072969 + 3 ^ 40 * 864060 * 2
def baseEnd_864060 : Nat := 394380528287995195534459

theorem tailTrace_864060 : CollatzResearch.WordTrace tailWord_864060 prefixEnd_864060 394380528287995195534459 := by
  unfold tailWord_864060
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757428624832832272242817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21009904833110443029657089 15757428624832832272242817)
  ·
    refine ⟨11818071468624624204182113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15757428624832832272242817 11818071468624624204182113)
    ·
      refine ⟨8863553601468468153136585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11818071468624624204182113 8863553601468468153136585)
      ·
        refine ⟨6647665201101351114852439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8863553601468468153136585 6647665201101351114852439)
        ·
          refine ⟨9971497801652026672278659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6647665201101351114852439 9971497801652026672278659)
          ·
            refine ⟨14957246702478040008417989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9971497801652026672278659 14957246702478040008417989)
            ·
              refine ⟨2804483756714632501578373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14957246702478040008417989 2804483756714632501578373)
              ·
                refine ⟨525840704383993594045945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2804483756714632501578373 525840704383993594045945)
                ·
                  refine ⟨394380528287995195534459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 525840704383993594045945 394380528287995195534459)
                  ·
                    rfl

theorem cell20_864060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 4, 2].length) (baseStart_864060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864060 prefixEnd_864060 := by exact prefixLift 864060
  have htrace : WordTrace (prefixWord ++ tailWord_864060) baseStart_864060 baseEnd_864060 := by
    simpa [prefixWord, tailWord_864060, baseEnd_864060] using wordTrace_append hprefix tailTrace_864060
  have hstable : (prefixWord ++ tailWord_864060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864060).length < 2 ^ (prefixWord ++ tailWord_864060).sum := by decide
  have hdescent : baseEnd_864060 < baseStart_864060 := by decide
  rcases family_descends (prefixWord ++ tailWord_864060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864081 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 4]
def baseStart_864081 : Nat := 118140960795 + 864081 * 2 ^ 59
def prefixEnd_864081 : Nat := 4983230072969 + 3 ^ 40 * 864081 * 2
def baseEnd_864081 : Nat := 394390113260212455834373

theorem tailTrace_864081 : CollatzResearch.WordTrace tailWord_864081 prefixEnd_864081 394390113260212455834373 := by
  unfold tailWord_864081
  simp only [CollatzResearch.WordTrace]
  refine ⟨31515623182589585131000097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21010415455059723420666731 31515623182589585131000097)
  ·
    refine ⟨23636717386942188848250073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31515623182589585131000097 23636717386942188848250073)
    ·
      refine ⟨17727538040206641636187555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23636717386942188848250073 17727538040206641636187555)
      ·
        refine ⟨26591307060309962454281333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17727538040206641636187555 26591307060309962454281333)
        ·
          refine ⟨2492935036904058980088875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26591307060309962454281333 2492935036904058980088875)
          ·
            refine ⟨3739402555356088470133313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2492935036904058980088875 3739402555356088470133313)
            ·
              refine ⟨2804551916517066352599985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3739402555356088470133313 2804551916517066352599985)
              ·
                refine ⟨2103413937387799764449989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2804551916517066352599985 2103413937387799764449989)
                ·
                  refine ⟨394390113260212455834373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2103413937387799764449989 394390113260212455834373)
                  ·
                    rfl

theorem cell20_864081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_864081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864081 prefixEnd_864081 := by exact prefixLift 864081
  have htrace : WordTrace (prefixWord ++ tailWord_864081) baseStart_864081 baseEnd_864081 := by
    simpa [prefixWord, tailWord_864081, baseEnd_864081] using wordTrace_append hprefix tailTrace_864081
  have hstable : (prefixWord ++ tailWord_864081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864081).length < 2 ^ (prefixWord ++ tailWord_864081).sum := by decide
  have hdescent : baseEnd_864081 < baseStart_864081 := by decide
  rcases family_descends (prefixWord ++ tailWord_864081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864084 : List Nat := [2, 4, 1, 1, 3, 3, 2, 4]
def baseStart_864084 : Nat := 118140960795 + 864084 * 2 ^ 59
def prefixEnd_864084 : Nat := 4983230072969 + 3 ^ 40 * 864084 * 2
def baseEnd_864084 : Nat := 131463827513985926244787

theorem tailTrace_864084 : CollatzResearch.WordTrace tailWord_864084 prefixEnd_864084 131463827513985926244787 := by
  unfold tailWord_864084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15757866300789358321679653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21010488401052477762239537 15757866300789358321679653)
  ·
    refine ⟨2954599931398004685314935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15757866300789358321679653 2954599931398004685314935)
    ·
      refine ⟨4431899897097007027972403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2954599931398004685314935 4431899897097007027972403)
      ·
        refine ⟨6647849845645510541958605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4431899897097007027972403 6647849845645510541958605)
        ·
          refine ⟨2492943692117066453234477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6647849845645510541958605 2492943692117066453234477)
          ·
            refine ⟨934853884543899919962929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2492943692117066453234477 934853884543899919962929)
            ·
              refine ⟨701140413407924939972197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 934853884543899919962929 701140413407924939972197)
              ·
                refine ⟨131463827513985926244787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701140413407924939972197 131463827513985926244787)
                ·
                  rfl

theorem cell20_864084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_864084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864084 prefixEnd_864084 := by exact prefixLift 864084
  have htrace : WordTrace (prefixWord ++ tailWord_864084) baseStart_864084 baseEnd_864084 := by
    simpa [prefixWord, tailWord_864084, baseEnd_864084] using wordTrace_append hprefix tailTrace_864084
  have hstable : (prefixWord ++ tailWord_864084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864084).length < 2 ^ (prefixWord ++ tailWord_864084).sum := by decide
  have hdescent : baseEnd_864084 < baseStart_864084 := by decide
  rcases family_descends (prefixWord ++ tailWord_864084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864095 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 5]
def baseStart_864095 : Nat := 118140960795 + 864095 * 2 ^ 59
def prefixEnd_864095 : Nat := 4983230072969 + 3 ^ 40 * 864095 * 2
def baseEnd_864095 : Nat := 394396503241690629367649

theorem tailTrace_864095 : CollatzResearch.WordTrace tailWord_864095 prefixEnd_864095 394396503241690629367649 := by
  unfold tailWord_864095
  simp only [CollatzResearch.WordTrace]
  refine ⟨31516133804538865522009739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21010755869692577014673159 31516133804538865522009739)
  ·
    refine ⟨47274200706808298283014609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31516133804538865522009739 47274200706808298283014609)
    ·
      refine ⟨35455650530106223712260957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47274200706808298283014609 35455650530106223712260957)
      ·
        refine ⟨13295868948789833892097859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35455650530106223712260957 13295868948789833892097859)
        ·
          refine ⟨19943803423184750838146789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295868948789833892097859 19943803423184750838146789)
          ·
            refine ⟨3739463141847140782152523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19943803423184750838146789 3739463141847140782152523)
            ·
              refine ⟨5609194712770711173228785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3739463141847140782152523 5609194712770711173228785)
              ·
                refine ⟨4206896034578033379921589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5609194712770711173228785 4206896034578033379921589)
                ·
                  refine ⟨394396503241690629367649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4206896034578033379921589 394396503241690629367649)
                  ·
                    rfl

theorem cell20_864095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_864095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864095 prefixEnd_864095 := by exact prefixLift 864095
  have htrace : WordTrace (prefixWord ++ tailWord_864095) baseStart_864095 baseEnd_864095 := by
    simpa [prefixWord, tailWord_864095, baseEnd_864095] using wordTrace_append hprefix tailTrace_864095
  have hstable : (prefixWord ++ tailWord_864095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864095).length < 2 ^ (prefixWord ++ tailWord_864095).sum := by decide
  have hdescent : baseEnd_864095 < baseStart_864095 := by decide
  rcases family_descends (prefixWord ++ tailWord_864095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864140 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 6]
def baseStart_864140 : Nat := 118140960795 + 864140 * 2 ^ 59
def prefixEnd_864140 : Nat := 4983230072969 + 3 ^ 40 * 864140 * 2
def baseEnd_864140 : Nat := 394417042467870472867465

theorem tailTrace_864140 : CollatzResearch.WordTrace tailWord_864140 prefixEnd_864140 394417042467870472867465 := by
  unfold tailWord_864140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15758887544687919103698937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21011850059583892138265249 15758887544687919103698937)
  ·
    refine ⟨11819165658515939327774203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15758887544687919103698937 11819165658515939327774203)
    ·
      refine ⟨17728748487773908991661305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11819165658515939327774203 17728748487773908991661305)
      ·
        refine ⟨13296561365830431743745979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17728748487773908991661305 13296561365830431743745979)
        ·
          refine ⟨19944842048745647615618969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13296561365830431743745979 19944842048745647615618969)
          ·
            refine ⟨14958631536559235711714227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19944842048745647615618969 14958631536559235711714227)
            ·
              refine ⟨22437947304838853567571341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14958631536559235711714227 22437947304838853567571341)
              ·
                refine ⟨8414230239314570087839253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22437947304838853567571341 8414230239314570087839253)
                ·
                  refine ⟨394417042467870472867465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8414230239314570087839253 394417042467870472867465)
                  ·
                    rfl

theorem cell20_864140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 6].length) (baseStart_864140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864140 prefixEnd_864140 := by exact prefixLift 864140
  have htrace : WordTrace (prefixWord ++ tailWord_864140) baseStart_864140 baseEnd_864140 := by
    simpa [prefixWord, tailWord_864140, baseEnd_864140] using wordTrace_append hprefix tailTrace_864140
  have hstable : (prefixWord ++ tailWord_864140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864140).length < 2 ^ (prefixWord ++ tailWord_864140).sum := by decide
  have hdescent : baseEnd_864140 < baseStart_864140 := by decide
  rcases family_descends (prefixWord ++ tailWord_864140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864167 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 3]
def baseStart_864167 : Nat := 118140960795 + 864167 * 2 ^ 59
def prefixEnd_864167 : Nat := 4983230072969 + 3 ^ 40 * 864167 * 2
def baseEnd_864167 : Nat := 394429366003578378967355

theorem tailTrace_864167 : CollatzResearch.WordTrace tailWord_864167 prefixEnd_864167 394429366003578378967355 := by
  unfold tailWord_864167
  simp only [CollatzResearch.WordTrace]
  refine ⟨31518759860278021818630755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21012506573518681212420503 31518759860278021818630755)
  ·
    refine ⟨47278139790417032727946133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31518759860278021818630755 47278139790417032727946133)
    ·
      refine ⟨2216162802675798409122475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47278139790417032727946133 2216162802675798409122475)
      ·
        refine ⟨3324244204013697613683713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216162802675798409122475 3324244204013697613683713)
        ·
          refine ⟨2493183153010273210262785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324244204013697613683713 2493183153010273210262785)
          ·
            refine ⟨1869887364757704907697089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493183153010273210262785 1869887364757704907697089)
            ·
              refine ⟨1402415523568278680772817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1869887364757704907697089 1402415523568278680772817)
              ·
                refine ⟨1051811642676209010579613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1402415523568278680772817 1051811642676209010579613)
                ·
                  refine ⟨394429366003578378967355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051811642676209010579613 394429366003578378967355)
                  ·
                    rfl

theorem cell20_864167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_864167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864167 prefixEnd_864167 := by exact prefixLift 864167
  have htrace : WordTrace (prefixWord ++ tailWord_864167) baseStart_864167 baseEnd_864167 := by
    simpa [prefixWord, tailWord_864167, baseEnd_864167] using wordTrace_append hprefix tailTrace_864167
  have hstable : (prefixWord ++ tailWord_864167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864167).length < 2 ^ (prefixWord ++ tailWord_864167).sum := by decide
  have hdescent : baseEnd_864167 < baseStart_864167 := by decide
  rcases family_descends (prefixWord ++ tailWord_864167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864178 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_864178 : Nat := 118140960795 + 864178 * 2 ^ 59
def prefixEnd_864178 : Nat := 4983230072969 + 3 ^ 40 * 864178 * 2
def baseEnd_864178 : Nat := 394434386703311229600643

theorem tailTrace_864178 : CollatzResearch.WordTrace tailWord_864178 prefixEnd_864178 394434386703311229600643 := by
  unfold tailWord_864178
  simp only [CollatzResearch.WordTrace]
  refine ⟨7879790265809542674320297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21012774042158780464854125 7879790265809542674320297)
  ·
    refine ⟨5909842699357157005740223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7879790265809542674320297 5909842699357157005740223)
    ·
      refine ⟨8864764049035735508610335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5909842699357157005740223 8864764049035735508610335)
      ·
        refine ⟨13297146073553603262915503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8864764049035735508610335 13297146073553603262915503)
        ·
          refine ⟨19945719110330404894373255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13297146073553603262915503 19945719110330404894373255)
          ·
            refine ⟨29918578665495607341559883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19945719110330404894373255 29918578665495607341559883)
            ·
              refine ⟨44877867998243411012339825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29918578665495607341559883 44877867998243411012339825)
              ·
                refine ⟨33658400998682558259254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44877867998243411012339825 33658400998682558259254869)
                ·
                  refine ⟨394434386703311229600643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33658400998682558259254869 394434386703311229600643)
                  ·
                    rfl

theorem cell20_864178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_864178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864178 prefixEnd_864178 := by exact prefixLift 864178
  have htrace : WordTrace (prefixWord ++ tailWord_864178) baseStart_864178 baseEnd_864178 := by
    simpa [prefixWord, tailWord_864178, baseEnd_864178] using wordTrace_append hprefix tailTrace_864178
  have hstable : (prefixWord ++ tailWord_864178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864178).length < 2 ^ (prefixWord ++ tailWord_864178).sum := by decide
  have hdescent : baseEnd_864178 < baseStart_864178 := by decide
  rcases family_descends (prefixWord ++ tailWord_864178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864181 : List Nat := [1, 3, 3, 2, 1, 4, 1, 5]
def baseStart_864181 : Nat := 118140960795 + 864181 * 2 ^ 59
def prefixEnd_864181 : Nat := 4983230072969 + 3 ^ 40 * 864181 * 2
def baseEnd_864181 : Nat := 131478585328352184166877

theorem tailTrace_864181 : CollatzResearch.WordTrace tailWord_864181 prefixEnd_864181 131478585328352184166877 := by
  unfold tailWord_864181
  simp only [CollatzResearch.WordTrace]
  refine ⟨31519270482227302209640397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21012846988151534806426931 31519270482227302209640397)
  ·
    refine ⟨11819726430835238328615149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31519270482227302209640397 11819726430835238328615149)
    ·
      refine ⟨4432397411563214373230681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11819726430835238328615149 4432397411563214373230681)
      ·
        refine ⟨3324298058672410779923011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4432397411563214373230681 3324298058672410779923011)
        ·
          refine ⟨4986447088008616169884517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3324298058672410779923011 4986447088008616169884517)
          ·
            refine ⟨934958829001615531853347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4986447088008616169884517 934958829001615531853347)
            ·
              refine ⟨1402438243502423297780021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 934958829001615531853347 1402438243502423297780021)
              ·
                refine ⟨131478585328352184166877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1402438243502423297780021 131478585328352184166877)
                ·
                  rfl

theorem cell20_864181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 5].length) (baseStart_864181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864181 prefixEnd_864181 := by exact prefixLift 864181
  have htrace : WordTrace (prefixWord ++ tailWord_864181) baseStart_864181 baseEnd_864181 := by
    simpa [prefixWord, tailWord_864181, baseEnd_864181] using wordTrace_append hprefix tailTrace_864181
  have hstable : (prefixWord ++ tailWord_864181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864181).length < 2 ^ (prefixWord ++ tailWord_864181).sum := by decide
  have hdescent : baseEnd_864181 < baseStart_864181 := by decide
  rcases family_descends (prefixWord ++ tailWord_864181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864216 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 6]
def baseStart_864216 : Nat := 118140960795 + 864216 * 2 ^ 59
def prefixEnd_864216 : Nat := 4983230072969 + 3 ^ 40 * 864216 * 2
def baseEnd_864216 : Nat := 394451730938751986333821

theorem tailTrace_864216 : CollatzResearch.WordTrace tailWord_864216 prefixEnd_864216 394451730938751986333821 := by
  unfold tailWord_864216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15760273518550251593582251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21013698024733668791443001 15760273518550251593582251)
  ·
    refine ⟨23640410277825377390373377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15760273518550251593582251 23640410277825377390373377)
    ·
      refine ⟨17730307708369033042780033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23640410277825377390373377 17730307708369033042780033)
      ·
        refine ⟨13297730781276774782085025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17730307708369033042780033 13297730781276774782085025)
        ·
          refine ⟨9973298085957581086563769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13297730781276774782085025 9973298085957581086563769)
          ·
            refine ⟨7479973564468185814922827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9973298085957581086563769 7479973564468185814922827)
            ·
              refine ⟨11219960346702278722384241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7479973564468185814922827 11219960346702278722384241)
              ·
                refine ⟨8414970260026709041788181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11219960346702278722384241 8414970260026709041788181)
                ·
                  refine ⟨394451730938751986333821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8414970260026709041788181 394451730938751986333821)
                  ·
                    rfl

theorem cell20_864216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_864216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864216 prefixEnd_864216 := by exact prefixLift 864216
  have htrace : WordTrace (prefixWord ++ tailWord_864216) baseStart_864216 baseEnd_864216 := by
    simpa [prefixWord, tailWord_864216, baseEnd_864216] using wordTrace_append hprefix tailTrace_864216
  have hstable : (prefixWord ++ tailWord_864216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864216).length < 2 ^ (prefixWord ++ tailWord_864216).sum := by decide
  have hdescent : baseEnd_864216 < baseStart_864216 := by decide
  rcases family_descends (prefixWord ++ tailWord_864216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864298 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 3]
def baseStart_864298 : Nat := 118140960795 + 864298 * 2 ^ 59
def prefixEnd_864298 : Nat := 4983230072969 + 3 ^ 40 * 864298 * 2
def baseEnd_864298 : Nat := 394489157973124145600153

theorem tailTrace_864298 : CollatzResearch.WordTrace tailWord_864298 prefixEnd_864298 394489157973124145600153 := by
  unfold tailWord_864298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7880884455700857797912387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21015691881868954127766365 7880884455700857797912387)
  ·
    refine ⟨11821326683551286696868581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7880884455700857797912387 11821326683551286696868581)
    ·
      refine ⟨2216498753165866255662859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11821326683551286696868581 2216498753165866255662859)
      ·
        refine ⟨3324748129748799383494289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216498753165866255662859 3324748129748799383494289)
        ·
          refine ⟨2493561097311599537620717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3324748129748799383494289 2493561097311599537620717)
          ·
            refine ⟨935085411491849826607769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2493561097311599537620717 935085411491849826607769)
            ·
              refine ⟨701314058618887369955827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935085411491849826607769 701314058618887369955827)
              ·
                refine ⟨1051971087928331054933741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701314058618887369955827 1051971087928331054933741)
                ·
                  refine ⟨394489157973124145600153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1051971087928331054933741 394489157973124145600153)
                  ·
                    rfl

theorem cell20_864298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_864298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864298 prefixEnd_864298 := by exact prefixLift 864298
  have htrace : WordTrace (prefixWord ++ tailWord_864298) baseStart_864298 baseEnd_864298 := by
    simpa [prefixWord, tailWord_864298, baseEnd_864298] using wordTrace_append hprefix tailTrace_864298
  have hstable : (prefixWord ++ tailWord_864298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864298).length < 2 ^ (prefixWord ++ tailWord_864298).sum := by decide
  have hdescent : baseEnd_864298 < baseStart_864298 := by decide
  rcases family_descends (prefixWord ++ tailWord_864298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864361 : List Nat := [1, 2, 1, 1, 1, 5, 1, 5, 3]
def baseStart_864361 : Nat := 118140960795 + 864361 * 2 ^ 59
def prefixEnd_864361 : Nat := 4983230072969 + 3 ^ 40 * 864361 * 2
def baseEnd_864361 : Nat := 394517912889775926499895

theorem tailTrace_864361 : CollatzResearch.WordTrace tailWord_864361 prefixEnd_864361 394517912889775926499895 := by
  unfold tailWord_864361
  simp only [CollatzResearch.WordTrace]
  refine ⟨31525835621575192951192937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21017223747716795300795291 31525835621575192951192937)
  ·
    refine ⟨23644376716181394713394703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31525835621575192951192937 23644376716181394713394703)
    ·
      refine ⟨35466565074272092070092055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23644376716181394713394703 35466565074272092070092055)
      ·
        refine ⟨53199847611408138105138083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35466565074272092070092055 53199847611408138105138083)
        ·
          refine ⟨79799771417112207157707125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53199847611408138105138083 79799771417112207157707125)
          ·
            refine ⟨7481228570354269421035043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79799771417112207157707125 7481228570354269421035043)
            ·
              refine ⟨11221842855531404131552565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481228570354269421035043 11221842855531404131552565)
              ·
                refine ⟨1052047767706069137333053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11221842855531404131552565 1052047767706069137333053)
                ·
                  refine ⟨394517912889775926499895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052047767706069137333053 394517912889775926499895)
                  ·
                    rfl

theorem cell20_864361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_864361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864361 prefixEnd_864361 := by exact prefixLift 864361
  have htrace : WordTrace (prefixWord ++ tailWord_864361) baseStart_864361 baseEnd_864361 := by
    simpa [prefixWord, tailWord_864361, baseEnd_864361] using wordTrace_append hprefix tailTrace_864361
  have hstable : (prefixWord ++ tailWord_864361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864361).length < 2 ^ (prefixWord ++ tailWord_864361).sum := by decide
  have hdescent : baseEnd_864361 < baseStart_864361 := by decide
  rcases family_descends (prefixWord ++ tailWord_864361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864368 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 6]
def baseStart_864368 : Nat := 118140960795 + 864368 * 2 ^ 59
def prefixEnd_864368 : Nat := 4983230072969 + 3 ^ 40 * 864368 * 2
def baseEnd_864368 : Nat := 394521107880515013266533

theorem tailTrace_864368 : CollatzResearch.WordTrace tailWord_864368 prefixEnd_864368 394521107880515013266533 := by
  unfold tailWord_864368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763045466274916573348879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21017393955033222097798505 15763045466274916573348879)
  ·
    refine ⟨23644568199412374860023319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15763045466274916573348879 23644568199412374860023319)
    ·
      refine ⟨35466852299118562290034979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23644568199412374860023319 35466852299118562290034979)
      ·
        refine ⟨53200278448677843435052469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35466852299118562290034979 53200278448677843435052469)
        ·
          refine ⟨4987526104563547822036169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53200278448677843435052469 4987526104563547822036169)
          ·
            refine ⟨3740644578422660866527127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4987526104563547822036169 3740644578422660866527127)
            ·
              refine ⟨5610966867633991299790691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3740644578422660866527127 5610966867633991299790691)
              ·
                refine ⟨8416450301450986949686037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5610966867633991299790691 8416450301450986949686037)
                ·
                  refine ⟨394521107880515013266533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8416450301450986949686037 394521107880515013266533)
                  ·
                    rfl

theorem cell20_864368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 6].length) (baseStart_864368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864368 prefixEnd_864368 := by exact prefixLift 864368
  have htrace : WordTrace (prefixWord ++ tailWord_864368) baseStart_864368 baseEnd_864368 := by
    simpa [prefixWord, tailWord_864368, baseEnd_864368] using wordTrace_append hprefix tailTrace_864368
  have hstable : (prefixWord ++ tailWord_864368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864368).length < 2 ^ (prefixWord ++ tailWord_864368).sum := by decide
  have hdescent : baseEnd_864368 < baseStart_864368 := by decide
  rcases family_descends (prefixWord ++ tailWord_864368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864392 : List Nat := [2, 1, 3, 4, 1, 2, 7]
def baseStart_864392 : Nat := 118140960795 + 864392 * 2 ^ 59
def prefixEnd_864392 : Nat := 4983230072969 + 3 ^ 40 * 864392 * 2
def baseEnd_864392 : Nat := 43836895792719732940715

theorem tailTrace_864392 : CollatzResearch.WordTrace tailWord_864392 prefixEnd_864392 43836895792719732940715 := by
  unfold tailWord_864392
  simp only [CollatzResearch.WordTrace]
  refine ⟨15763483142231442622785715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21017977522975256830380953 15763483142231442622785715)
  ·
    refine ⟨23645224713347163934178573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15763483142231442622785715 23645224713347163934178573)
    ·
      refine ⟨8866959267505186475316965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23645224713347163934178573 8866959267505186475316965)
      ·
        refine ⟨1662554862657222464121931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8866959267505186475316965 1662554862657222464121931)
        ·
          refine ⟨2493832293985833696182897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662554862657222464121931 2493832293985833696182897)
          ·
            refine ⟨1870374220489375272137173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2493832293985833696182897 1870374220489375272137173)
            ·
              refine ⟨43836895792719732940715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1870374220489375272137173 43836895792719732940715)
              ·
                rfl

theorem cell20_864392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 7].length) (baseStart_864392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864392 prefixEnd_864392 := by exact prefixLift 864392
  have htrace : WordTrace (prefixWord ++ tailWord_864392) baseStart_864392 baseEnd_864392 := by
    simpa [prefixWord, tailWord_864392, baseEnd_864392] using wordTrace_append hprefix tailTrace_864392
  have hstable : (prefixWord ++ tailWord_864392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864392).length < 2 ^ (prefixWord ++ tailWord_864392).sum := by decide
  have hdescent : baseEnd_864392 < baseStart_864392 := by decide
  rcases family_descends (prefixWord ++ tailWord_864392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864402 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_864402 : Nat := 118140960795 + 864402 * 2 ^ 59
def prefixEnd_864402 : Nat := 4983230072969 + 3 ^ 40 * 864402 * 2
def baseEnd_864402 : Nat := 394536626406962006133061

theorem tailTrace_864402 : CollatzResearch.WordTrace tailWord_864402 prefixEnd_864402 394536626406962006133061 := by
  unfold tailWord_864402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7881832753606664238358865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21018220676284437968956973 7881832753606664238358865)
  ·
    refine ⟨5911374565204998178769149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7881832753606664238358865 5911374565204998178769149)
    ·
      refine ⟨2216765461951874317038431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5911374565204998178769149 2216765461951874317038431)
      ·
        refine ⟨3325148192927811475557647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2216765461951874317038431 3325148192927811475557647)
        ·
          refine ⟨4987722289391717213336471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3325148192927811475557647 4987722289391717213336471)
          ·
            refine ⟨7481583434087575820004707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4987722289391717213336471 7481583434087575820004707)
            ·
              refine ⟨11222375151131363730007061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7481583434087575820004707 11222375151131363730007061)
              ·
                refine ⟨526048835209282674844081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11222375151131363730007061 526048835209282674844081)
                ·
                  refine ⟨394536626406962006133061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526048835209282674844081 394536626406962006133061)
                  ·
                    rfl

theorem cell20_864402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_864402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864402 prefixEnd_864402 := by exact prefixLift 864402
  have htrace : WordTrace (prefixWord ++ tailWord_864402) baseStart_864402 baseEnd_864402 := by
    simpa [prefixWord, tailWord_864402, baseEnd_864402] using wordTrace_append hprefix tailTrace_864402
  have hstable : (prefixWord ++ tailWord_864402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864402).length < 2 ^ (prefixWord ++ tailWord_864402).sum := by decide
  have hdescent : baseEnd_864402 < baseStart_864402 := by decide
  rcases family_descends (prefixWord ++ tailWord_864402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864496 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 7]
def baseStart_864496 : Nat := 118140960795 + 864496 * 2 ^ 59
def prefixEnd_864496 : Nat := 4983230072969 + 3 ^ 40 * 864496 * 2
def baseEnd_864496 : Nat := 394579530568315456999343

theorem tailTrace_864496 : CollatzResearch.WordTrace tailWord_864496 prefixEnd_864496 394579530568315456999343 := by
  unfold tailWord_864496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15765379738043055503678671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21020506317390740671571561 15765379738043055503678671)
  ·
    refine ⟨23648069607064583255518007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15765379738043055503678671 23648069607064583255518007)
    ·
      refine ⟨35472104410596874883277011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23648069607064583255518007 35472104410596874883277011)
      ·
        refine ⟨53208156615895312324915517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35472104410596874883277011 53208156615895312324915517)
        ·
          refine ⟨19953058730960742121843319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53208156615895312324915517 19953058730960742121843319)
          ·
            refine ⟨29929588096441113182764979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19953058730960742121843319 29929588096441113182764979)
            ·
              refine ⟨44894382144661669774147469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29929588096441113182764979 44894382144661669774147469)
              ·
                refine ⟨16835393304248126165305301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44894382144661669774147469 16835393304248126165305301)
                ·
                  refine ⟨394579530568315456999343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16835393304248126165305301 394579530568315456999343)
                  ·
                    rfl

theorem cell20_864496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_864496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864496 prefixEnd_864496 := by exact prefixLift 864496
  have htrace : WordTrace (prefixWord ++ tailWord_864496) baseStart_864496 baseEnd_864496 := by
    simpa [prefixWord, tailWord_864496, baseEnd_864496] using wordTrace_append hprefix tailTrace_864496
  have hstable : (prefixWord ++ tailWord_864496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864496).length < 2 ^ (prefixWord ++ tailWord_864496).sum := by decide
  have hdescent : baseEnd_864496 < baseStart_864496 := by decide
  rcases family_descends (prefixWord ++ tailWord_864496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864499 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 2]
def baseStart_864499 : Nat := 118140960795 + 864499 * 2 ^ 59
def prefixEnd_864499 : Nat := 4983230072969 + 3 ^ 40 * 864499 * 2
def baseEnd_864499 : Nat := 394580899850060779899331

theorem tailTrace_864499 : CollatzResearch.WordTrace tailWord_864499 prefixEnd_864499 394580899850060779899331 := by
  unfold tailWord_864499
  simp only [CollatzResearch.WordTrace]
  refine ⟨31530868895075242519716551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21020579263383495013144367 31530868895075242519716551)
  ·
    refine ⟨47296303342612863779574827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31530868895075242519716551 47296303342612863779574827)
    ·
      refine ⟨70944455013919295669362241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47296303342612863779574827 70944455013919295669362241)
      ·
        refine ⟨53208341260439471752021681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70944455013919295669362241 53208341260439471752021681)
        ·
          refine ⟨39906255945329603814016261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53208341260439471752021681 39906255945329603814016261)
          ·
            refine ⟨7482422989749300715128049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39906255945329603814016261 7482422989749300715128049)
            ·
              refine ⟨5611817242311975536346037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7482422989749300715128049 5611817242311975536346037)
              ·
                refine ⟨526107866466747706532441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5611817242311975536346037 526107866466747706532441)
                ·
                  refine ⟨394580899850060779899331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526107866466747706532441 394580899850060779899331)
                  ·
                    rfl

theorem cell20_864499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 2].length) (baseStart_864499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864499 prefixEnd_864499 := by exact prefixLift 864499
  have htrace : WordTrace (prefixWord ++ tailWord_864499) baseStart_864499 baseEnd_864499 := by
    simpa [prefixWord, tailWord_864499, baseEnd_864499] using wordTrace_append hprefix tailTrace_864499
  have hstable : (prefixWord ++ tailWord_864499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864499).length < 2 ^ (prefixWord ++ tailWord_864499).sum := by decide
  have hdescent : baseEnd_864499 < baseStart_864499 := by decide
  rcases family_descends (prefixWord ++ tailWord_864499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864565 : List Nat := [1, 3, 3, 1, 2, 1, 9]
def baseStart_864565 : Nat := 118140960795 + 864565 * 2 ^ 59
def prefixEnd_864565 : Nat := 4983230072969 + 3 ^ 40 * 864565 * 2
def baseEnd_864565 : Nat := 43845669338717542633229

theorem tailTrace_864565 : CollatzResearch.WordTrace tailWord_864565 prefixEnd_864565 43845669338717542633229 := by
  unfold tailWord_864565
  simp only [CollatzResearch.WordTrace]
  refine ⟨31533276112836135791619149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21022184075224090527746099 31533276112836135791619149)
  ·
    refine ⟨11824978542313550921857181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31533276112836135791619149 11824978542313550921857181)
    ·
      refine ⟨4434366953367581595696443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11824978542313550921857181 4434366953367581595696443)
      ·
        refine ⟨6651550430051372393544665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4434366953367581595696443 6651550430051372393544665)
        ·
          refine ⟨4988662822538529295158499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6651550430051372393544665 4988662822538529295158499)
          ·
            refine ⟨7482994233807793942737749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988662822538529295158499 7482994233807793942737749)
            ·
              refine ⟨43845669338717542633229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7482994233807793942737749 43845669338717542633229)
              ·
                rfl

theorem cell20_864565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 9].length) (baseStart_864565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864565 prefixEnd_864565 := by exact prefixLift 864565
  have htrace : WordTrace (prefixWord ++ tailWord_864565) baseStart_864565 baseEnd_864565 := by
    simpa [prefixWord, tailWord_864565, baseEnd_864565] using wordTrace_append hprefix tailTrace_864565
  have hstable : (prefixWord ++ tailWord_864565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864565).length < 2 ^ (prefixWord ++ tailWord_864565).sum := by decide
  have hdescent : baseEnd_864565 < baseStart_864565 := by decide
  rcases family_descends (prefixWord ++ tailWord_864565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864575 : List Nat := [1, 1, 2, 2, 4, 1, 1, 6, 2]
def baseStart_864575 : Nat := 118140960795 + 864575 * 2 ^ 59
def prefixEnd_864575 : Nat := 4983230072969 + 3 ^ 40 * 864575 * 2
def baseEnd_864575 : Nat := 394615588320942293365687

theorem tailTrace_864575 : CollatzResearch.WordTrace tailWord_864575 prefixEnd_864575 394615588320942293365687 := by
  unfold tailWord_864575
  simp only [CollatzResearch.WordTrace]
  refine ⟨31533640842799907499483179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21022427228533271666322119 31533640842799907499483179)
  ·
    refine ⟨47300461264199861249224769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31533640842799907499483179 47300461264199861249224769)
    ·
      refine ⟨35475345948149895936918577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47300461264199861249224769 35475345948149895936918577)
      ·
        refine ⟨26606509461112421952688933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35475345948149895936918577 26606509461112421952688933)
        ·
          refine ⟨4988720523958579116129175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26606509461112421952688933 4988720523958579116129175)
          ·
            refine ⟨7483080785937868674193763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4988720523958579116129175 7483080785937868674193763)
            ·
              refine ⟨11224621178906803011290645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7483080785937868674193763 11224621178906803011290645)
              ·
                refine ⟨526154117761256391154249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11224621178906803011290645 526154117761256391154249)
                ·
                  refine ⟨394615588320942293365687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526154117761256391154249 394615588320942293365687)
                  ·
                    rfl

theorem cell20_864575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 6, 2].length) (baseStart_864575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864575 prefixEnd_864575 := by exact prefixLift 864575
  have htrace : WordTrace (prefixWord ++ tailWord_864575) baseStart_864575 baseEnd_864575 := by
    simpa [prefixWord, tailWord_864575, baseEnd_864575] using wordTrace_append hprefix tailTrace_864575
  have hstable : (prefixWord ++ tailWord_864575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864575).length < 2 ^ (prefixWord ++ tailWord_864575).sum := by decide
  have hdescent : baseEnd_864575 < baseStart_864575 := by decide
  rcases family_descends (prefixWord ++ tailWord_864575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864620 : List Nat := [2, 2, 1, 1, 6, 2, 6]
def baseStart_864620 : Nat := 118140960795 + 864620 * 2 ^ 59
def prefixEnd_864620 : Nat := 4983230072969 + 3 ^ 40 * 864620 * 2
def baseEnd_864620 : Nat := 43848458616346904096167

theorem tailTrace_864620 : CollatzResearch.WordTrace tailWord_864620 prefixEnd_864620 43848458616346904096167 := by
  unfold tailWord_864620
  simp only [CollatzResearch.WordTrace]
  refine ⟨15767641063818440092435657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21023521418424586789914209 15767641063818440092435657)
  ·
    refine ⟨11825730797863830069326743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15767641063818440092435657 11825730797863830069326743)
    ·
      refine ⟨17738596196795745103990115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11825730797863830069326743 17738596196795745103990115)
      ·
        refine ⟨26607894295193617655985173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17738596196795745103990115 26607894295193617655985173)
        ·
          refine ⟨1247245045087200827624305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26607894295193617655985173 1247245045087200827624305)
          ·
            refine ⟨935433783815400620718229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1247245045087200827624305 935433783815400620718229)
            ·
              refine ⟨43848458616346904096167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 935433783815400620718229 43848458616346904096167)
              ·
                rfl

theorem cell20_864620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 6].length) (baseStart_864620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864620 prefixEnd_864620 := by exact prefixLift 864620
  have htrace : WordTrace (prefixWord ++ tailWord_864620) baseStart_864620 baseEnd_864620 := by
    simpa [prefixWord, tailWord_864620, baseEnd_864620] using wordTrace_append hprefix tailTrace_864620
  have hstable : (prefixWord ++ tailWord_864620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864620).length < 2 ^ (prefixWord ++ tailWord_864620).sum := by decide
  have hdescent : baseEnd_864620 < baseStart_864620 := by decide
  rcases family_descends (prefixWord ++ tailWord_864620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864679 : List Nat := [1, 1, 6, 1, 1, 10]
def baseStart_864679 : Nat := 118140960795 + 864679 * 2 ^ 59
def prefixEnd_864679 : Nat := 4983230072969 + 3 ^ 40 * 864679 * 2
def baseEnd_864679 : Nat := 14617150250177042736985

theorem tailTrace_864679 : CollatzResearch.WordTrace tailWord_864679 prefixEnd_864679 14617150250177042736985 := by
  unfold tailWord_864679
  simp only [CollatzResearch.WordTrace]
  refine ⟨31537434034423133261269091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21024956022948755507512727 31537434034423133261269091)
  ·
    refine ⟨47306151051634699891903637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31537434034423133261269091 47306151051634699891903637)
    ·
      refine ⟨2217475830545376557432983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47306151051634699891903637 2217475830545376557432983)
      ·
        refine ⟨3326213745818064836149475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217475830545376557432983 3326213745818064836149475)
        ·
          refine ⟨4989320618727097254224213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326213745818064836149475 4989320618727097254224213)
          ·
            refine ⟨14617150250177042736985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4989320618727097254224213 14617150250177042736985)
            ·
              rfl

theorem cell20_864679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 10].length) (baseStart_864679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864679 prefixEnd_864679 := by exact prefixLift 864679
  have htrace : WordTrace (prefixWord ++ tailWord_864679) baseStart_864679 baseEnd_864679 := by
    simpa [prefixWord, tailWord_864679, baseEnd_864679] using wordTrace_append hprefix tailTrace_864679
  have hstable : (prefixWord ++ tailWord_864679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864679).length < 2 ^ (prefixWord ++ tailWord_864679).sum := by decide
  have hdescent : baseEnd_864679 < baseStart_864679 := by decide
  rcases family_descends (prefixWord ++ tailWord_864679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864685 : List Nat := [1, 5, 2, 2, 2, 1, 1, 4, 2]
def baseStart_864685 : Nat := 118140960795 + 864685 * 2 ^ 59
def prefixEnd_864685 : Nat := 4983230072969 + 3 ^ 40 * 864685 * 2
def baseEnd_864685 : Nat := 394665795318270799698571

theorem tailTrace_864685 : CollatzResearch.WordTrace tailWord_864685 prefixEnd_864685 394665795318270799698571 := by
  unfold tailWord_864685
  simp only [CollatzResearch.WordTrace]
  refine ⟨31537652872401396285987509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21025101914934264190658339 31537652872401396285987509)
  ·
    refine ⟨2956654956787630901811329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31537652872401396285987509 2956654956787630901811329)
    ·
      refine ⟨2217491217590723176358497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2956654956787630901811329 2217491217590723176358497)
      ·
        refine ⟨1663118413193042382268873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2217491217590723176358497 1663118413193042382268873)
        ·
          refine ⟨1247338809894781786701655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1663118413193042382268873 1247338809894781786701655)
          ·
            refine ⟨1871008214842172680052483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247338809894781786701655 1871008214842172680052483)
            ·
              refine ⟨2806512322263259020078725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871008214842172680052483 2806512322263259020078725)
              ·
                refine ⟨526221060424361066264761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2806512322263259020078725 526221060424361066264761)
                ·
                  refine ⟨394665795318270799698571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526221060424361066264761 394665795318270799698571)
                  ·
                    rfl

theorem cell20_864685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_864685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864685 prefixEnd_864685 := by exact prefixLift 864685
  have htrace : WordTrace (prefixWord ++ tailWord_864685) baseStart_864685 baseEnd_864685 := by
    simpa [prefixWord, tailWord_864685, baseEnd_864685] using wordTrace_append hprefix tailTrace_864685
  have hstable : (prefixWord ++ tailWord_864685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864685).length < 2 ^ (prefixWord ++ tailWord_864685).sum := by decide
  have hdescent : baseEnd_864685 < baseStart_864685 := by decide
  rcases family_descends (prefixWord ++ tailWord_864685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864748 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 4]
def baseStart_864748 : Nat := 118140960795 + 864748 * 2 ^ 59
def prefixEnd_864748 : Nat := 4983230072969 + 3 ^ 40 * 864748 * 2
def baseEnd_864748 : Nat := 394694550234922580598313

theorem tailTrace_864748 : CollatzResearch.WordTrace tailWord_864748 prefixEnd_864748 394694550234922580598313 := by
  unfold tailWord_864748
  simp only [CollatzResearch.WordTrace]
  refine ⟨15769975335586579022765449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21026633780782105363687265 15769975335586579022765449)
  ·
    refine ⟨11827481501689934267074087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15769975335586579022765449 11827481501689934267074087)
    ·
      refine ⟨17741222252534901400611131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11827481501689934267074087 17741222252534901400611131)
      ·
        refine ⟨26611833378802352100916697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17741222252534901400611131 26611833378802352100916697)
        ·
          refine ⟨19958875034101764075687523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26611833378802352100916697 19958875034101764075687523)
          ·
            refine ⟨29938312551152646113531285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19958875034101764075687523 29938312551152646113531285)
            ·
              refine ⟨1403358400835280286571779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29938312551152646113531285 1403358400835280286571779)
              ·
                refine ⟨2105037601252920429857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403358400835280286571779 2105037601252920429857669)
                ·
                  refine ⟨394694550234922580598313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105037601252920429857669 394694550234922580598313)
                  ·
                    rfl

theorem cell20_864748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 4].length) (baseStart_864748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864748 prefixEnd_864748 := by exact prefixLift 864748
  have htrace : WordTrace (prefixWord ++ tailWord_864748) baseStart_864748 baseEnd_864748 := by
    simpa [prefixWord, tailWord_864748, baseEnd_864748] using wordTrace_append hprefix tailTrace_864748
  have hstable : (prefixWord ++ tailWord_864748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864748).length < 2 ^ (prefixWord ++ tailWord_864748).sum := by decide
  have hdescent : baseEnd_864748 < baseStart_864748 := by decide
  rcases family_descends (prefixWord ++ tailWord_864748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864772 : List Nat := [2, 3, 2, 3, 1, 2, 1, 6]
def baseStart_864772 : Nat := 118140960795 + 864772 * 2 ^ 59
def prefixEnd_864772 : Nat := 4983230072969 + 3 ^ 40 * 864772 * 2
def baseEnd_864772 : Nat := 131568501496295054599405

theorem tailTrace_864772 : CollatzResearch.WordTrace tailWord_864772 prefixEnd_864772 131568501496295054599405 := by
  unfold tailWord_864772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15770413011543105072202285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21027217348724140096269713 15770413011543105072202285)
  ·
    refine ⟨5913904879328664402075857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15770413011543105072202285 5913904879328664402075857)
    ·
      refine ⟨4435428659496498301556893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5913904879328664402075857 4435428659496498301556893)
      ·
        refine ⟨1663285747311186863083835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4435428659496498301556893 1663285747311186863083835)
        ·
          refine ⟨2494928620966780294625753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1663285747311186863083835 2494928620966780294625753)
          ·
            refine ⟨1871196465725085220969315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2494928620966780294625753 1871196465725085220969315)
            ·
              refine ⟨2806794698587627831453973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871196465725085220969315 2806794698587627831453973)
              ·
                refine ⟨131568501496295054599405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2806794698587627831453973 131568501496295054599405)
                ·
                  rfl

theorem cell20_864772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_864772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864772 prefixEnd_864772 := by exact prefixLift 864772
  have htrace : WordTrace (prefixWord ++ tailWord_864772) baseStart_864772 baseEnd_864772 := by
    simpa [prefixWord, tailWord_864772, baseEnd_864772] using wordTrace_append hprefix tailTrace_864772
  have hstable : (prefixWord ++ tailWord_864772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864772).length < 2 ^ (prefixWord ++ tailWord_864772).sum := by decide
  have hdescent : baseEnd_864772 < baseStart_864772 := by decide
  rcases family_descends (prefixWord ++ tailWord_864772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864782 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 2]
def baseStart_864782 : Nat := 118140960795 + 864782 * 2 ^ 59
def prefixEnd_864782 : Nat := 4983230072969 + 3 ^ 40 * 864782 * 2
def baseEnd_864782 : Nat := 394710068761369573464841

theorem tailTrace_864782 : CollatzResearch.WordTrace tailWord_864782 prefixEnd_864782 394710068761369573464841 := by
  unfold tailWord_864782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3942648844131247731533575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21027460502033321234845733 3942648844131247731533575)
  ·
    refine ⟨5913973266196871597300363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3942648844131247731533575 5913973266196871597300363)
    ·
      refine ⟨8870959899295307395950545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5913973266196871597300363 8870959899295307395950545)
      ·
        refine ⟨6653219924471480546962909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8870959899295307395950545 6653219924471480546962909)
        ·
          refine ⟨2494957471676805205111091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6653219924471480546962909 2494957471676805205111091)
          ·
            refine ⟨3742436207515207807666637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2494957471676805205111091 3742436207515207807666637)
            ·
              refine ⟨1403413577818202927874989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3742436207515207807666637 1403413577818202927874989)
              ·
                refine ⟨526280091681826097953121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403413577818202927874989 526280091681826097953121)
                ·
                  refine ⟨394710068761369573464841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526280091681826097953121 394710068761369573464841)
                  ·
                    rfl

theorem cell20_864782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_864782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864782 prefixEnd_864782 := by exact prefixLift 864782
  have htrace : WordTrace (prefixWord ++ tailWord_864782) baseStart_864782 baseEnd_864782 := by
    simpa [prefixWord, tailWord_864782, baseEnd_864782] using wordTrace_append hprefix tailTrace_864782
  have hstable : (prefixWord ++ tailWord_864782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864782).length < 2 ^ (prefixWord ++ tailWord_864782).sum := by decide
  have hdescent : baseEnd_864782 < baseStart_864782 := by decide
  rcases family_descends (prefixWord ++ tailWord_864782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864803 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 4]
def baseStart_864803 : Nat := 118140960795 + 864803 * 2 ^ 59
def prefixEnd_864803 : Nat := 4983230072969 + 3 ^ 40 * 864803 * 2
def baseEnd_864803 : Nat := 394719653733586833764755

theorem tailTrace_864803 : CollatzResearch.WordTrace tailWord_864803 prefixEnd_864803 394719653733586833764755 := by
  unfold tailWord_864803
  simp only [CollatzResearch.WordTrace]
  refine ⟨31541956685973902438783063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21027971123982601625855375 31541956685973902438783063)
  ·
    refine ⟨47312935028960853658174595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31541956685973902438783063 47312935028960853658174595)
    ·
      refine ⟨70969402543441280487261893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47312935028960853658174595 70969402543441280487261893)
      ·
        refine ⟨13306762976895240091361605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70969402543441280487261893 13306762976895240091361605)
        ·
          refine ⟨2495018058167857517130301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13306762976895240091361605 2495018058167857517130301)
          ·
            refine ⟨935631771812946568923863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2495018058167857517130301 935631771812946568923863)
            ·
              refine ⟨1403447657719419853385795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935631771812946568923863 1403447657719419853385795)
              ·
                refine ⟨2105171486579129780078693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1403447657719419853385795 2105171486579129780078693)
                ·
                  refine ⟨394719653733586833764755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105171486579129780078693 394719653733586833764755)
                  ·
                    rfl

theorem cell20_864803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 4].length) (baseStart_864803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864803 prefixEnd_864803 := by exact prefixLift 864803
  have htrace : WordTrace (prefixWord ++ tailWord_864803) baseStart_864803 baseEnd_864803 := by
    simpa [prefixWord, tailWord_864803, baseEnd_864803] using wordTrace_append hprefix tailTrace_864803
  have hstable : (prefixWord ++ tailWord_864803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864803).length < 2 ^ (prefixWord ++ tailWord_864803).sum := by decide
  have hdescent : baseEnd_864803 < baseStart_864803 := by decide
  rcases family_descends (prefixWord ++ tailWord_864803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864810 : List Nat := [3, 1, 4, 1, 1, 3, 2, 5]
def baseStart_864810 : Nat := 118140960795 + 864810 * 2 ^ 59
def prefixEnd_864810 : Nat := 4983230072969 + 3 ^ 40 * 864810 * 2
def baseEnd_864810 : Nat := 131574282908108640177131

theorem tailTrace_864810 : CollatzResearch.WordTrace tailWord_864810 prefixEnd_864810 131574282908108640177131 := by
  unfold tailWord_864810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7885552999237135658571971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21028141331299028422858589 7885552999237135658571971)
  ·
    refine ⟨11828329498855703487857957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7885552999237135658571971 11828329498855703487857957)
    ·
      refine ⟨2217811781035444403973367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11828329498855703487857957 2217811781035444403973367)
      ·
        refine ⟨3326717671553166605960051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2217811781035444403973367 3326717671553166605960051)
        ·
          refine ⟨4990076507329749908940077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3326717671553166605960051 4990076507329749908940077)
          ·
            refine ⟨1871278690248656215852529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4990076507329749908940077 1871278690248656215852529)
            ·
              refine ⟨1403459017686492161889397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871278690248656215852529 1403459017686492161889397)
              ·
                refine ⟨131574282908108640177131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1403459017686492161889397 131574282908108640177131)
                ·
                  rfl

theorem cell20_864810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_864810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864810 prefixEnd_864810 := by exact prefixLift 864810
  have htrace : WordTrace (prefixWord ++ tailWord_864810) baseStart_864810 baseEnd_864810 := by
    simpa [prefixWord, tailWord_864810, baseEnd_864810] using wordTrace_append hprefix tailTrace_864810
  have hstable : (prefixWord ++ tailWord_864810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864810).length < 2 ^ (prefixWord ++ tailWord_864810).sum := by decide
  have hdescent : baseEnd_864810 < baseStart_864810 := by decide
  rcases family_descends (prefixWord ++ tailWord_864810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864855 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 3]
def baseStart_864855 : Nat := 118140960795 + 864855 * 2 ^ 59
def prefixEnd_864855 : Nat := 4983230072969 + 3 ^ 40 * 864855 * 2
def baseEnd_864855 : Nat := 394743387950505764031209

theorem tailTrace_864855 : CollatzResearch.WordTrace tailWord_864855 prefixEnd_864855 394743387950505764031209 := by
  unfold tailWord_864855
  simp only [CollatzResearch.WordTrace]
  refine ⟨31543853281785515319676019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21029235521190343546450679 31543853281785515319676019)
  ·
    refine ⟨47315779922678272979514029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31543853281785515319676019 47315779922678272979514029)
    ·
      refine ⟨17743417471004352367317761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47315779922678272979514029 17743417471004352367317761)
      ·
        refine ⟨13307563103253264275488321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17743417471004352367317761 13307563103253264275488321)
        ·
          refine ⟨9980672327439948206616241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13307563103253264275488321 9980672327439948206616241)
          ·
            refine ⟨7485504245579961154962181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9980672327439948206616241 7485504245579961154962181)
            ·
              refine ⟨1403532046046242716555409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7485504245579961154962181 1403532046046242716555409)
              ·
                refine ⟨1052649034534682037416557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1403532046046242716555409 1052649034534682037416557)
                ·
                  refine ⟨394743387950505764031209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052649034534682037416557 394743387950505764031209)
                  ·
                    rfl

theorem cell20_864855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_864855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864855 prefixEnd_864855 := by exact prefixLift 864855
  have htrace : WordTrace (prefixWord ++ tailWord_864855) baseStart_864855 baseEnd_864855 := by
    simpa [prefixWord, tailWord_864855, baseEnd_864855] using wordTrace_append hprefix tailTrace_864855
  have hstable : (prefixWord ++ tailWord_864855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864855).length < 2 ^ (prefixWord ++ tailWord_864855).sum := by decide
  have hdescent : baseEnd_864855 < baseStart_864855 := by decide
  rcases family_descends (prefixWord ++ tailWord_864855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864941 : List Nat := [1, 5, 2, 1, 1, 4, 2, 4]
def baseStart_864941 : Nat := 118140960795 + 864941 * 2 ^ 59
def prefixEnd_864941 : Nat := 4983230072969 + 3 ^ 40 * 864941 * 2
def baseEnd_864941 : Nat := 131594213564623895721397

theorem tailTrace_864941 : CollatzResearch.WordTrace tailWord_864941 prefixEnd_864941 131594213564623895721397 := by
  unfold tailWord_864941
  simp only [CollatzResearch.WordTrace]
  refine ⟨31546989959473952007306677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21031326639649301338204451 31546989959473952007306677)
  ·
    refine ⟨2957530308700683000685001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31546989959473952007306677 2957530308700683000685001)
    ·
      refine ⟨2218147731525512250513751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2957530308700683000685001 2218147731525512250513751)
      ·
        refine ⟨3327221597288268375770627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218147731525512250513751 3327221597288268375770627)
        ·
          refine ⟨4990832395932402563655941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3327221597288268375770627 4990832395932402563655941)
          ·
            refine ⟨935781074237325480685489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4990832395932402563655941 935781074237325480685489)
            ·
              refine ⟨701835805677994110514117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935781074237325480685489 701835805677994110514117)
              ·
                refine ⟨131594213564623895721397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701835805677994110514117 131594213564623895721397)
                ·
                  rfl

theorem cell20_864941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 4].length) (baseStart_864941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864941 prefixEnd_864941 := by exact prefixLift 864941
  have htrace : WordTrace (prefixWord ++ tailWord_864941) baseStart_864941 baseEnd_864941 := by
    simpa [prefixWord, tailWord_864941, baseEnd_864941] using wordTrace_append hprefix tailTrace_864941
  have hstable : (prefixWord ++ tailWord_864941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864941).length < 2 ^ (prefixWord ++ tailWord_864941).sum := by decide
  have hdescent : baseEnd_864941 < baseStart_864941 := by decide
  rcases family_descends (prefixWord ++ tailWord_864941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864951 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 2]
def baseStart_864951 : Nat := 118140960795 + 864951 * 2 ^ 59
def prefixEnd_864951 : Nat := 4983230072969 + 3 ^ 40 * 864951 * 2
def baseEnd_864951 : Nat := 394787204966356096830817

theorem tailTrace_864951 : CollatzResearch.WordTrace tailWord_864951 prefixEnd_864951 394787204966356096830817 := by
  unfold tailWord_864951
  simp only [CollatzResearch.WordTrace]
  refine ⟨31547354689437723715170707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21031569792958482476780471 31547354689437723715170707)
  ·
    refine ⟨47321032034156585572756061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31547354689437723715170707 47321032034156585572756061)
    ·
      refine ⟨17745387012808719589783523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47321032034156585572756061 17745387012808719589783523)
      ·
        refine ⟨26618080519213079384675285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17745387012808719589783523 26618080519213079384675285)
        ·
          refine ⟨623861262169056548078327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26618080519213079384675285 623861262169056548078327)
          ·
            refine ⟨935791893253584822117491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623861262169056548078327 935791893253584822117491)
            ·
              refine ⟨1403687839880377233176237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935791893253584822117491 1403687839880377233176237)
              ·
                refine ⟨526382939955141462441089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403687839880377233176237 526382939955141462441089)
                ·
                  refine ⟨394787204966356096830817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526382939955141462441089 394787204966356096830817)
                  ·
                    rfl

theorem cell20_864951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 2].length) (baseStart_864951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864951 prefixEnd_864951 := by exact prefixLift 864951
  have htrace : WordTrace (prefixWord ++ tailWord_864951) baseStart_864951 baseEnd_864951 := by
    simpa [prefixWord, tailWord_864951, baseEnd_864951] using wordTrace_append hprefix tailTrace_864951
  have hstable : (prefixWord ++ tailWord_864951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864951).length < 2 ^ (prefixWord ++ tailWord_864951).sum := by decide
  have hdescent : baseEnd_864951 < baseStart_864951 := by decide
  rcases family_descends (prefixWord ++ tailWord_864951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_864983 : List Nat := [1, 1, 3, 2, 1, 5, 2, 5]
def baseStart_864983 : Nat := 118140960795 + 864983 * 2 ^ 59
def prefixEnd_864983 : Nat := 4983230072969 + 3 ^ 40 * 864983 * 2
def baseEnd_864983 : Nat := 131600603546102069254673

theorem tailTrace_864983 : CollatzResearch.WordTrace tailWord_864983 prefixEnd_864983 131600603546102069254673 := by
  unfold tailWord_864983
  simp only [CollatzResearch.WordTrace]
  refine ⟨31548521825321793180335603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21032347883547862120223735 31548521825321793180335603)
  ·
    refine ⟨47322782737982689770503405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31548521825321793180335603 47322782737982689770503405)
    ·
      refine ⟨17746043526743508663938777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47322782737982689770503405 17746043526743508663938777)
      ·
        refine ⟨13309532645057631497954083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17746043526743508663938777 13309532645057631497954083)
        ·
          refine ⟨19964298967586447246931125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13309532645057631497954083 19964298967586447246931125)
          ·
            refine ⟨1871653028211229429399793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19964298967586447246931125 1871653028211229429399793)
            ·
              refine ⟨1403739771158422072049845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1871653028211229429399793 1403739771158422072049845)
              ·
                refine ⟨131600603546102069254673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1403739771158422072049845 131600603546102069254673)
                ·
                  rfl

theorem cell20_864983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 5].length) (baseStart_864983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_864983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_864983 prefixEnd_864983 := by exact prefixLift 864983
  have htrace : WordTrace (prefixWord ++ tailWord_864983) baseStart_864983 baseEnd_864983 := by
    simpa [prefixWord, tailWord_864983, baseEnd_864983] using wordTrace_append hprefix tailTrace_864983
  have hstable : (prefixWord ++ tailWord_864983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_864983).length < 2 ^ (prefixWord ++ tailWord_864983).sum := by decide
  have hdescent : baseEnd_864983 < baseStart_864983 := by decide
  rcases family_descends (prefixWord ++ tailWord_864983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865035 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 4]
def baseStart_865035 : Nat := 118140960795 + 865035 * 2 ^ 59
def prefixEnd_865035 : Nat := 4983230072969 + 3 ^ 40 * 865035 * 2
def baseEnd_865035 : Nat := 394825544855225138030473

theorem tailTrace_865035 : CollatzResearch.WordTrace tailWord_865035 prefixEnd_865035 394825544855225138030473 := by
  unfold tailWord_865035
  simp only [CollatzResearch.WordTrace]
  refine ⟨31550418421133406061228559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21033612280755604040819039 31550418421133406061228559)
  ·
    refine ⟨47325627631700109091842839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31550418421133406061228559 47325627631700109091842839)
    ·
      refine ⟨70988441447550163637764259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47325627631700109091842839 70988441447550163637764259)
      ·
        refine ⟨106482662171325245456646389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70988441447550163637764259 106482662171325245456646389)
        ·
          refine ⟨9982749578561741761560599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106482662171325245456646389 9982749578561741761560599)
          ·
            refine ⟨14974124367842612642340899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9982749578561741761560599 14974124367842612642340899)
            ·
              refine ⟨22461186551763918963511349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14974124367842612642340899 22461186551763918963511349)
              ·
                refine ⟨2105736239227867402829189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22461186551763918963511349 2105736239227867402829189)
                ·
                  refine ⟨394825544855225138030473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105736239227867402829189 394825544855225138030473)
                  ·
                    rfl

theorem cell20_865035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_865035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865035 prefixEnd_865035 := by exact prefixLift 865035
  have htrace : WordTrace (prefixWord ++ tailWord_865035) baseStart_865035 baseEnd_865035 := by
    simpa [prefixWord, tailWord_865035, baseEnd_865035] using wordTrace_append hprefix tailTrace_865035
  have hstable : (prefixWord ++ tailWord_865035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865035).length < 2 ^ (prefixWord ++ tailWord_865035).sum := by decide
  have hdescent : baseEnd_865035 < baseStart_865035 := by decide
  rcases family_descends (prefixWord ++ tailWord_865035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865052 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 4]
def baseStart_865052 : Nat := 118140960795 + 865052 * 2 ^ 59
def prefixEnd_865052 : Nat := 4983230072969 + 3 ^ 40 * 865052 * 2
def baseEnd_865052 : Nat := 394833304118448634463737

theorem tailTrace_865052 : CollatzResearch.WordTrace tailWord_865052 prefixEnd_865052 394833304118448634463737 := by
  unfold tailWord_865052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775519231035908982298705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21034025641381211976398273 15775519231035908982298705)
  ·
    refine ⟨11831639423276931736724029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15775519231035908982298705 11831639423276931736724029)
    ·
      refine ⟨4436864783728849401271511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11831639423276931736724029 4436864783728849401271511)
      ·
        refine ⟨6655297175593274101907267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4436864783728849401271511 6655297175593274101907267)
        ·
          refine ⟨9982945763389911152860901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6655297175593274101907267 9982945763389911152860901)
          ·
            refine ⟨1871802330635608341161419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9982945763389911152860901 1871802330635608341161419)
            ·
              refine ⟨2807703495953412511742129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1871802330635608341161419 2807703495953412511742129)
              ·
                refine ⟨2105777621965059383806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2807703495953412511742129 2105777621965059383806597)
                ·
                  refine ⟨394833304118448634463737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2105777621965059383806597 394833304118448634463737)
                  ·
                    rfl

theorem cell20_865052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_865052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865052 prefixEnd_865052 := by exact prefixLift 865052
  have htrace : WordTrace (prefixWord ++ tailWord_865052) baseStart_865052 baseEnd_865052 := by
    simpa [prefixWord, tailWord_865052, baseEnd_865052] using wordTrace_append hprefix tailTrace_865052
  have hstable : (prefixWord ++ tailWord_865052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865052).length < 2 ^ (prefixWord ++ tailWord_865052).sum := by decide
  have hdescent : baseEnd_865052 < baseStart_865052 := by decide
  rcases family_descends (prefixWord ++ tailWord_865052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865073 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 6]
def baseStart_865073 : Nat := 118140960795 + 865073 * 2 ^ 59
def prefixEnd_865073 : Nat := 4983230072969 + 3 ^ 40 * 865073 * 2
def baseEnd_865073 : Nat := 394842889090665894763651

theorem tailTrace_865073 : CollatzResearch.WordTrace tailWord_865073 prefixEnd_865073 394842889090665894763651 := by
  unfold tailWord_865073
  simp only [CollatzResearch.WordTrace]
  refine ⟨31551804394995738551111873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21034536263330492367407915 31551804394995738551111873)
  ·
    refine ⟨23663853296246803913333905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31551804394995738551111873 23663853296246803913333905)
    ·
      refine ⟨17747889972185102935000429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23663853296246803913333905 17747889972185102935000429)
      ·
        refine ⟨6655458739569413600625161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17747889972185102935000429 6655458739569413600625161)
        ·
          refine ⟨4991594054677060200468871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6655458739569413600625161 4991594054677060200468871)
          ·
            refine ⟨7487391082015590300703307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4991594054677060200468871 7487391082015590300703307)
            ·
              refine ⟨11231086623023385451054961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7487391082015590300703307 11231086623023385451054961)
              ·
                refine ⟨8423314967267539088291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11231086623023385451054961 8423314967267539088291221)
                ·
                  refine ⟨394842889090665894763651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8423314967267539088291221 394842889090665894763651)
                  ·
                    rfl

theorem cell20_865073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_865073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865073 prefixEnd_865073 := by exact prefixLift 865073
  have htrace : WordTrace (prefixWord ++ tailWord_865073) baseStart_865073 baseEnd_865073 := by
    simpa [prefixWord, tailWord_865073, baseEnd_865073] using wordTrace_append hprefix tailTrace_865073
  have hstable : (prefixWord ++ tailWord_865073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865073).length < 2 ^ (prefixWord ++ tailWord_865073).sum := by decide
  have hdescent : baseEnd_865073 < baseStart_865073 := by decide
  rcases family_descends (prefixWord ++ tailWord_865073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865076 : List Nat := [2, 5, 1, 1, 3, 1, 7]
def baseStart_865076 : Nat := 118140960795 + 865076 * 2 ^ 59
def prefixEnd_865076 : Nat := 4983230072969 + 3 ^ 40 * 865076 * 2
def baseEnd_865076 : Nat := 43871584263601246407071

theorem tailTrace_865076 : CollatzResearch.WordTrace tailWord_865076 prefixEnd_865076 43871584263601246407071 := by
  unfold tailWord_865076
  simp only [CollatzResearch.WordTrace]
  refine ⟨15775956906992435031735541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21034609209323246708980721 15775956906992435031735541)
  ·
    refine ⟨1478995960030540784225207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15775956906992435031735541 1478995960030540784225207)
    ·
      refine ⟨2218493940045811176337811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1478995960030540784225207 2218493940045811176337811)
      ·
        refine ⟨3327740910068716764506717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218493940045811176337811 3327740910068716764506717)
        ·
          refine ⟨1247902841275768786690019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3327740910068716764506717 1247902841275768786690019)
          ·
            refine ⟨1871854261913653180035029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247902841275768786690019 1871854261913653180035029)
            ·
              refine ⟨43871584263601246407071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1871854261913653180035029 43871584263601246407071)
              ·
                rfl

theorem cell20_865076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 7].length) (baseStart_865076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865076 prefixEnd_865076 := by exact prefixLift 865076
  have htrace : WordTrace (prefixWord ++ tailWord_865076) baseStart_865076 baseEnd_865076 := by
    simpa [prefixWord, tailWord_865076, baseEnd_865076] using wordTrace_append hprefix tailTrace_865076
  have hstable : (prefixWord ++ tailWord_865076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865076).length < 2 ^ (prefixWord ++ tailWord_865076).sum := by decide
  have hdescent : baseEnd_865076 < baseStart_865076 := by decide
  rcases family_descends (prefixWord ++ tailWord_865076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865080 : List Nat := [2, 1, 2, 1, 3, 2, 9]
def baseStart_865080 : Nat := 118140960795 + 865080 * 2 ^ 59
def prefixEnd_865080 : Nat := 4983230072969 + 3 ^ 40 * 865080 * 2
def baseEnd_865080 : Nat := 43871787120156109058921

theorem tailTrace_865080 : CollatzResearch.WordTrace tailWord_865080 prefixEnd_865080 43871787120156109058921 := by
  unfold tailWord_865080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776029852985189373308347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21034706470646919164411129 15776029852985189373308347)
  ·
    refine ⟨23664044779477784059962521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15776029852985189373308347 23664044779477784059962521)
    ·
      refine ⟨17748033584608338044971891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23664044779477784059962521 17748033584608338044971891)
      ·
        refine ⟨26622050376912507067457837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17748033584608338044971891 26622050376912507067457837)
        ·
          refine ⟨9983268891342190150296689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26622050376912507067457837 9983268891342190150296689)
          ·
            refine ⟨7487451668506642612722517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9983268891342190150296689 7487451668506642612722517)
            ·
              refine ⟨43871787120156109058921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7487451668506642612722517 43871787120156109058921)
              ·
                rfl

theorem cell20_865080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 9].length) (baseStart_865080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865080 prefixEnd_865080 := by exact prefixLift 865080
  have htrace : WordTrace (prefixWord ++ tailWord_865080) baseStart_865080 baseEnd_865080 := by
    simpa [prefixWord, tailWord_865080, baseEnd_865080] using wordTrace_append hprefix tailTrace_865080
  have hstable : (prefixWord ++ tailWord_865080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865080).length < 2 ^ (prefixWord ++ tailWord_865080).sum := by decide
  have hdescent : baseEnd_865080 < baseStart_865080 := by decide
  rcases family_descends (prefixWord ++ tailWord_865080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865100 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 3]
def baseStart_865100 : Nat := 118140960795 + 865100 * 2 ^ 59
def prefixEnd_865100 : Nat := 4983230072969 + 3 ^ 40 * 865100 * 2
def baseEnd_865100 : Nat := 394855212626373800863541

theorem tailTrace_865100 : CollatzResearch.WordTrace tailWord_865100 prefixEnd_865100 394855212626373800863541 := by
  unfold tailWord_865100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776394582948961081172377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21035192777265281441563169 15776394582948961081172377)
  ·
    refine ⟨11832295937211720810879283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15776394582948961081172377 11832295937211720810879283)
    ·
      refine ⟨17748443905817581216318925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11832295937211720810879283 17748443905817581216318925)
      ·
        refine ⟨6655666464681592956119597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17748443905817581216318925 6655666464681592956119597)
        ·
          refine ⟨2495874924255597358544849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6655666464681592956119597 2495874924255597358544849)
          ·
            refine ⟨1871906193191698018908637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2495874924255597358544849 1871906193191698018908637)
            ·
              refine ⟨701964822446886757090739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1871906193191698018908637 701964822446886757090739)
              ·
                refine ⟨1052947233670330135636109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 701964822446886757090739 1052947233670330135636109)
                ·
                  refine ⟨394855212626373800863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052947233670330135636109 394855212626373800863541)
                  ·
                    rfl

theorem cell20_865100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_865100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865100 prefixEnd_865100 := by exact prefixLift 865100
  have htrace : WordTrace (prefixWord ++ tailWord_865100) baseStart_865100 baseEnd_865100 := by
    simpa [prefixWord, tailWord_865100, baseEnd_865100] using wordTrace_append hprefix tailTrace_865100
  have hstable : (prefixWord ++ tailWord_865100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865100).length < 2 ^ (prefixWord ++ tailWord_865100).sum := by decide
  have hdescent : baseEnd_865100 < baseStart_865100 := by decide
  rcases family_descends (prefixWord ++ tailWord_865100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865104 : List Nat := [2, 1, 1, 1, 1, 4, 2, 5, 3]
def baseStart_865104 : Nat := 118140960795 + 865104 * 2 ^ 59
def prefixEnd_865104 : Nat := 4983230072969 + 3 ^ 40 * 865104 * 2
def baseEnd_865104 : Nat := 394857038335367564730191

theorem tailTrace_865104 : CollatzResearch.WordTrace tailWord_865104 prefixEnd_865104 394857038335367564730191 := by
  unfold tailWord_865104
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776467528941715422745183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21035290038588953896993577 15776467528941715422745183)
  ·
    refine ⟨23664701293412573134117775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15776467528941715422745183 23664701293412573134117775)
    ·
      refine ⟨35497051940118859701176663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23664701293412573134117775 35497051940118859701176663)
      ·
        refine ⟨53245577910178289551764995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35497051940118859701176663 53245577910178289551764995)
        ·
          refine ⟨79868366865267434327647493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53245577910178289551764995 79868366865267434327647493)
          ·
            refine ⟨14975318787237643936433905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79868366865267434327647493 14975318787237643936433905)
            ·
              refine ⟨11231489090428232952325429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14975318787237643936433905 11231489090428232952325429)
              ·
                refine ⟨1052952102227646839280509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11231489090428232952325429 1052952102227646839280509)
                ·
                  refine ⟨394857038335367564730191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1052952102227646839280509 394857038335367564730191)
                  ·
                    rfl

theorem cell20_865104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 5, 3].length) (baseStart_865104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865104 prefixEnd_865104 := by exact prefixLift 865104
  have htrace : WordTrace (prefixWord ++ tailWord_865104) baseStart_865104 baseEnd_865104 := by
    simpa [prefixWord, tailWord_865104, baseEnd_865104] using wordTrace_append hprefix tailTrace_865104
  have hstable : (prefixWord ++ tailWord_865104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865104).length < 2 ^ (prefixWord ++ tailWord_865104).sum := by decide
  have hdescent : baseEnd_865104 < baseStart_865104 := by decide
  rcases family_descends (prefixWord ++ tailWord_865104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865114 : List Nat := [3, 1, 1, 2, 1, 6, 2, 4]
def baseStart_865114 : Nat := 118140960795 + 865114 * 2 ^ 59
def prefixEnd_865114 : Nat := 4983230072969 + 3 ^ 40 * 865114 * 2
def baseEnd_865114 : Nat := 131620534202617324798939

theorem tailTrace_865114 : CollatzResearch.WordTrace tailWord_865114 prefixEnd_865114 131620534202617324798939 := by
  unfold tailWord_865114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7888324946961800638338599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21035533191898135035569597 7888324946961800638338599)
  ·
    refine ⟨11832487420442700957507899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7888324946961800638338599 11832487420442700957507899)
    ·
      refine ⟨17748731130664051436261849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11832487420442700957507899 17748731130664051436261849)
      ·
        refine ⟨13311548347998038577196387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17748731130664051436261849 13311548347998038577196387)
        ·
          refine ⟨19967322521997057865794581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13311548347998038577196387 19967322521997057865794581)
          ·
            refine ⟨935968243218612087459121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19967322521997057865794581 935968243218612087459121)
            ·
              refine ⟨701976182413959065594341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935968243218612087459121 701976182413959065594341)
              ·
                refine ⟨131620534202617324798939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 701976182413959065594341 131620534202617324798939)
                ·
                  rfl

theorem cell20_865114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_865114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865114 prefixEnd_865114 := by exact prefixLift 865114
  have htrace : WordTrace (prefixWord ++ tailWord_865114) baseStart_865114 baseEnd_865114 := by
    simpa [prefixWord, tailWord_865114, baseEnd_865114] using wordTrace_append hprefix tailTrace_865114
  have hstable : (prefixWord ++ tailWord_865114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865114).length < 2 ^ (prefixWord ++ tailWord_865114).sum := by decide
  have hdescent : baseEnd_865114 < baseStart_865114 := by decide
  rcases family_descends (prefixWord ++ tailWord_865114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865124 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 2]
def baseStart_865124 : Nat := 118140960795 + 865124 * 2 ^ 59
def prefixEnd_865124 : Nat := 4983230072969 + 3 ^ 40 * 865124 * 2
def baseEnd_865124 : Nat := 394866166880336384063443

theorem tailTrace_865124 : CollatzResearch.WordTrace tailWord_865124 prefixEnd_865124 394866166880336384063443 := by
  unfold tailWord_865124
  simp only [CollatzResearch.WordTrace]
  refine ⟨15776832258905487130609213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21035776345207316174145617 15776832258905487130609213)
  ·
    refine ⟨5916312097089557673978455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15776832258905487130609213 5916312097089557673978455)
    ·
      refine ⟨8874468145634336510967683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5916312097089557673978455 8874468145634336510967683)
      ·
        refine ⟨13311702218451504766451525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8874468145634336510967683 13311702218451504766451525)
        ·
          refine ⟨2495944165959657143709661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13311702218451504766451525 2495944165959657143709661)
          ·
            refine ⟨935979062234871428891123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2495944165959657143709661 935979062234871428891123)
            ·
              refine ⟨1403968593352307143336685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935979062234871428891123 1403968593352307143336685)
              ·
                refine ⟨526488222507115178751257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1403968593352307143336685 526488222507115178751257)
                ·
                  refine ⟨394866166880336384063443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526488222507115178751257 394866166880336384063443)
                  ·
                    rfl

theorem cell20_865124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_865124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865124 prefixEnd_865124 := by exact prefixLift 865124
  have htrace : WordTrace (prefixWord ++ tailWord_865124) baseStart_865124 baseEnd_865124 := by
    simpa [prefixWord, tailWord_865124, baseEnd_865124] using wordTrace_append hprefix tailTrace_865124
  have hstable : (prefixWord ++ tailWord_865124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865124).length < 2 ^ (prefixWord ++ tailWord_865124).sum := by decide
  have hdescent : baseEnd_865124 < baseStart_865124 := by decide
  rcases family_descends (prefixWord ++ tailWord_865124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865159 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 3]
def baseStart_865159 : Nat := 118140960795 + 865159 * 2 ^ 59
def prefixEnd_865159 : Nat := 4983230072969 + 3 ^ 40 * 865159 * 2
def baseEnd_865159 : Nat := 394882141834031817896633

theorem tailTrace_865159 : CollatzResearch.WordTrace tailWord_865159 prefixEnd_865159 394882141834031817896633 := by
  unfold tailWord_865159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31554941072684175238742531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21036627381789450159161687 31554941072684175238742531)
  ·
    refine ⟨47332411609026262858113797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31554941072684175238742531 47332411609026262858113797)
    ·
      refine ⟨8874827176692424285896337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47332411609026262858113797 8874827176692424285896337)
      ·
        refine ⟨6656120382519318214422253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8874827176692424285896337 6656120382519318214422253)
        ·
          refine ⟨2496045143444744330408345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6656120382519318214422253 2496045143444744330408345)
          ·
            refine ⟨1872033857583558247806259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496045143444744330408345 1872033857583558247806259)
            ·
              refine ⟨2808050786375337371709389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1872033857583558247806259 2808050786375337371709389)
              ·
                refine ⟨1053019044890751514391021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2808050786375337371709389 1053019044890751514391021)
                ·
                  refine ⟨394882141834031817896633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053019044890751514391021 394882141834031817896633)
                  ·
                    rfl

theorem cell20_865159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 3].length) (baseStart_865159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865159 prefixEnd_865159 := by exact prefixLift 865159
  have htrace : WordTrace (prefixWord ++ tailWord_865159) baseStart_865159 baseEnd_865159 := by
    simpa [prefixWord, tailWord_865159, baseEnd_865159] using wordTrace_append hprefix tailTrace_865159
  have hstable : (prefixWord ++ tailWord_865159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865159).length < 2 ^ (prefixWord ++ tailWord_865159).sum := by decide
  have hdescent : baseEnd_865159 < baseStart_865159 := by decide
  rcases family_descends (prefixWord ++ tailWord_865159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865238 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_865238 : Nat := 118140960795 + 865238 * 2 ^ 59
def prefixEnd_865238 : Nat := 4983230072969 + 3 ^ 40 * 865238 * 2
def baseEnd_865238 : Nat := 394918199586658654262977

theorem tailTrace_865238 : CollatzResearch.WordTrace tailWord_865238 prefixEnd_865238 394918199586658654262977 := by
  unfold tailWord_865238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972363902462373233179273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21038548292931981153912245 1972363902462373233179273)
  ·
    refine ⟨1479272926846779924884455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1972363902462373233179273 1479272926846779924884455)
    ·
      refine ⟨2218909390270169887326683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479272926846779924884455 2218909390270169887326683)
      ·
        refine ⟨3328364085405254830990025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2218909390270169887326683 3328364085405254830990025)
        ·
          refine ⟨2496273064053941123242519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3328364085405254830990025 2496273064053941123242519)
          ·
            refine ⟨3744409596080911684863779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2496273064053941123242519 3744409596080911684863779)
            ·
              refine ⟨5616614394121367527295669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744409596080911684863779 5616614394121367527295669)
              ·
                refine ⟨526557599448878205683969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5616614394121367527295669 526557599448878205683969)
                ·
                  refine ⟨394918199586658654262977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526557599448878205683969 394918199586658654262977)
                  ·
                    rfl

theorem cell20_865238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_865238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865238 prefixEnd_865238 := by exact prefixLift 865238
  have htrace : WordTrace (prefixWord ++ tailWord_865238) baseStart_865238 baseEnd_865238 := by
    simpa [prefixWord, tailWord_865238, baseEnd_865238] using wordTrace_append hprefix tailTrace_865238
  have hstable : (prefixWord ++ tailWord_865238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865238).length < 2 ^ (prefixWord ++ tailWord_865238).sum := by decide
  have hdescent : baseEnd_865238 < baseStart_865238 := by decide
  rcases family_descends (prefixWord ++ tailWord_865238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865263 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 4]
def baseStart_865263 : Nat := 118140960795 + 865263 * 2 ^ 59
def prefixEnd_865263 : Nat := 4983230072969 + 3 ^ 40 * 865263 * 2
def baseEnd_865263 : Nat := 394929610267869678429541

theorem tailTrace_865263 : CollatzResearch.WordTrace tailWord_865263 prefixEnd_865263 394929610267869678429541 := by
  unfold tailWord_865263
  simp only [CollatzResearch.WordTrace]
  refine ⟨31558734264307401000528443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21039156176204934000352295 31558734264307401000528443)
  ·
    refine ⟨47338101396461101500792665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31558734264307401000528443 47338101396461101500792665)
    ·
      refine ⟨35503576047345826125594499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47338101396461101500792665 35503576047345826125594499)
      ·
        refine ⟨53255364071018739188391749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35503576047345826125594499 53255364071018739188391749)
        ·
          refine ⟨9985380763316013597823453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53255364071018739188391749 9985380763316013597823453)
          ·
            refine ⟨3744517786243505099183795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9985380763316013597823453 3744517786243505099183795)
            ·
              refine ⟨5616776679365257648775693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744517786243505099183795 5616776679365257648775693)
              ·
                refine ⟨2106291254761971618290885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5616776679365257648775693 2106291254761971618290885)
                ·
                  refine ⟨394929610267869678429541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106291254761971618290885 394929610267869678429541)
                  ·
                    rfl

theorem cell20_865263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_865263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865263 prefixEnd_865263 := by exact prefixLift 865263
  have htrace : WordTrace (prefixWord ++ tailWord_865263) baseStart_865263 baseEnd_865263 := by
    simpa [prefixWord, tailWord_865263, baseEnd_865263] using wordTrace_append hprefix tailTrace_865263
  have hstable : (prefixWord ++ tailWord_865263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865263).length < 2 ^ (prefixWord ++ tailWord_865263).sum := by decide
  have hdescent : baseEnd_865263 < baseStart_865263 := by decide
  rcases family_descends (prefixWord ++ tailWord_865263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865273 : List Nat := [1, 2, 1, 3, 1, 3, 5, 1, 3]
def baseStart_865273 : Nat := 118140960795 + 865273 * 2 ^ 59
def prefixEnd_865273 : Nat := 4983230072969 + 3 ^ 40 * 865273 * 2
def baseEnd_865273 : Nat := 394934174540354088096167

theorem tailTrace_865273 : CollatzResearch.WordTrace tailWord_865273 prefixEnd_865273 394934174540354088096167 := by
  unfold tailWord_865273
  simp only [CollatzResearch.WordTrace]
  refine ⟨31559098994271172708392473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21039399329514115138928315 31559098994271172708392473)
  ·
    refine ⟨23669324245703379531294355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31559098994271172708392473 23669324245703379531294355)
    ·
      refine ⟨35503986368555069296941533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23669324245703379531294355 35503986368555069296941533)
      ·
        refine ⟨13313994888208150986353075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35503986368555069296941533 13313994888208150986353075)
        ·
          refine ⟨19970992332312226479529613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13313994888208150986353075 19970992332312226479529613)
          ·
            refine ⟨7489122124617084929823605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19970992332312226479529613 7489122124617084929823605)
            ·
              refine ⟨702105199182851712170963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7489122124617084929823605 702105199182851712170963)
              ·
                refine ⟨1053157798774277568256445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702105199182851712170963 1053157798774277568256445)
                ·
                  refine ⟨394934174540354088096167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053157798774277568256445 394934174540354088096167)
                  ·
                    rfl

theorem cell20_865273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_865273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865273 prefixEnd_865273 := by exact prefixLift 865273
  have htrace : WordTrace (prefixWord ++ tailWord_865273) baseStart_865273 baseEnd_865273 := by
    simpa [prefixWord, tailWord_865273, baseEnd_865273] using wordTrace_append hprefix tailTrace_865273
  have hstable : (prefixWord ++ tailWord_865273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865273).length < 2 ^ (prefixWord ++ tailWord_865273).sum := by decide
  have hdescent : baseEnd_865273 < baseStart_865273 := by decide
  rcases family_descends (prefixWord ++ tailWord_865273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865294 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_865294 : Nat := 118140960795 + 865294 * 2 ^ 59
def prefixEnd_865294 : Nat := 4983230072969 + 3 ^ 40 * 865294 * 2
def baseEnd_865294 : Nat := 394943759512571348396081

theorem tailTrace_865294 : CollatzResearch.WordTrace tailWord_865294 prefixEnd_865294 394943759512571348396081 := by
  unfold tailWord_865294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3944983115899386661863367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21039909951463395529937957 3944983115899386661863367)
  ·
    refine ⟨5917474673849079992795051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3944983115899386661863367 5917474673849079992795051)
    ·
      refine ⟨8876212010773619989192577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5917474673849079992795051 8876212010773619989192577)
      ·
        refine ⟨6657159008080214991894433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8876212010773619989192577 6657159008080214991894433)
        ·
          refine ⟨4992869256060161243920825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6657159008080214991894433 4992869256060161243920825)
          ·
            refine ⟨3744651942045120932940619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4992869256060161243920825 3744651942045120932940619)
            ·
              refine ⟨5616977913067681399410929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3744651942045120932940619 5616977913067681399410929)
              ·
                refine ⟨4212733434800761049558197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5616977913067681399410929 4212733434800761049558197)
                ·
                  refine ⟨394943759512571348396081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4212733434800761049558197 394943759512571348396081)
                  ·
                    rfl

theorem cell20_865294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_865294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865294 prefixEnd_865294 := by exact prefixLift 865294
  have htrace : WordTrace (prefixWord ++ tailWord_865294) baseStart_865294 baseEnd_865294 := by
    simpa [prefixWord, tailWord_865294, baseEnd_865294] using wordTrace_append hprefix tailTrace_865294
  have hstable : (prefixWord ++ tailWord_865294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865294).length < 2 ^ (prefixWord ++ tailWord_865294).sum := by decide
  have hdescent : baseEnd_865294 < baseStart_865294 := by decide
  rcases family_descends (prefixWord ++ tailWord_865294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865314 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 2]
def baseStart_865314 : Nat := 118140960795 + 865314 * 2 ^ 59
def prefixEnd_865314 : Nat := 4983230072969 + 3 ^ 40 * 865314 * 2
def baseEnd_865314 : Nat := 394952888057540167729333

theorem tailTrace_865314 : CollatzResearch.WordTrace tailWord_865314 prefixEnd_865314 394952888057540167729333 := by
  unfold tailWord_865314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7890148596780659177658749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21040396258081757807089997 7890148596780659177658749)
  ·
    refine ⟨2958805723792747191622031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7890148596780659177658749 2958805723792747191622031)
    ·
      refine ⟨4438208585689120787433047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2958805723792747191622031 4438208585689120787433047)
      ·
        refine ⟨6657312878533681181149571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4438208585689120787433047 6657312878533681181149571)
        ·
          refine ⟨9985969317800521771724357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657312878533681181149571 9985969317800521771724357)
          ·
            refine ⟨1872369247087597832198317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9985969317800521771724357 1872369247087597832198317)
            ·
              refine ⟨702138467657849187074369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872369247087597832198317 702138467657849187074369)
              ·
                refine ⟨526603850743386890305777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702138467657849187074369 526603850743386890305777)
                ·
                  refine ⟨394952888057540167729333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526603850743386890305777 394952888057540167729333)
                  ·
                    rfl

theorem cell20_865314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_865314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865314 prefixEnd_865314 := by exact prefixLift 865314
  have htrace : WordTrace (prefixWord ++ tailWord_865314) baseStart_865314 baseEnd_865314 := by
    simpa [prefixWord, tailWord_865314, baseEnd_865314] using wordTrace_append hprefix tailTrace_865314
  have hstable : (prefixWord ++ tailWord_865314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865314).length < 2 ^ (prefixWord ++ tailWord_865314).sum := by decide
  have hdescent : baseEnd_865314 < baseStart_865314 := by decide
  rcases family_descends (prefixWord ++ tailWord_865314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865353 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 5]
def baseStart_865353 : Nat := 118140960795 + 865353 * 2 ^ 59
def prefixEnd_865353 : Nat := 4983230072969 + 3 ^ 40 * 865353 * 2
def baseEnd_865353 : Nat := 394970688720229365429173

theorem tailTrace_865353 : CollatzResearch.WordTrace tailWord_865353 prefixEnd_865353 394970688720229365429173 := by
  unfold tailWord_865353
  simp only [CollatzResearch.WordTrace]
  refine ⟨31562016833981346371304713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21041344555987564247536475 31562016833981346371304713)
  ·
    refine ⟨23671512625486009778478535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31562016833981346371304713 23671512625486009778478535)
    ·
      refine ⟨35507268938229014667717803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23671512625486009778478535 35507268938229014667717803)
      ·
        refine ⟨53260903407343522001576705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35507268938229014667717803 53260903407343522001576705)
        ·
          refine ⟨39945677555507641501182529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53260903407343522001576705 39945677555507641501182529)
          ·
            refine ⟨29959258166630731125886897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39945677555507641501182529 29959258166630731125886897)
            ·
              refine ⟨22469443624973048344415173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29959258166630731125886897 22469443624973048344415173)
              ·
                refine ⟨4213020679682446564577845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22469443624973048344415173 4213020679682446564577845)
                ·
                  refine ⟨394970688720229365429173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4213020679682446564577845 394970688720229365429173)
                  ·
                    rfl

theorem cell20_865353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_865353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865353 prefixEnd_865353 := by exact prefixLift 865353
  have htrace : WordTrace (prefixWord ++ tailWord_865353) baseStart_865353 baseEnd_865353 := by
    simpa [prefixWord, tailWord_865353, baseEnd_865353] using wordTrace_append hprefix tailTrace_865353
  have hstable : (prefixWord ++ tailWord_865353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865353).length < 2 ^ (prefixWord ++ tailWord_865353).sum := by decide
  have hdescent : baseEnd_865353 < baseStart_865353 := by decide
  rcases family_descends (prefixWord ++ tailWord_865353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865356 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 2]
def baseStart_865356 : Nat := 118140960795 + 865356 * 2 ^ 59
def prefixEnd_865356 : Nat := 4983230072969 + 3 ^ 40 * 865356 * 2
def baseEnd_865356 : Nat := 394972058001974688329161

theorem tailTrace_865356 : CollatzResearch.WordTrace tailWord_865356 prefixEnd_865356 394972058001974688329161 := by
  unfold tailWord_865356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15781063126485238941831961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21041417501980318589109281 15781063126485238941831961)
  ·
    refine ⟨11835797344863929206373971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15781063126485238941831961 11835797344863929206373971)
    ·
      refine ⟨17753696017295893809560957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11835797344863929206373971 17753696017295893809560957)
      ·
        refine ⟨6657636006485960178585359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17753696017295893809560957 6657636006485960178585359)
        ·
          refine ⟨9986454009728940267878039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6657636006485960178585359 9986454009728940267878039)
          ·
            refine ⟨14979681014593410401817059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9986454009728940267878039 14979681014593410401817059)
            ·
              refine ⟨22469521521890115602725589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14979681014593410401817059 22469521521890115602725589)
              ·
                refine ⟨526629410669299584438881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22469521521890115602725589 526629410669299584438881)
                ·
                  refine ⟨394972058001974688329161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526629410669299584438881 394972058001974688329161)
                  ·
                    rfl

theorem cell20_865356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 2].length) (baseStart_865356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865356 prefixEnd_865356 := by exact prefixLift 865356
  have htrace : WordTrace (prefixWord ++ tailWord_865356) baseStart_865356 baseEnd_865356 := by
    simpa [prefixWord, tailWord_865356, baseEnd_865356] using wordTrace_append hprefix tailTrace_865356
  have hstable : (prefixWord ++ tailWord_865356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865356).length < 2 ^ (prefixWord ++ tailWord_865356).sum := by decide
  have hdescent : baseEnd_865356 < baseStart_865356 := by decide
  rcases family_descends (prefixWord ++ tailWord_865356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865397 : List Nat := [1, 3, 4, 3, 1, 1, 3, 4]
def baseStart_865397 : Nat := 118140960795 + 865397 * 2 ^ 59
def prefixEnd_865397 : Nat := 4983230072969 + 3 ^ 40 * 865397 * 2
def baseEnd_865397 : Nat := 131663590506386922654109

theorem tailTrace_865397 : CollatzResearch.WordTrace tailWord_865397 prefixEnd_865397 131663590506386922654109 := by
  unfold tailWord_865397
  simp only [CollatzResearch.WordTrace]
  refine ⟨31563621645821941885906445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21042414430547961257270963 31563621645821941885906445)
  ·
    refine ⟨11836358117183228207214917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31563621645821941885906445 11836358117183228207214917)
    ·
      refine ⟨2219317146971855288852797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11836358117183228207214917 2219317146971855288852797)
      ·
        refine ⟨832243930114445733319799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2219317146971855288852797 832243930114445733319799)
        ·
          refine ⟨1248365895171668599979699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832243930114445733319799 1248365895171668599979699)
          ·
            refine ⟨1872548842757502899969549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248365895171668599979699 1872548842757502899969549)
            ·
              refine ⟨702205816034063587488581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872548842757502899969549 702205816034063587488581)
              ·
                refine ⟨131663590506386922654109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702205816034063587488581 131663590506386922654109)
                ·
                  rfl

theorem cell20_865397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 4].length) (baseStart_865397 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865397 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865397 prefixEnd_865397 := by exact prefixLift 865397
  have htrace : WordTrace (prefixWord ++ tailWord_865397) baseStart_865397 baseEnd_865397 := by
    simpa [prefixWord, tailWord_865397, baseEnd_865397] using wordTrace_append hprefix tailTrace_865397
  have hstable : (prefixWord ++ tailWord_865397).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865397).length < 2 ^ (prefixWord ++ tailWord_865397).sum := by decide
  have hdescent : baseEnd_865397 < baseStart_865397 := by decide
  rcases family_descends (prefixWord ++ tailWord_865397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865432 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 4]
def baseStart_865432 : Nat := 118140960795 + 865432 * 2 ^ 59
def prefixEnd_865432 : Nat := 4983230072969 + 3 ^ 40 * 865432 * 2
def baseEnd_865432 : Nat := 395006746472856201795517

theorem tailTrace_865432 : CollatzResearch.WordTrace tailWord_865432 prefixEnd_865432 395006746472856201795517 := by
  unfold tailWord_865432
  simp only [CollatzResearch.WordTrace]
  refine ⟨15782449100347571431715275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21043265467130095242287033 15782449100347571431715275)
  ·
    refine ⟨23673673650521357147572913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15782449100347571431715275 23673673650521357147572913)
    ·
      refine ⟨17755255237891017860679685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23673673650521357147572913 17755255237891017860679685)
      ·
        refine ⟨3329110357104565848877441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17755255237891017860679685 3329110357104565848877441)
        ·
          refine ⟨2496832767828424386658081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329110357104565848877441 2496832767828424386658081)
          ·
            refine ⟨1872624575871318289993561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2496832767828424386658081 1872624575871318289993561)
            ·
              refine ⟨1404468431903488717495171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1872624575871318289993561 1404468431903488717495171)
              ·
                refine ⟨2106702647855233076242757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1404468431903488717495171 2106702647855233076242757)
                ·
                  refine ⟨395006746472856201795517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2106702647855233076242757 395006746472856201795517)
                  ·
                    rfl

theorem cell20_865432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 4].length) (baseStart_865432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865432 prefixEnd_865432 := by exact prefixLift 865432
  have htrace : WordTrace (prefixWord ++ tailWord_865432) baseStart_865432 baseEnd_865432 := by
    simpa [prefixWord, tailWord_865432, baseEnd_865432] using wordTrace_append hprefix tailTrace_865432
  have hstable : (prefixWord ++ tailWord_865432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865432).length < 2 ^ (prefixWord ++ tailWord_865432).sum := by decide
  have hdescent : baseEnd_865432 < baseStart_865432 := by decide
  rcases family_descends (prefixWord ++ tailWord_865432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865462 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_865462 : Nat := 118140960795 + 865462 * 2 ^ 59
def prefixEnd_865462 : Nat := 4983230072969 + 3 ^ 40 * 865462 * 2
def baseEnd_865462 : Nat := 395020439290309430795395

theorem tailTrace_865462 : CollatzResearch.WordTrace tailWord_865462 prefixEnd_865462 395020439290309430795395 := by
  unfold tailWord_865462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972874524411653624188915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21043994927057638658015093 1972874524411653624188915)
  ·
    refine ⟨2959311786617480436283373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972874524411653624188915 2959311786617480436283373)
    ·
      refine ⟨1109741919981555163606265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2959311786617480436283373 1109741919981555163606265)
      ·
        refine ⟨832306439986166372704699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1109741919981555163606265 832306439986166372704699)
        ·
          refine ⟨1248459659979249559057049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832306439986166372704699 1248459659979249559057049)
          ·
            refine ⟨936344744984437169292787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248459659979249559057049 936344744984437169292787)
            ·
              refine ⟨1404517117476655753939181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936344744984437169292787 1404517117476655753939181)
              ·
                refine ⟨526693919053745907727193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1404517117476655753939181 526693919053745907727193)
                ·
                  refine ⟨395020439290309430795395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526693919053745907727193 395020439290309430795395)
                  ·
                    rfl

theorem cell20_865462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_865462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865462 prefixEnd_865462 := by exact prefixLift 865462
  have htrace : WordTrace (prefixWord ++ tailWord_865462) baseStart_865462 baseEnd_865462 := by
    simpa [prefixWord, tailWord_865462, baseEnd_865462] using wordTrace_append hprefix tailTrace_865462
  have hstable : (prefixWord ++ tailWord_865462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865462).length < 2 ^ (prefixWord ++ tailWord_865462).sum := by decide
  have hdescent : baseEnd_865462 < baseStart_865462 := by decide
  rcases family_descends (prefixWord ++ tailWord_865462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865538 : List Nat := [3, 4, 1, 1, 4, 1, 2, 2, 2]
def baseStart_865538 : Nat := 118140960795 + 865538 * 2 ^ 59
def prefixEnd_865538 : Nat := 4983230072969 + 3 ^ 40 * 865538 * 2
def baseEnd_865538 : Nat := 395055127761190944261751

theorem tailTrace_865538 : CollatzResearch.WordTrace tailWord_865538 prefixEnd_865538 395055127761190944261751 := by
  unfold tailWord_865538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892191084577780741697317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21045842892207415311192845 7892191084577780741697317)
  ·
    refine ⟨1479785828358333889068247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7892191084577780741697317 1479785828358333889068247)
    ·
      refine ⟨2219678742537500833602371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1479785828358333889068247 2219678742537500833602371)
      ·
        refine ⟨3329518113806251250403557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2219678742537500833602371 3329518113806251250403557)
        ·
          refine ⟨624284646338672109450667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3329518113806251250403557 624284646338672109450667)
          ·
            refine ⟨936426969508008164176001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624284646338672109450667 936426969508008164176001)
            ·
              refine ⟨702320227131006123132001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936426969508008164176001 702320227131006123132001)
              ·
                refine ⟨526740170348254592349001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702320227131006123132001 526740170348254592349001)
                ·
                  refine ⟨395055127761190944261751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526740170348254592349001 395055127761190944261751)
                  ·
                    rfl

theorem cell20_865538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_865538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865538 prefixEnd_865538 := by exact prefixLift 865538
  have htrace : WordTrace (prefixWord ++ tailWord_865538) baseStart_865538 baseEnd_865538 := by
    simpa [prefixWord, tailWord_865538, baseEnd_865538] using wordTrace_append hprefix tailTrace_865538
  have hstable : (prefixWord ++ tailWord_865538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865538).length < 2 ^ (prefixWord ++ tailWord_865538).sum := by decide
  have hdescent : baseEnd_865538 < baseStart_865538 := by decide
  rcases family_descends (prefixWord ++ tailWord_865538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865560 : List Nat := [2, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_865560 : Nat := 118140960795 + 865560 * 2 ^ 59
def prefixEnd_865560 : Nat := 4983230072969 + 3 ^ 40 * 865560 * 2
def baseEnd_865560 : Nat := 395065169160656645528327

theorem tailTrace_865560 : CollatzResearch.WordTrace tailWord_865560 prefixEnd_865560 395065169160656645528327 := by
  unfold tailWord_865560
  simp only [CollatzResearch.WordTrace]
  refine ⟨15784783372115710362045067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21046377829487613816060089 15784783372115710362045067)
  ·
    refine ⟨23677175058173565543067601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15784783372115710362045067 23677175058173565543067601)
    ·
      refine ⟨17757881293630174157300701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23677175058173565543067601 17757881293630174157300701)
      ·
        refine ⟨6659205485111315308987763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17757881293630174157300701 6659205485111315308987763)
        ·
          refine ⟨9988808227666972963481645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6659205485111315308987763 9988808227666972963481645)
          ·
            refine ⟨3745803085375114861305617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9988808227666972963481645 3745803085375114861305617)
            ·
              refine ⟨2809352314031336145979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745803085375114861305617 2809352314031336145979213)
              ·
                refine ⟨1053507117761751054742205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2809352314031336145979213 1053507117761751054742205)
                ·
                  refine ⟨395065169160656645528327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053507117761751054742205 395065169160656645528327)
                  ·
                    rfl

theorem cell20_865560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_865560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865560 prefixEnd_865560 := by exact prefixLift 865560
  have htrace : WordTrace (prefixWord ++ tailWord_865560) baseStart_865560 baseEnd_865560 := by
    simpa [prefixWord, tailWord_865560, baseEnd_865560] using wordTrace_append hprefix tailTrace_865560
  have hstable : (prefixWord ++ tailWord_865560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865560).length < 2 ^ (prefixWord ++ tailWord_865560).sum := by decide
  have hdescent : baseEnd_865560 < baseStart_865560 := by decide
  rcases family_descends (prefixWord ++ tailWord_865560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865570 : List Nat := [3, 3, 1, 1, 4, 1, 3, 4]
def baseStart_865570 : Nat := 118140960795 + 865570 * 2 ^ 59
def prefixEnd_865570 : Nat := 4983230072969 + 3 ^ 40 * 865570 * 2
def baseEnd_865570 : Nat := 131689911144380351731651

theorem tailTrace_865570 : CollatzResearch.WordTrace tailWord_865570 prefixEnd_865570 131689911144380351731651 := by
  unfold tailWord_865570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7892482868548798107988541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21046620982796794954636109 7892482868548798107988541)
  ·
    refine ⟨2959681075705799290495703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7892482868548798107988541 2959681075705799290495703)
    ·
      refine ⟨4439521613558698935743555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959681075705799290495703 4439521613558698935743555)
      ·
        refine ⟨6659282420338048403615333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4439521613558698935743555 6659282420338048403615333)
        ·
          refine ⟨1248615453813384075677875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6659282420338048403615333 1248615453813384075677875)
          ·
            refine ⟨1872923180720076113516813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1248615453813384075677875 1872923180720076113516813)
            ·
              refine ⟨702346192770028542568805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1872923180720076113516813 702346192770028542568805)
              ·
                refine ⟨131689911144380351731651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702346192770028542568805 131689911144380351731651)
                ·
                  rfl

theorem cell20_865570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_865570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865570 prefixEnd_865570 := by exact prefixLift 865570
  have htrace : WordTrace (prefixWord ++ tailWord_865570) baseStart_865570 baseEnd_865570 := by
    simpa [prefixWord, tailWord_865570, baseEnd_865570] using wordTrace_append hprefix tailTrace_865570
  have hstable : (prefixWord ++ tailWord_865570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865570).length < 2 ^ (prefixWord ++ tailWord_865570).sum := by decide
  have hdescent : baseEnd_865570 < baseStart_865570 := by decide
  rcases family_descends (prefixWord ++ tailWord_865570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865584 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 2]
def baseStart_865584 : Nat := 118140960795 + 865584 * 2 ^ 59
def prefixEnd_865584 : Nat := 4983230072969 + 3 ^ 40 * 865584 * 2
def baseEnd_865584 : Nat := 395076123414619228728229

theorem tailTrace_865584 : CollatzResearch.WordTrace tailWord_865584 prefixEnd_865584 395076123414619228728229 := by
  unfold tailWord_865584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15785221048072236411481903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21046961397429648548642537 15785221048072236411481903)
  ·
    refine ⟨23677831572108354617222855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15785221048072236411481903 23677831572108354617222855)
    ·
      refine ⟨35516747358162531925834283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23677831572108354617222855 35516747358162531925834283)
      ·
        refine ⟨53275121037243797888751425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35516747358162531925834283 53275121037243797888751425)
        ·
          refine ⟨39956340777932848416563569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53275121037243797888751425 39956340777932848416563569)
          ·
            refine ⟨29967255583449636312422677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39956340777932848416563569 29967255583449636312422677)
            ·
              refine ⟨1404715105474201702144813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29967255583449636312422677 1404715105474201702144813)
              ·
                refine ⟨526768164552825638304305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1404715105474201702144813 526768164552825638304305)
                ·
                  refine ⟨395076123414619228728229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526768164552825638304305 395076123414619228728229)
                  ·
                    rfl

theorem cell20_865584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_865584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865584 prefixEnd_865584 := by exact prefixLift 865584
  have htrace : WordTrace (prefixWord ++ tailWord_865584) baseStart_865584 baseEnd_865584 := by
    simpa [prefixWord, tailWord_865584, baseEnd_865584] using wordTrace_append hprefix tailTrace_865584
  have hstable : (prefixWord ++ tailWord_865584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865584).length < 2 ^ (prefixWord ++ tailWord_865584).sum := by decide
  have hdescent : baseEnd_865584 < baseStart_865584 := by decide
  rcases family_descends (prefixWord ++ tailWord_865584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865590 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_865590 : Nat := 118140960795 + 865590 * 2 ^ 59
def prefixEnd_865590 : Nat := 4983230072969 + 3 ^ 40 * 865590 * 2
def baseEnd_865590 : Nat := 395078861978109874528205

theorem tailTrace_865590 : CollatzResearch.WordTrace tailWord_865590 prefixEnd_865590 395078861978109874528205 := by
  unfold tailWord_865590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1973166308382670990480139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21047107289415157231788149 1973166308382670990480139)
  ·
    refine ⟨2959749462574006485720209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1973166308382670990480139 2959749462574006485720209)
    ·
      refine ⟨2219812096930504864290157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2959749462574006485720209 2219812096930504864290157)
      ·
        refine ⟨832429536348939324108809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2219812096930504864290157 832429536348939324108809)
        ·
          refine ⟨624322152261704493081607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 832429536348939324108809 624322152261704493081607)
          ·
            refine ⟨936483228392556739622411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 624322152261704493081607 936483228392556739622411)
            ·
              refine ⟨1404724842588835109433617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936483228392556739622411 1404724842588835109433617)
              ·
                refine ⟨1053543631941626332075213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1404724842588835109433617 1053543631941626332075213)
                ·
                  refine ⟨395078861978109874528205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053543631941626332075213 395078861978109874528205)
                  ·
                    rfl

theorem cell20_865590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_865590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865590 prefixEnd_865590 := by exact prefixLift 865590
  have htrace : WordTrace (prefixWord ++ tailWord_865590) baseStart_865590 baseEnd_865590 := by
    simpa [prefixWord, tailWord_865590, baseEnd_865590] using wordTrace_append hprefix tailTrace_865590
  have hstable : (prefixWord ++ tailWord_865590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865590).length < 2 ^ (prefixWord ++ tailWord_865590).sum := by decide
  have hdescent : baseEnd_865590 < baseStart_865590 := by decide
  rcases family_descends (prefixWord ++ tailWord_865590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865598 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_865598 : Nat := 118140960795 + 865598 * 2 ^ 59
def prefixEnd_865598 : Nat := 4983230072969 + 3 ^ 40 * 865598 * 2
def baseEnd_865598 : Nat := 395082513396097402261505

theorem tailTrace_865598 : CollatzResearch.WordTrace tailWord_865598 prefixEnd_865598 395082513396097402261505 := by
  unfold tailWord_865598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946369089761719151746681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21047301812062502142648965 3946369089761719151746681)
  ·
    refine ⟨2959776817321289363810011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3946369089761719151746681 2959776817321289363810011)
    ·
      refine ⟨4439665225981934045715017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959776817321289363810011 4439665225981934045715017)
      ·
        refine ⟨3329748919486450534286263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4439665225981934045715017 3329748919486450534286263)
        ·
          refine ⟨4994623379229675801429395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3329748919486450534286263 4994623379229675801429395)
          ·
            refine ⟨7491935068844513702144093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4994623379229675801429395 7491935068844513702144093)
            ·
              refine ⟨2809475650816692638304035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7491935068844513702144093 2809475650816692638304035)
              ·
                refine ⟨4214213476225038957456053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809475650816692638304035 4214213476225038957456053)
                ·
                  refine ⟨395082513396097402261505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4214213476225038957456053 395082513396097402261505)
                  ·
                    rfl

theorem cell20_865598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_865598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865598 prefixEnd_865598 := by exact prefixLift 865598
  have htrace : WordTrace (prefixWord ++ tailWord_865598) baseStart_865598 baseEnd_865598 := by
    simpa [prefixWord, tailWord_865598, baseEnd_865598] using wordTrace_append hprefix tailTrace_865598
  have hstable : (prefixWord ++ tailWord_865598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865598).length < 2 ^ (prefixWord ++ tailWord_865598).sum := by decide
  have hdescent : baseEnd_865598 < baseStart_865598 := by decide
  rcases family_descends (prefixWord ++ tailWord_865598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865601 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 2]
def baseStart_865601 : Nat := 118140960795 + 865601 * 2 ^ 59
def prefixEnd_865601 : Nat := 4983230072969 + 3 ^ 40 * 865601 * 2
def baseEnd_865601 : Nat := 395083882677842725161493

theorem tailTrace_865601 : CollatzResearch.WordTrace tailWord_865601 prefixEnd_865601 395083882677842725161493 := by
  unfold tailWord_865601
  simp only [CollatzResearch.WordTrace]
  refine ⟨31571062137082884726332657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21047374758055256484221771 31571062137082884726332657)
  ·
    refine ⟨23678296602812163544749493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31571062137082884726332657 23678296602812163544749493)
    ·
      refine ⟨2219840306513640332320265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23678296602812163544749493 2219840306513640332320265)
      ·
        refine ⟨1664880229885230249240199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2219840306513640332320265 1664880229885230249240199)
        ·
          refine ⟨2497320344827845373860299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664880229885230249240199 2497320344827845373860299)
          ·
            refine ⟨3745980517241768060790449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2497320344827845373860299 3745980517241768060790449)
            ·
              refine ⟨2809485387931326045592837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3745980517241768060790449 2809485387931326045592837)
              ·
                refine ⟨526778510237123633548657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2809485387931326045592837 526778510237123633548657)
                ·
                  refine ⟨395083882677842725161493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526778510237123633548657 395083882677842725161493)
                  ·
                    rfl

theorem cell20_865601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 2].length) (baseStart_865601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865601 prefixEnd_865601 := by exact prefixLift 865601
  have htrace : WordTrace (prefixWord ++ tailWord_865601) baseStart_865601 baseEnd_865601 := by
    simpa [prefixWord, tailWord_865601, baseEnd_865601] using wordTrace_append hprefix tailTrace_865601
  have hstable : (prefixWord ++ tailWord_865601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865601).length < 2 ^ (prefixWord ++ tailWord_865601).sum := by decide
  have hdescent : baseEnd_865601 < baseStart_865601 := by decide
  rcases family_descends (prefixWord ++ tailWord_865601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865646 : List Nat := [4, 1, 2, 4, 1, 2, 6]
def baseStart_865646 : Nat := 118140960795 + 865646 * 2 ^ 59
def prefixEnd_865646 : Nat := 4983230072969 + 3 ^ 40 * 865646 * 2
def baseEnd_865646 : Nat := 43900491322669174295701

theorem tailTrace_865646 : CollatzResearch.WordTrace tailWord_865646 prefixEnd_865646 43900491322669174295701 := by
  unfold tailWord_865646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3946587927739982176465099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21048468947946571607813861 3946587927739982176465099)
  ·
    refine ⟨5919881891609973264697649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3946587927739982176465099 5919881891609973264697649)
    ·
      refine ⟨4439911418707479948523237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5919881891609973264697649 4439911418707479948523237)
      ·
        refine ⟨832483391007652490348107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4439911418707479948523237 832483391007652490348107)
        ·
          refine ⟨1248725086511478735522161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 832483391007652490348107 1248725086511478735522161)
          ·
            refine ⟨936543814883609051641621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1248725086511478735522161 936543814883609051641621)
            ·
              refine ⟨43900491322669174295701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 936543814883609051641621 43900491322669174295701)
              ·
                rfl

theorem cell20_865646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 6].length) (baseStart_865646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865646 prefixEnd_865646 := by exact prefixLift 865646
  have htrace : WordTrace (prefixWord ++ tailWord_865646) baseStart_865646 baseEnd_865646 := by
    simpa [prefixWord, tailWord_865646, baseEnd_865646] using wordTrace_append hprefix tailTrace_865646
  have hstable : (prefixWord ++ tailWord_865646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865646).length < 2 ^ (prefixWord ++ tailWord_865646).sum := by decide
  have hdescent : baseEnd_865646 < baseStart_865646 := by decide
  rcases family_descends (prefixWord ++ tailWord_865646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865657 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 5]
def baseStart_865657 : Nat := 118140960795 + 865657 * 2 ^ 59
def prefixEnd_865657 : Nat := 4983230072969 + 3 ^ 40 * 865657 * 2
def baseEnd_865657 : Nat := 395109442603755419294597

theorem tailTrace_865657 : CollatzResearch.WordTrace tailWord_865657 prefixEnd_865657 395109442603755419294597 := by
  unfold tailWord_865657
  simp only [CollatzResearch.WordTrace]
  refine ⟨31573104624880006290371225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21048736416586670860247483 31573104624880006290371225)
  ·
    refine ⟨23679828468660004717778419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31573104624880006290371225 23679828468660004717778419)
    ·
      refine ⟨35519742702990007076667629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23679828468660004717778419 35519742702990007076667629)
      ·
        refine ⟨13319903513621252653750361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35519742702990007076667629 13319903513621252653750361)
        ·
          refine ⟨9989927635215939490312771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13319903513621252653750361 9989927635215939490312771)
          ·
            refine ⟨14984891452823909235469157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9989927635215939490312771 14984891452823909235469157)
            ·
              refine ⟨2809667147404482981650467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14984891452823909235469157 2809667147404482981650467)
              ·
                refine ⟨4214500721106724472475701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2809667147404482981650467 4214500721106724472475701)
                ·
                  refine ⟨395109442603755419294597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4214500721106724472475701 395109442603755419294597)
                  ·
                    rfl

theorem cell20_865657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_865657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865657 prefixEnd_865657 := by exact prefixLift 865657
  have htrace : WordTrace (prefixWord ++ tailWord_865657) baseStart_865657 baseEnd_865657 := by
    simpa [prefixWord, tailWord_865657, baseEnd_865657] using wordTrace_append hprefix tailTrace_865657
  have hstable : (prefixWord ++ tailWord_865657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865657).length < 2 ^ (prefixWord ++ tailWord_865657).sum := by decide
  have hdescent : baseEnd_865657 < baseStart_865657 := by decide
  rcases family_descends (prefixWord ++ tailWord_865657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865767 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 3]
def baseStart_865767 : Nat := 118140960795 + 865767 * 2 ^ 59
def prefixEnd_865767 : Nat := 4983230072969 + 3 ^ 40 * 865767 * 2
def baseEnd_865767 : Nat := 395159649601083925627481

theorem tailTrace_865767 : CollatzResearch.WordTrace tailWord_865767 prefixEnd_865767 395159649601083925627481 := by
  unfold tailWord_865767
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577116654481495076875555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21051411102987663384583703 31577116654481495076875555)
  ·
    refine ⟨47365674981722242615313333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31577116654481495076875555 47365674981722242615313333)
    ·
      refine ⟨4440532029536460245185625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 47365674981722242615313333 4440532029536460245185625)
      ·
        refine ⟨3330399022152345183889219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4440532029536460245185625 3330399022152345183889219)
        ·
          refine ⟨4995598533228517775833829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3330399022152345183889219 4995598533228517775833829)
          ·
            refine ⟨936674724980347082968843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4995598533228517775833829 936674724980347082968843)
            ·
              refine ⟨1405012087470520624453265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936674724980347082968843 1405012087470520624453265)
              ·
                refine ⟨1053759065602890468339949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405012087470520624453265 1053759065602890468339949)
                ·
                  refine ⟨395159649601083925627481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053759065602890468339949 395159649601083925627481)
                  ·
                    rfl

theorem cell20_865767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 3].length) (baseStart_865767 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865767 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865767 prefixEnd_865767 := by exact prefixLift 865767
  have htrace : WordTrace (prefixWord ++ tailWord_865767) baseStart_865767 baseEnd_865767 := by
    simpa [prefixWord, tailWord_865767, baseEnd_865767] using wordTrace_append hprefix tailTrace_865767
  have hstable : (prefixWord ++ tailWord_865767).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865767).length < 2 ^ (prefixWord ++ tailWord_865767).sum := by decide
  have hdescent : baseEnd_865767 < baseStart_865767 := by decide
  rcases family_descends (prefixWord ++ tailWord_865767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865771 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 3]
def baseStart_865771 : Nat := 118140960795 + 865771 * 2 ^ 59
def prefixEnd_865771 : Nat := 4983230072969 + 3 ^ 40 * 865771 * 2
def baseEnd_865771 : Nat := 395161475310077689494131

theorem tailTrace_865771 : CollatzResearch.WordTrace tailWord_865771 prefixEnd_865771 395161475310077689494131 := by
  unfold tailWord_865771
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577262546467003760021167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21051508364311335840014111 31577262546467003760021167)
  ·
    refine ⟨47365893819700505640031751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31577262546467003760021167 47365893819700505640031751)
    ·
      refine ⟨71048840729550758460047627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47365893819700505640031751 71048840729550758460047627)
      ·
        refine ⟨106573261094326137690071441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71048840729550758460047627 106573261094326137690071441)
        ·
          refine ⟨79929945820744603267553581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106573261094326137690071441 79929945820744603267553581)
          ·
            refine ⟨29973729682779226225332593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79929945820744603267553581 29973729682779226225332593)
            ·
              refine ⟨22480297262084419668999445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29973729682779226225332593 22480297262084419668999445)
              ·
                refine ⟨1053763934160207171984349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22480297262084419668999445 1053763934160207171984349)
                ·
                  refine ⟨395161475310077689494131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053763934160207171984349 395161475310077689494131)
                  ·
                    rfl

theorem cell20_865771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 3].length) (baseStart_865771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865771 prefixEnd_865771 := by exact prefixLift 865771
  have htrace : WordTrace (prefixWord ++ tailWord_865771) baseStart_865771 baseEnd_865771 := by
    simpa [prefixWord, tailWord_865771, baseEnd_865771] using wordTrace_append hprefix tailTrace_865771
  have hstable : (prefixWord ++ tailWord_865771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865771).length < 2 ^ (prefixWord ++ tailWord_865771).sum := by decide
  have hdescent : baseEnd_865771 < baseStart_865771 := by decide
  rcases family_descends (prefixWord ++ tailWord_865771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865774 : List Nat := [4, 1, 2, 1, 2, 1, 1, 6, 2]
def baseStart_865774 : Nat := 118140960795 + 865774 * 2 ^ 59
def prefixEnd_865774 : Nat := 4983230072969 + 3 ^ 40 * 865774 * 2
def baseEnd_865774 : Nat := 395162844591823012394119

theorem tailTrace_865774 : CollatzResearch.WordTrace tailWord_865774 prefixEnd_865774 395162844591823012394119 := by
  unfold tailWord_865774
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947171495682016909047547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21051581310304090181586917 3947171495682016909047547)
  ·
    refine ⟨5920757243523025363571321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947171495682016909047547 5920757243523025363571321)
    ·
      refine ⟨4440567932642269022678491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5920757243523025363571321 4440567932642269022678491)
      ·
        refine ⟨6660851898963403534017737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4440567932642269022678491 6660851898963403534017737)
        ·
          refine ⟨4995638924222552650513303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6660851898963403534017737 4995638924222552650513303)
          ·
            refine ⟨7493458386333828975769955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4995638924222552650513303 7493458386333828975769955)
            ·
              refine ⟨11240187579500743463654933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7493458386333828975769955 11240187579500743463654933)
              ·
                refine ⟨526883792789097349858825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11240187579500743463654933 526883792789097349858825)
                ·
                  refine ⟨395162844591823012394119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526883792789097349858825 395162844591823012394119)
                  ·
                    rfl

theorem cell20_865774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_865774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865774 prefixEnd_865774 := by exact prefixLift 865774
  have htrace : WordTrace (prefixWord ++ tailWord_865774) baseStart_865774 baseEnd_865774 := by
    simpa [prefixWord, tailWord_865774, baseEnd_865774] using wordTrace_append hprefix tailTrace_865774
  have hstable : (prefixWord ++ tailWord_865774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865774).length < 2 ^ (prefixWord ++ tailWord_865774).sum := by decide
  have hdescent : baseEnd_865774 < baseStart_865774 := by decide
  rcases family_descends (prefixWord ++ tailWord_865774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865785 : List Nat := [1, 2, 1, 3, 1, 2, 1, 9]
def baseStart_865785 : Nat := 118140960795 + 865785 * 2 ^ 59
def prefixEnd_865785 : Nat := 4983230072969 + 3 ^ 40 * 865785 * 2
def baseEnd_865785 : Nat := 131722621763851954342469

theorem tailTrace_865785 : CollatzResearch.WordTrace tailWord_865785 prefixEnd_865785 131722621763851954342469 := by
  unfold tailWord_865785
  simp only [CollatzResearch.WordTrace]
  refine ⟨31577773168416284151030809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21051848778944189434020539 31577773168416284151030809)
  ·
    refine ⟨23683329876312213113273107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31577773168416284151030809 23683329876312213113273107)
    ·
      refine ⟨35524994814468319669909661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23683329876312213113273107 35524994814468319669909661)
      ·
        refine ⟨13321873055425619876216123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35524994814468319669909661 13321873055425619876216123)
        ·
          refine ⟨19982809583138429814324185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13321873055425619876216123 19982809583138429814324185)
          ·
            refine ⟨14987107187353822360743139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19982809583138429814324185 14987107187353822360743139)
            ·
              refine ⟨22480660781030733541114709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14987107187353822360743139 22480660781030733541114709)
              ·
                refine ⟨131722621763851954342469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22480660781030733541114709 131722621763851954342469)
                ·
                  rfl

theorem cell20_865785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 9].length) (baseStart_865785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865785 prefixEnd_865785 := by exact prefixLift 865785
  have htrace : WordTrace (prefixWord ++ tailWord_865785) baseStart_865785 baseEnd_865785 := by
    simpa [prefixWord, tailWord_865785, baseEnd_865785] using wordTrace_append hprefix tailTrace_865785
  have hstable : (prefixWord ++ tailWord_865785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865785).length < 2 ^ (prefixWord ++ tailWord_865785).sum := by decide
  have hdescent : baseEnd_865785 < baseStart_865785 := by decide
  rcases family_descends (prefixWord ++ tailWord_865785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865802 : List Nat := [3, 1, 2, 2, 2, 3, 1, 6]
def baseStart_865802 : Nat := 118140960795 + 865802 * 2 ^ 59
def prefixEnd_865802 : Nat := 4983230072969 + 3 ^ 40 * 865802 * 2
def baseEnd_865802 : Nat := 131725208184926453153557

theorem tailTrace_865802 : CollatzResearch.WordTrace tailWord_865802 prefixEnd_865802 131725208184926453153557 := by
  unfold tailWord_865802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7894598302338674013599915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21052262139569797369599773 7894598302338674013599915)
  ·
    refine ⟨11841897453508011020399873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7894598302338674013599915 11841897453508011020399873)
    ·
      refine ⟨8881423090131008265299905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11841897453508011020399873 8881423090131008265299905)
      ·
        refine ⟨6661067317598256198974929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8881423090131008265299905 6661067317598256198974929)
        ·
          refine ⟨4995800488198692149231197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6661067317598256198974929 4995800488198692149231197)
          ·
            refine ⟨1873425183074509555961699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4995800488198692149231197 1873425183074509555961699)
            ·
              refine ⟨2810137774611764333942549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1873425183074509555961699 2810137774611764333942549)
              ·
                refine ⟨131725208184926453153557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2810137774611764333942549 131725208184926453153557)
                ·
                  rfl

theorem cell20_865802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_865802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865802 prefixEnd_865802 := by exact prefixLift 865802
  have htrace : WordTrace (prefixWord ++ tailWord_865802) baseStart_865802 baseEnd_865802 := by
    simpa [prefixWord, tailWord_865802, baseEnd_865802] using wordTrace_append hprefix tailTrace_865802
  have hstable : (prefixWord ++ tailWord_865802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865802).length < 2 ^ (prefixWord ++ tailWord_865802).sum := by decide
  have hdescent : baseEnd_865802 < baseStart_865802 := by decide
  rcases family_descends (prefixWord ++ tailWord_865802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865823 : List Nat := [1, 1, 2, 4, 1, 1, 10]
def baseStart_865823 : Nat := 118140960795 + 865823 * 2 ^ 59
def prefixEnd_865823 : Nat := 4983230072969 + 3 ^ 40 * 865823 * 2
def baseEnd_865823 : Nat := 43909467725221846640065

theorem tailTrace_865823 : CollatzResearch.WordTrace tailWord_865823 prefixEnd_865823 43909467725221846640065 := by
  unfold tailWord_865823
  simp only [CollatzResearch.WordTrace]
  refine ⟨31579159142278616640914123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21052772761519077760609415 31579159142278616640914123)
  ·
    refine ⟨47368738713417924961371185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31579159142278616640914123 47368738713417924961371185)
    ·
      refine ⟨35526554035063443721028389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47368738713417924961371185 35526554035063443721028389)
      ·
        refine ⟨6661228881574395697692823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35526554035063443721028389 6661228881574395697692823)
        ·
          refine ⟨9991843322361593546539235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6661228881574395697692823 9991843322361593546539235)
          ·
            refine ⟨14987764983542390319808853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9991843322361593546539235 14987764983542390319808853)
            ·
              refine ⟨43909467725221846640065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14987764983542390319808853 43909467725221846640065)
              ·
                rfl

theorem cell20_865823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 10].length) (baseStart_865823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865823 prefixEnd_865823 := by exact prefixLift 865823
  have htrace : WordTrace (prefixWord ++ tailWord_865823) baseStart_865823 baseEnd_865823 := by
    simpa [prefixWord, tailWord_865823, baseEnd_865823] using wordTrace_append hprefix tailTrace_865823
  have hstable : (prefixWord ++ tailWord_865823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865823).length < 2 ^ (prefixWord ++ tailWord_865823).sum := by decide
  have hdescent : baseEnd_865823 < baseStart_865823 := by decide
  rcases family_descends (prefixWord ++ tailWord_865823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865843 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 3]
def baseStart_865843 : Nat := 118140960795 + 865843 * 2 ^ 59
def prefixEnd_865843 : Nat := 4983230072969 + 3 ^ 40 * 865843 * 2
def baseEnd_865843 : Nat := 395194338071965439093837

theorem tailTrace_865843 : CollatzResearch.WordTrace tailWord_865843 prefixEnd_865843 395194338071965439093837 := by
  unfold tailWord_865843
  simp only [CollatzResearch.WordTrace]
  refine ⟨31579888602206160056642183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21053259068137440037761455 31579888602206160056642183)
  ·
    refine ⟨47369832903309240084963275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31579888602206160056642183 47369832903309240084963275)
    ·
      refine ⟨71054749354963860127444913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47369832903309240084963275 71054749354963860127444913)
      ·
        refine ⟨53291062016222895095583685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71054749354963860127444913 53291062016222895095583685)
        ·
          refine ⟨9992074128041792830421941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53291062016222895095583685 9992074128041792830421941)
          ·
            refine ⟨936756949503918077852057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9992074128041792830421941 936756949503918077852057)
            ·
              refine ⟨702567712127938558389043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936756949503918077852057 702567712127938558389043)
              ·
                refine ⟨1053851568191907837583565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702567712127938558389043 1053851568191907837583565)
                ·
                  refine ⟨395194338071965439093837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1053851568191907837583565 395194338071965439093837)
                  ·
                    rfl

theorem cell20_865843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 3].length) (baseStart_865843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865843 prefixEnd_865843 := by exact prefixLift 865843
  have htrace : WordTrace (prefixWord ++ tailWord_865843) baseStart_865843 baseEnd_865843 := by
    simpa [prefixWord, tailWord_865843, baseEnd_865843] using wordTrace_append hprefix tailTrace_865843
  have hstable : (prefixWord ++ tailWord_865843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865843).length < 2 ^ (prefixWord ++ tailWord_865843).sum := by decide
  have hdescent : baseEnd_865843 < baseStart_865843 := by decide
  rcases family_descends (prefixWord ++ tailWord_865843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865861 : List Nat := [1, 3, 1, 1, 1, 4, 1, 8]
def baseStart_865861 : Nat := 118140960795 + 865861 * 2 ^ 59
def prefixEnd_865861 : Nat := 4983230072969 + 3 ^ 40 * 865861 * 2
def baseEnd_865861 : Nat := 131734184587479125497921

theorem tailTrace_865861 : CollatzResearch.WordTrace tailWord_865861 prefixEnd_865861 131734184587479125497921 := by
  unfold tailWord_865861
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580545116140949130797437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21053696744093966087198291 31580545116140949130797437)
  ·
    refine ⟨11842704418552855924049039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31580545116140949130797437 11842704418552855924049039)
    ·
      refine ⟨17764056627829283886073559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11842704418552855924049039 17764056627829283886073559)
      ·
        refine ⟨26646084941743925829110339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17764056627829283886073559 26646084941743925829110339)
        ·
          refine ⟨39969127412615888743665509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26646084941743925829110339 39969127412615888743665509)
          ·
            refine ⟨7494211389865479139437283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39969127412615888743665509 7494211389865479139437283)
            ·
              refine ⟨11241317084798218709155925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7494211389865479139437283 11241317084798218709155925)
              ·
                refine ⟨131734184587479125497921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11241317084798218709155925 131734184587479125497921)
                ·
                  rfl

theorem cell20_865861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 8].length) (baseStart_865861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865861 prefixEnd_865861 := by exact prefixLift 865861
  have htrace : WordTrace (prefixWord ++ tailWord_865861) baseStart_865861 baseEnd_865861 := by
    simpa [prefixWord, tailWord_865861, baseEnd_865861] using wordTrace_append hprefix tailTrace_865861
  have hstable : (prefixWord ++ tailWord_865861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865861).length < 2 ^ (prefixWord ++ tailWord_865861).sum := by decide
  have hdescent : baseEnd_865861 < baseStart_865861 := by decide
  rcases family_descends (prefixWord ++ tailWord_865861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865871 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 2]
def baseStart_865871 : Nat := 118140960795 + 865871 * 2 ^ 59
def prefixEnd_865871 : Nat := 4983230072969 + 3 ^ 40 * 865871 * 2
def baseEnd_865871 : Nat := 395207118034921786160389

theorem tailTrace_865871 : CollatzResearch.WordTrace tailWord_865871 prefixEnd_865871 395207118034921786160389 := by
  unfold tailWord_865871
  simp only [CollatzResearch.WordTrace]
  refine ⟨31580909846104720838661467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21053939897403147225774311 31580909846104720838661467)
  ·
    refine ⟨47371364769157081257992201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31580909846104720838661467 47371364769157081257992201)
    ·
      refine ⟨35528523576867810943494151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47371364769157081257992201 35528523576867810943494151)
      ·
        refine ⟨53292785365301716415241227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35528523576867810943494151 53292785365301716415241227)
        ·
          refine ⟨79939178047952574622861841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53292785365301716415241227 79939178047952574622861841)
          ·
            refine ⟨59954383535964430967146381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79939178047952574622861841 59954383535964430967146381)
            ·
              refine ⟨22482893825986661612679893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59954383535964430967146381 22482893825986661612679893)
              ·
                refine ⟨526942824046562381547185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 22482893825986661612679893 526942824046562381547185)
                ·
                  refine ⟨395207118034921786160389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526942824046562381547185 395207118034921786160389)
                  ·
                    rfl

theorem cell20_865871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 2].length) (baseStart_865871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865871 prefixEnd_865871 := by exact prefixLift 865871
  have htrace : WordTrace (prefixWord ++ tailWord_865871) baseStart_865871 baseEnd_865871 := by
    simpa [prefixWord, tailWord_865871, baseEnd_865871] using wordTrace_append hprefix tailTrace_865871
  have hstable : (prefixWord ++ tailWord_865871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865871).length < 2 ^ (prefixWord ++ tailWord_865871).sum := by decide
  have hdescent : baseEnd_865871 < baseStart_865871 := by decide
  rcases family_descends (prefixWord ++ tailWord_865871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865884 : List Nat := [2, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_865884 : Nat := 118140960795 + 865884 * 2 ^ 59
def prefixEnd_865884 : Nat := 4983230072969 + 3 ^ 40 * 865884 * 2
def baseEnd_865884 : Nat := 395213051589151518727003

theorem tailTrace_865884 : CollatzResearch.WordTrace tailWord_865884 prefixEnd_865884 395213051589151518727003 := by
  unfold tailWord_865884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15790691997528812029442353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21054255996705082705923137 15790691997528812029442353)
  ·
    refine ⟨11843018998146609022081765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15790691997528812029442353 11843018998146609022081765)
    ·
      refine ⟨2220566062152489191640331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11843018998146609022081765 2220566062152489191640331)
      ·
        refine ⟨3330849093228733787460497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2220566062152489191640331 3330849093228733787460497)
        ·
          refine ⟨2498136819921550340595373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3330849093228733787460497 2498136819921550340595373)
          ·
            refine ⟨936801307470581377723265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2498136819921550340595373 936801307470581377723265)
            ·
              refine ⟨702600980602936033292449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 936801307470581377723265 702600980602936033292449)
              ·
                refine ⟨526950735452202024969337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702600980602936033292449 526950735452202024969337)
                ·
                  refine ⟨395213051589151518727003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 526950735452202024969337 395213051589151518727003)
                  ·
                    rfl

theorem cell20_865884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_865884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865884 prefixEnd_865884 := by exact prefixLift 865884
  have htrace : WordTrace (prefixWord ++ tailWord_865884) baseStart_865884 baseEnd_865884 := by
    simpa [prefixWord, tailWord_865884, baseEnd_865884] using wordTrace_append hprefix tailTrace_865884
  have hstable : (prefixWord ++ tailWord_865884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865884).length < 2 ^ (prefixWord ++ tailWord_865884).sum := by decide
  have hdescent : baseEnd_865884 < baseStart_865884 := by decide
  rcases family_descends (prefixWord ++ tailWord_865884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865909 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 6]
def baseStart_865909 : Nat := 118140960795 + 865909 * 2 ^ 59
def prefixEnd_865909 : Nat := 4983230072969 + 3 ^ 40 * 865909 * 2
def baseEnd_865909 : Nat := 395224462270362542893567

theorem tailTrace_865909 : CollatzResearch.WordTrace tailWord_865909 prefixEnd_865909 395224462270362542893567 := by
  unfold tailWord_865909
  simp only [CollatzResearch.WordTrace]
  refine ⟨31582295819967053328544781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21054863879978035552363187 31582295819967053328544781)
  ·
    refine ⟨11843360932487644998204293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31582295819967053328544781 11843360932487644998204293)
    ·
      refine ⟨2220630174841433437163305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11843360932487644998204293 2220630174841433437163305)
      ·
        refine ⟨1665472631131075077872479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2220630174841433437163305 1665472631131075077872479)
        ·
          refine ⟨2498208946696612616808719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665472631131075077872479 2498208946696612616808719)
          ·
            refine ⟨3747313420044918925213079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2498208946696612616808719 3747313420044918925213079)
            ·
              refine ⟨5620970130067378387819619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3747313420044918925213079 5620970130067378387819619)
              ·
                refine ⟨8431455195101067581729429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5620970130067378387819619 8431455195101067581729429)
                ·
                  refine ⟨395224462270362542893567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8431455195101067581729429 395224462270362542893567)
                  ·
                    rfl

theorem cell20_865909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_865909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865909 prefixEnd_865909 := by exact prefixLift 865909
  have htrace : WordTrace (prefixWord ++ tailWord_865909) baseStart_865909 baseEnd_865909 := by
    simpa [prefixWord, tailWord_865909, baseEnd_865909] using wordTrace_append hprefix tailTrace_865909
  have hstable : (prefixWord ++ tailWord_865909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865909).length < 2 ^ (prefixWord ++ tailWord_865909).sum := by decide
  have hdescent : baseEnd_865909 < baseStart_865909 := by decide
  rcases family_descends (prefixWord ++ tailWord_865909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_865968 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_865968 : Nat := 118140960795 + 865968 * 2 ^ 59
def prefixEnd_865968 : Nat := 4983230072969 + 3 ^ 40 * 865968 * 2
def baseEnd_865968 : Nat := 395251391478020559926659

theorem tailTrace_865968 : CollatzResearch.WordTrace tailWord_865968 prefixEnd_865968 395251391478020559926659 := by
  unfold tailWord_865968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15792223863376653202471279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21056298484502204269961705 15792223863376653202471279)
  ·
    refine ⟨23688335795064979803706919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15792223863376653202471279 23688335795064979803706919)
    ·
      refine ⟨35532503692597469705560379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23688335795064979803706919 35532503692597469705560379)
      ·
        refine ⟨53298755538896204558340569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35532503692597469705560379 53298755538896204558340569)
        ·
          refine ⟨39974066654172153418755427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53298755538896204558340569 39974066654172153418755427)
          ·
            refine ⟨59961099981258230128133141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39974066654172153418755427 59961099981258230128133141)
            ·
              refine ⟨2810676561621479537256241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59961099981258230128133141 2810676561621479537256241)
              ·
                refine ⟨2108007421216109652942181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2810676561621479537256241 2108007421216109652942181)
                ·
                  refine ⟨395251391478020559926659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108007421216109652942181 395251391478020559926659)
                  ·
                    rfl

theorem cell20_865968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_865968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_865968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_865968 prefixEnd_865968 := by exact prefixLift 865968
  have htrace : WordTrace (prefixWord ++ tailWord_865968) baseStart_865968 baseEnd_865968 := by
    simpa [prefixWord, tailWord_865968, baseEnd_865968] using wordTrace_append hprefix tailTrace_865968
  have hstable : (prefixWord ++ tailWord_865968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_865968).length < 2 ^ (prefixWord ++ tailWord_865968).sum := by decide
  have hdescent : baseEnd_865968 < baseStart_865968 := by decide
  rcases family_descends (prefixWord ++ tailWord_865968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866002 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_866002 : Nat := 118140960795 + 866002 * 2 ^ 59
def prefixEnd_866002 : Nat := 4983230072969 + 3 ^ 40 * 866002 * 2
def baseEnd_866002 : Nat := 395266910004467552793187

theorem tailTrace_866002 : CollatzResearch.WordTrace tailWord_866002 prefixEnd_866002 395266910004467552793187 := by
  unfold tailWord_866002
  simp only [CollatzResearch.WordTrace]
  refine ⟨7896421952157532552920065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21057125205753420141120173 7896421952157532552920065)
  ·
    refine ⟨5922316464118149414690049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7896421952157532552920065 5922316464118149414690049)
    ·
      refine ⟨4441737348088612061017537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5922316464118149414690049 4441737348088612061017537)
      ·
        refine ⟨3331303011066459045763153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4441737348088612061017537 3331303011066459045763153)
        ·
          refine ⟨2498477258299844284322365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3331303011066459045763153 2498477258299844284322365)
          ·
            refine ⟨936928971862441606620887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2498477258299844284322365 936928971862441606620887)
            ·
              refine ⟨1405393457793662409931331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 936928971862441606620887 1405393457793662409931331)
              ·
                refine ⟨2108090186690493614896997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405393457793662409931331 2108090186690493614896997)
                ·
                  refine ⟨395266910004467552793187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108090186690493614896997 395266910004467552793187)
                  ·
                    rfl

theorem cell20_866002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_866002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866002 prefixEnd_866002 := by exact prefixLift 866002
  have htrace : WordTrace (prefixWord ++ tailWord_866002) baseStart_866002 baseEnd_866002 := by
    simpa [prefixWord, tailWord_866002, baseEnd_866002] using wordTrace_append hprefix tailTrace_866002
  have hstable : (prefixWord ++ tailWord_866002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866002).length < 2 ^ (prefixWord ++ tailWord_866002).sum := by decide
  have hdescent : baseEnd_866002 < baseStart_866002 := by decide
  rcases family_descends (prefixWord ++ tailWord_866002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866016 : List Nat := [2, 1, 1, 3, 1, 2, 6, 1, 3]
def baseStart_866016 : Nat := 118140960795 + 866016 * 2 ^ 59
def prefixEnd_866016 : Nat := 4983230072969 + 3 ^ 40 * 866016 * 2
def baseEnd_866016 : Nat := 395273299985945726326463

theorem tailTrace_866016 : CollatzResearch.WordTrace tailWord_866016 prefixEnd_866016 395273299985945726326463 := by
  unfold tailWord_866016
  simp only [CollatzResearch.WordTrace]
  refine ⟨15793099215289705301344951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21057465620386273735126601 15793099215289705301344951)
  ·
    refine ⟨23689648822934557952017427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15793099215289705301344951 23689648822934557952017427)
    ·
      refine ⟨35534473234401836928026141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23689648822934557952017427 35534473234401836928026141)
      ·
        refine ⟨13325427462900688848009803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35534473234401836928026141 13325427462900688848009803)
        ·
          refine ⟨19988141194351033272014705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13325427462900688848009803 19988141194351033272014705)
          ·
            refine ⟨14991105895763274954011029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19988141194351033272014705 14991105895763274954011029)
            ·
              refine ⟨702708088863903513469267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14991105895763274954011029 702708088863903513469267)
              ·
                refine ⟨1054062133295855270203901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 702708088863903513469267 1054062133295855270203901)
                ·
                  refine ⟨395273299985945726326463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054062133295855270203901 395273299985945726326463)
                  ·
                    rfl

theorem cell20_866016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_866016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866016 prefixEnd_866016 := by exact prefixLift 866016
  have htrace : WordTrace (prefixWord ++ tailWord_866016) baseStart_866016 baseEnd_866016 := by
    simpa [prefixWord, tailWord_866016, baseEnd_866016] using wordTrace_append hprefix tailTrace_866016
  have hstable : (prefixWord ++ tailWord_866016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866016).length < 2 ^ (prefixWord ++ tailWord_866016).sum := by decide
  have hdescent : baseEnd_866016 < baseStart_866016 := by decide
  rcases family_descends (prefixWord ++ tailWord_866016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866109 : List Nat := [1, 4, 1, 4, 1, 3, 1, 2, 3]
def baseStart_866109 : Nat := 118140960795 + 866109 * 2 ^ 59
def prefixEnd_866109 : Nat := 4983230072969 + 3 ^ 40 * 866109 * 2
def baseEnd_866109 : Nat := 395315747720050736226083

theorem tailTrace_866109 : CollatzResearch.WordTrace tailWord_866109 prefixEnd_866109 395315747720050736226083 := by
  unfold tailWord_866109
  simp only [CollatzResearch.WordTrace]
  refine ⟨31589590419242487485825381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21059726946161658323883587 31589590419242487485825381)
  ·
    refine ⟨5923048203607966403592259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31589590419242487485825381 5923048203607966403592259)
    ·
      refine ⟨8884572305411949605388389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5923048203607966403592259 8884572305411949605388389)
      ·
        refine ⟨1665857307264740551010323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8884572305411949605388389 1665857307264740551010323)
        ·
          refine ⟨2498785960897110826515485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665857307264740551010323 2498785960897110826515485)
          ·
            refine ⟨937044735336416559943307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2498785960897110826515485 937044735336416559943307)
            ·
              refine ⟨1405567103004624839914961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937044735336416559943307 1405567103004624839914961)
              ·
                refine ⟨1054175327253468629936221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405567103004624839914961 1054175327253468629936221)
                ·
                  refine ⟨395315747720050736226083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054175327253468629936221 395315747720050736226083)
                  ·
                    rfl

theorem cell20_866109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_866109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866109 prefixEnd_866109 := by exact prefixLift 866109
  have htrace : WordTrace (prefixWord ++ tailWord_866109) baseStart_866109 baseEnd_866109 := by
    simpa [prefixWord, tailWord_866109, baseEnd_866109] using wordTrace_append hprefix tailTrace_866109
  have hstable : (prefixWord ++ tailWord_866109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866109).length < 2 ^ (prefixWord ++ tailWord_866109).sum := by decide
  have hdescent : baseEnd_866109 < baseStart_866109 := by decide
  rcases family_descends (prefixWord ++ tailWord_866109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866120 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 4]
def baseStart_866120 : Nat := 118140960795 + 866120 * 2 ^ 59
def prefixEnd_866120 : Nat := 4983230072969 + 3 ^ 40 * 866120 * 2
def baseEnd_866120 : Nat := 395320768419783586859371

theorem tailTrace_866120 : CollatzResearch.WordTrace tailWord_866120 prefixEnd_866120 395320768419783586859371 := by
  unfold tailWord_866120
  simp only [CollatzResearch.WordTrace]
  refine ⟨15794995811101318182237907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21059994414801757576317209 15794995811101318182237907)
  ·
    refine ⟨23692493716651977273356861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15794995811101318182237907 23692493716651977273356861)
    ·
      refine ⟨8884685143744491477508823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23692493716651977273356861 8884685143744491477508823)
      ·
        refine ⟨13327027715616737216263235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8884685143744491477508823 13327027715616737216263235)
        ·
          refine ⟨19990541573425105824394853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13327027715616737216263235 19990541573425105824394853)
          ·
            refine ⟨3748226545017207342074035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19990541573425105824394853 3748226545017207342074035)
            ·
              refine ⟨5622339817525811013111053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3748226545017207342074035 5622339817525811013111053)
              ·
                refine ⟨2108377431572179129916645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5622339817525811013111053 2108377431572179129916645)
                ·
                  refine ⟨395320768419783586859371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108377431572179129916645 395320768419783586859371)
                  ·
                    rfl

theorem cell20_866120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_866120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866120 prefixEnd_866120 := by exact prefixLift 866120
  have htrace : WordTrace (prefixWord ++ tailWord_866120) baseStart_866120 baseEnd_866120 := by
    simpa [prefixWord, tailWord_866120, baseEnd_866120] using wordTrace_append hprefix tailTrace_866120
  have hstable : (prefixWord ++ tailWord_866120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866120).length < 2 ^ (prefixWord ++ tailWord_866120).sum := by decide
  have hdescent : baseEnd_866120 < baseStart_866120 := by decide
  rcases family_descends (prefixWord ++ tailWord_866120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866140 : List Nat := [2, 2, 4, 2, 2, 2, 2, 4]
def baseStart_866140 : Nat := 118140960795 + 866140 * 2 ^ 59
def prefixEnd_866140 : Nat := 4983230072969 + 3 ^ 40 * 866140 * 2
def baseEnd_866140 : Nat := 131776632321584135397541

theorem tailTrace_866140 : CollatzResearch.WordTrace tailWord_866140 prefixEnd_866140 131776632321584135397541 := by
  unfold tailWord_866140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15795360541065089890101937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21060480721420119853469249 15795360541065089890101937)
  ·
    refine ⟨11846520405798817417576453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15795360541065089890101937 11846520405798817417576453)
    ·
      refine ⟨2221222576087278265795585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11846520405798817417576453 2221222576087278265795585)
      ·
        refine ⟨1665916932065458699346689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2221222576087278265795585 1665916932065458699346689)
        ·
          refine ⟨1249437699049094024510017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1665916932065458699346689 1249437699049094024510017)
          ·
            refine ⟨937078274286820518382513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249437699049094024510017 937078274286820518382513)
            ·
              refine ⟨702808705715115388786885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937078274286820518382513 702808705715115388786885)
              ·
                refine ⟨131776632321584135397541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702808705715115388786885 131776632321584135397541)
                ·
                  rfl

theorem cell20_866140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_866140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866140 prefixEnd_866140 := by exact prefixLift 866140
  have htrace : WordTrace (prefixWord ++ tailWord_866140) baseStart_866140 baseEnd_866140 := by
    simpa [prefixWord, tailWord_866140, baseEnd_866140] using wordTrace_append hprefix tailTrace_866140
  have hstable : (prefixWord ++ tailWord_866140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866140).length < 2 ^ (prefixWord ++ tailWord_866140).sum := by decide
  have hdescent : baseEnd_866140 < baseStart_866140 := by decide
  rcases family_descends (prefixWord ++ tailWord_866140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866144 : List Nat := [2, 1, 1, 3, 3, 2, 4, 4]
def baseStart_866144 : Nat := 118140960795 + 866144 * 2 ^ 59
def prefixEnd_866144 : Nat := 4983230072969 + 3 ^ 40 * 866144 * 2
def baseEnd_866144 : Nat := 131777240891248723353091

theorem tailTrace_866144 : CollatzResearch.WordTrace tailWord_866144 prefixEnd_866144 131777240891248723353091 := by
  unfold tailWord_866144
  simp only [CollatzResearch.WordTrace]
  refine ⟨15795433487057844231674743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21060577982743792308899657 15795433487057844231674743)
  ·
    refine ⟨23693150230586766347512115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15795433487057844231674743 23693150230586766347512115)
    ·
      refine ⟨35539725345880149521268173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23693150230586766347512115 35539725345880149521268173)
      ·
        refine ⟨13327397004705056070475565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35539725345880149521268173 13327397004705056070475565)
        ·
          refine ⟨4997773876764396026428337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13327397004705056070475565 4997773876764396026428337)
          ·
            refine ⟨3748330407573297019821253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4997773876764396026428337 3748330407573297019821253)
            ·
              refine ⟨702811951419993191216485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3748330407573297019821253 702811951419993191216485)
              ·
                refine ⟨131777240891248723353091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 702811951419993191216485 131777240891248723353091)
                ·
                  rfl

theorem cell20_866144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_866144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866144 prefixEnd_866144 := by exact prefixLift 866144
  have htrace : WordTrace (prefixWord ++ tailWord_866144) baseStart_866144 baseEnd_866144 := by
    simpa [prefixWord, tailWord_866144, baseEnd_866144] using wordTrace_append hprefix tailTrace_866144
  have hstable : (prefixWord ++ tailWord_866144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866144).length < 2 ^ (prefixWord ++ tailWord_866144).sum := by decide
  have hdescent : baseEnd_866144 < baseStart_866144 := by decide
  rcases family_descends (prefixWord ++ tailWord_866144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866217 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 8]
def baseStart_866217 : Nat := 118140960795 + 866217 * 2 ^ 59
def prefixEnd_866217 : Nat := 4983230072969 + 3 ^ 40 * 866217 * 2
def baseEnd_866217 : Nat := 395365041862882360625641

theorem tailTrace_866217 : CollatzResearch.WordTrace tailWord_866217 prefixEnd_866217 395365041862882360625641 := by
  unfold tailWord_866217
  simp only [CollatzResearch.WordTrace]
  refine ⟨31593529502851221930756905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21062353001900814620504603 31593529502851221930756905)
  ·
    refine ⟨23695147127138416448067679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31593529502851221930756905 23695147127138416448067679)
    ·
      refine ⟨35542720690707624672101519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23695147127138416448067679 35542720690707624672101519)
      ·
        refine ⟨53314081036061437008152279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35542720690707624672101519 53314081036061437008152279)
        ·
          refine ⟨79971121554092155512228419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53314081036061437008152279 79971121554092155512228419)
          ·
            refine ⟨119956682331138233268342629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79971121554092155512228419 119956682331138233268342629)
            ·
              refine ⟨22491877937088418737814243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 119956682331138233268342629 22491877937088418737814243)
              ·
                refine ⟨33737816905632628106721365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22491877937088418737814243 33737816905632628106721365)
                ·
                  refine ⟨395365041862882360625641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33737816905632628106721365 395365041862882360625641)
                  ·
                    rfl

theorem cell20_866217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_866217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866217 prefixEnd_866217 := by exact prefixLift 866217
  have htrace : WordTrace (prefixWord ++ tailWord_866217) baseStart_866217 baseEnd_866217 := by
    simpa [prefixWord, tailWord_866217, baseEnd_866217] using wordTrace_append hprefix tailTrace_866217
  have hstable : (prefixWord ++ tailWord_866217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866217).length < 2 ^ (prefixWord ++ tailWord_866217).sum := by decide
  have hdescent : baseEnd_866217 < baseStart_866217 := by decide
  rcases family_descends (prefixWord ++ tailWord_866217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866222 : List Nat := [4, 1, 5, 1, 1, 2, 2, 2, 2]
def baseStart_866222 : Nat := 118140960795 + 866222 * 2 ^ 59
def prefixEnd_866222 : Nat := 4983230072969 + 3 ^ 40 * 866222 * 2
def baseEnd_866222 : Nat := 395367323999124565458955

theorem tailTrace_866222 : CollatzResearch.WordTrace tailWord_866222 prefixEnd_866222 395367323999124565458955 := by
  unfold tailWord_866222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949213983479138473086115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21062474578555405189792613 3949213983479138473086115)
  ·
    refine ⟨5923820975218707709629173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949213983479138473086115 5923820975218707709629173)
    ·
      refine ⟨555358216426753847777735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5923820975218707709629173 555358216426753847777735)
      ·
        refine ⟨833037324640130771666603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 555358216426753847777735 833037324640130771666603)
        ·
          refine ⟨1249555986960196157499905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833037324640130771666603 1249555986960196157499905)
          ·
            refine ⟨937166990220147118124929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249555986960196157499905 937166990220147118124929)
            ·
              refine ⟨702875242665110338593697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937166990220147118124929 702875242665110338593697)
              ·
                refine ⟨527156431998832753945273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 702875242665110338593697 527156431998832753945273)
                ·
                  refine ⟨395367323999124565458955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527156431998832753945273 395367323999124565458955)
                  ·
                    rfl

theorem cell20_866222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_866222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866222 prefixEnd_866222 := by exact prefixLift 866222
  have htrace : WordTrace (prefixWord ++ tailWord_866222) baseStart_866222 baseEnd_866222 := by
    simpa [prefixWord, tailWord_866222, baseEnd_866222] using wordTrace_append hprefix tailTrace_866222
  have hstable : (prefixWord ++ tailWord_866222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866222).length < 2 ^ (prefixWord ++ tailWord_866222).sum := by decide
  have hdescent : baseEnd_866222 < baseStart_866222 := by decide
  rcases family_descends (prefixWord ++ tailWord_866222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866227 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 3]
def baseStart_866227 : Nat := 118140960795 + 866227 * 2 ^ 59
def prefixEnd_866227 : Nat := 4983230072969 + 3 ^ 40 * 866227 * 2
def baseEnd_866227 : Nat := 395369606135366770292267

theorem tailTrace_866227 : CollatzResearch.WordTrace tailWord_866227 prefixEnd_866227 395369606135366770292267 := by
  unfold tailWord_866227
  simp only [CollatzResearch.WordTrace]
  refine ⟨31593894232814993638620935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21062596155209995759080623 31593894232814993638620935)
  ·
    refine ⟨47390841349222490457931403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31593894232814993638620935 47390841349222490457931403)
    ·
      refine ⟨71086262023833735686897105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47390841349222490457931403 71086262023833735686897105)
      ·
        refine ⟨53314696517875301765172829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71086262023833735686897105 53314696517875301765172829)
        ·
          refine ⟨19993011194203238161939811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53314696517875301765172829 19993011194203238161939811)
          ·
            refine ⟨29989516791304857242909717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19993011194203238161939811 29989516791304857242909717)
            ·
              refine ⟨1405758599592415183261393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29989516791304857242909717 1405758599592415183261393)
              ·
                refine ⟨1054318949694311387446045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1405758599592415183261393 1054318949694311387446045)
                ·
                  refine ⟨395369606135366770292267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054318949694311387446045 395369606135366770292267)
                  ·
                    rfl

theorem cell20_866227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_866227 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866227 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866227 prefixEnd_866227 := by exact prefixLift 866227
  have htrace : WordTrace (prefixWord ++ tailWord_866227) baseStart_866227 baseEnd_866227 := by
    simpa [prefixWord, tailWord_866227, baseEnd_866227] using wordTrace_append hprefix tailTrace_866227
  have hstable : (prefixWord ++ tailWord_866227).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866227).length < 2 ^ (prefixWord ++ tailWord_866227).sum := by decide
  have hdescent : baseEnd_866227 < baseStart_866227 := by decide
  rcases family_descends (prefixWord ++ tailWord_866227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866289 : List Nat := [1, 2, 2, 2, 5, 1, 2, 1, 4]
def baseStart_866289 : Nat := 118140960795 + 866289 * 2 ^ 59
def prefixEnd_866289 : Nat := 4983230072969 + 3 ^ 40 * 866289 * 2
def baseEnd_866289 : Nat := 395397904624770110225347

theorem tailTrace_866289 : CollatzResearch.WordTrace tailWord_866289 prefixEnd_866289 395397904624770110225347 := by
  unfold tailWord_866289
  simp only [CollatzResearch.WordTrace]
  refine ⟨31596155558590378227377921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21064103705726918818251947 31596155558590378227377921)
  ·
    refine ⟨23697116668942783670533441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31596155558590378227377921 23697116668942783670533441)
    ·
      refine ⟨17772837501707087752900081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23697116668942783670533441 17772837501707087752900081)
      ·
        refine ⟨13329628126280315814675061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17772837501707087752900081 13329628126280315814675061)
        ·
          refine ⟨1249652636838779607625787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13329628126280315814675061 1249652636838779607625787)
          ·
            refine ⟨1874478955258169411438681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249652636838779607625787 1874478955258169411438681)
            ·
              refine ⟨1405859216443627058579011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874478955258169411438681 1405859216443627058579011)
              ·
                refine ⟨2108788824665440587868517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1405859216443627058579011 2108788824665440587868517)
                ·
                  refine ⟨395397904624770110225347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2108788824665440587868517 395397904624770110225347)
                  ·
                    rfl

theorem cell20_866289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_866289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866289 prefixEnd_866289 := by exact prefixLift 866289
  have htrace : WordTrace (prefixWord ++ tailWord_866289) baseStart_866289 baseEnd_866289 := by
    simpa [prefixWord, tailWord_866289, baseEnd_866289] using wordTrace_append hprefix tailTrace_866289
  have hstable : (prefixWord ++ tailWord_866289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866289).length < 2 ^ (prefixWord ++ tailWord_866289).sum := by decide
  have hdescent : baseEnd_866289 < baseStart_866289 := by decide
  rcases family_descends (prefixWord ++ tailWord_866289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866358 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_866358 : Nat := 118140960795 + 866358 * 2 ^ 59
def prefixEnd_866358 : Nat := 4983230072969 + 3 ^ 40 * 866358 * 2
def baseEnd_866358 : Nat := 395429398104912536925065

theorem tailTrace_866358 : CollatzResearch.WordTrace tailWord_866358 prefixEnd_866358 395429398104912536925065 := by
  unfold tailWord_866358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1974917012208775188227483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21065781463560268674426485 1974917012208775188227483)
  ·
    refine ⟨2962375518313162782341225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1974917012208775188227483 2962375518313162782341225)
    ·
      refine ⟨2221781638734872086755919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2962375518313162782341225 2221781638734872086755919)
      ·
        refine ⟨3332672458102308130133879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221781638734872086755919 3332672458102308130133879)
        ·
          refine ⟨4999008687153462195200819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332672458102308130133879 4999008687153462195200819)
          ·
            refine ⟨7498513030730193292801229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4999008687153462195200819 7498513030730193292801229)
            ·
              refine ⟨2811942386523822484800461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7498513030730193292801229 2811942386523822484800461)
              ·
                refine ⟨1054478394946433431800173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2811942386523822484800461 1054478394946433431800173)
                ·
                  refine ⟨395429398104912536925065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054478394946433431800173 395429398104912536925065)
                  ·
                    rfl

theorem cell20_866358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_866358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866358 prefixEnd_866358 := by exact prefixLift 866358
  have htrace : WordTrace (prefixWord ++ tailWord_866358) baseStart_866358 baseEnd_866358 := by
    simpa [prefixWord, tailWord_866358, baseEnd_866358] using wordTrace_append hprefix tailTrace_866358
  have hstable : (prefixWord ++ tailWord_866358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866358).length < 2 ^ (prefixWord ++ tailWord_866358).sum := by decide
  have hdescent : baseEnd_866358 < baseStart_866358 := by decide
  rcases family_descends (prefixWord ++ tailWord_866358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866396 : List Nat := [2, 2, 4, 1, 1, 3, 2, 2, 3]
def baseStart_866396 : Nat := 118140960795 + 866396 * 2 ^ 59
def prefixEnd_866396 : Nat := 4983230072969 + 3 ^ 40 * 866396 * 2
def baseEnd_866396 : Nat := 395446742340353293658243

theorem tailTrace_866396 : CollatzResearch.WordTrace tailWord_866396 prefixEnd_866396 395446742340353293658243 := by
  unfold tailWord_866396
  simp only [CollatzResearch.WordTrace]
  refine ⟨15800029084601367750761521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21066705446135157001015361 15800029084601367750761521)
  ·
    refine ⟨11850021813451025813071141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15800029084601367750761521 11850021813451025813071141)
    ·
      refine ⟨2221879090022067339950839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11850021813451025813071141 2221879090022067339950839)
      ·
        refine ⟨3332818635033101009926259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2221879090022067339950839 3332818635033101009926259)
        ·
          refine ⟨4999227952549651514889389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3332818635033101009926259 4999227952549651514889389)
          ·
            refine ⟨1874710482206119318083521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4999227952549651514889389 1874710482206119318083521)
            ·
              refine ⟨1406032861654589488562641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1874710482206119318083521 1406032861654589488562641)
              ·
                refine ⟨1054524646240942116421981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406032861654589488562641 1054524646240942116421981)
                ·
                  refine ⟨395446742340353293658243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054524646240942116421981 395446742340353293658243)
                  ·
                    rfl

theorem cell20_866396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_866396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866396 prefixEnd_866396 := by exact prefixLift 866396
  have htrace : WordTrace (prefixWord ++ tailWord_866396) baseStart_866396 baseEnd_866396 := by
    simpa [prefixWord, tailWord_866396, baseEnd_866396] using wordTrace_append hprefix tailTrace_866396
  have hstable : (prefixWord ++ tailWord_866396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866396).length < 2 ^ (prefixWord ++ tailWord_866396).sum := by decide
  have hdescent : baseEnd_866396 < baseStart_866396 := by decide
  rcases family_descends (prefixWord ++ tailWord_866396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866441 : List Nat := [1, 2, 1, 1, 4, 2, 4, 3, 2]
def baseStart_866441 : Nat := 118140960795 + 866441 * 2 ^ 59
def prefixEnd_866441 : Nat := 4983230072969 + 3 ^ 40 * 866441 * 2
def baseEnd_866441 : Nat := 395467281566533137158059

theorem tailTrace_866441 : CollatzResearch.WordTrace tailWord_866441 prefixEnd_866441 395467281566533137158059 := by
  unfold tailWord_866441
  simp only [CollatzResearch.WordTrace]
  refine ⟨31601699454039708186911177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21067799636026472124607451 31601699454039708186911177)
  ·
    refine ⟨23701274590529781140183383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31601699454039708186911177 23701274590529781140183383)
    ·
      refine ⟨35551911885794671710275075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23701274590529781140183383 35551911885794671710275075)
      ·
        refine ⟨53327867828692007565412613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35551911885794671710275075 53327867828692007565412613)
        ·
          refine ⟨9998975217879751418514865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53327867828692007565412613 9998975217879751418514865)
          ·
            refine ⟨7499231413409813563886149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9998975217879751418514865 7499231413409813563886149)
            ·
              refine ⟨1406105890014340043228653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7499231413409813563886149 1406105890014340043228653)
              ·
                refine ⟨527289708755377516210745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406105890014340043228653 527289708755377516210745)
                ·
                  refine ⟨395467281566533137158059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527289708755377516210745 395467281566533137158059)
                  ·
                    rfl

theorem cell20_866441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 3, 2].length) (baseStart_866441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866441 prefixEnd_866441 := by exact prefixLift 866441
  have htrace : WordTrace (prefixWord ++ tailWord_866441) baseStart_866441 baseEnd_866441 := by
    simpa [prefixWord, tailWord_866441, baseEnd_866441] using wordTrace_append hprefix tailTrace_866441
  have hstable : (prefixWord ++ tailWord_866441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866441).length < 2 ^ (prefixWord ++ tailWord_866441).sum := by decide
  have hdescent : baseEnd_866441 < baseStart_866441 := by decide
  rcases family_descends (prefixWord ++ tailWord_866441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866455 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 5]
def baseStart_866455 : Nat := 118140960795 + 866455 * 2 ^ 59
def prefixEnd_866455 : Nat := 4983230072969 + 3 ^ 40 * 866455 * 2
def baseEnd_866455 : Nat := 395473671548011310691335

theorem tailTrace_866455 : CollatzResearch.WordTrace tailWord_866455 prefixEnd_866455 395473671548011310691335 := by
  unfold tailWord_866455
  simp only [CollatzResearch.WordTrace]
  refine ⟨31602210075988988577920819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21068140050659325718613879 31602210075988988577920819)
  ·
    refine ⟨47403315113983482866881229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31602210075988988577920819 47403315113983482866881229)
    ·
      refine ⟨17776243167743806075080461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47403315113983482866881229 17776243167743806075080461)
      ·
        refine ⟨6666091187903927278155173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17776243167743806075080461 6666091187903927278155173)
        ·
          refine ⟨1249892097731986364654095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6666091187903927278155173 1249892097731986364654095)
          ·
            refine ⟨1874838146597979546981143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1249892097731986364654095 1874838146597979546981143)
            ·
              refine ⟨2812257219896969320471715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1874838146597979546981143 2812257219896969320471715)
              ·
                refine ⟨4218385829845453980707573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2812257219896969320471715 4218385829845453980707573)
                ·
                  refine ⟨395473671548011310691335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4218385829845453980707573 395473671548011310691335)
                  ·
                    rfl

theorem cell20_866455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 5].length) (baseStart_866455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866455 prefixEnd_866455 := by exact prefixLift 866455
  have htrace : WordTrace (prefixWord ++ tailWord_866455) baseStart_866455 baseEnd_866455 := by
    simpa [prefixWord, tailWord_866455, baseEnd_866455] using wordTrace_append hprefix tailTrace_866455
  have hstable : (prefixWord ++ tailWord_866455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866455).length < 2 ^ (prefixWord ++ tailWord_866455).sum := by decide
  have hdescent : baseEnd_866455 < baseStart_866455 := by decide
  rcases family_descends (prefixWord ++ tailWord_866455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866496 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 2]
def baseStart_866496 : Nat := 118140960795 + 866496 * 2 ^ 59
def prefixEnd_866496 : Nat := 4983230072969 + 3 ^ 40 * 866496 * 2
def baseEnd_866496 : Nat := 395492385065197390324501

theorem tailTrace_866496 : CollatzResearch.WordTrace tailWord_866496 prefixEnd_866496 395492385065197390324501 := by
  unfold tailWord_866496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15801852734420226290081671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21069136979226968386775561 15801852734420226290081671)
  ·
    refine ⟨23702779101630339435122507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15801852734420226290081671 23702779101630339435122507)
    ·
      refine ⟨35554168652445509152683761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23702779101630339435122507 35554168652445509152683761)
      ·
        refine ⟨26665626489334131864512821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35554168652445509152683761 26665626489334131864512821)
        ·
          refine ⟨2499902483375074862298077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26665626489334131864512821 2499902483375074862298077)
          ·
            refine ⟨937463431265653073361779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2499902483375074862298077 937463431265653073361779)
            ·
              refine ⟨1406195146898479610042669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937463431265653073361779 1406195146898479610042669)
              ·
                refine ⟨527323180086929853766001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406195146898479610042669 527323180086929853766001)
                ·
                  refine ⟨395492385065197390324501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527323180086929853766001 395492385065197390324501)
                  ·
                    rfl

theorem cell20_866496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 2].length) (baseStart_866496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866496 prefixEnd_866496 := by exact prefixLift 866496
  have htrace : WordTrace (prefixWord ++ tailWord_866496) baseStart_866496 baseEnd_866496 := by
    simpa [prefixWord, tailWord_866496, baseEnd_866496] using wordTrace_append hprefix tailTrace_866496
  have hstable : (prefixWord ++ tailWord_866496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866496).length < 2 ^ (prefixWord ++ tailWord_866496).sum := by decide
  have hdescent : baseEnd_866496 < baseStart_866496 := by decide
  rcases family_descends (prefixWord ++ tailWord_866496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866569 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 3]
def baseStart_866569 : Nat := 118140960795 + 866569 * 2 ^ 59
def prefixEnd_866569 : Nat := 4983230072969 + 3 ^ 40 * 866569 * 2
def baseEnd_866569 : Nat := 395525704254333580890869

theorem tailTrace_866569 : CollatzResearch.WordTrace tailWord_866569 prefixEnd_866569 395525704254333580890869 := by
  unfold tailWord_866569
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606367997575986047570761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21070911998383990698380507 31606367997575986047570761)
  ·
    refine ⟨23704775998181989535678071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31606367997575986047570761 23704775998181989535678071)
    ·
      refine ⟨35557163997272984303517107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23704775998181989535678071 35557163997272984303517107)
      ·
        refine ⟨53335745995909476455275661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35557163997272984303517107 53335745995909476455275661)
        ·
          refine ⟨20000904748466053670728373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53335745995909476455275661 20000904748466053670728373)
          ·
            refine ⟨1875084820168692531630785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20000904748466053670728373 1875084820168692531630785)
            ·
              refine ⟨1406313615126519398723089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875084820168692531630785 1406313615126519398723089)
              ·
                refine ⟨1054735211344889549042317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1406313615126519398723089 1054735211344889549042317)
                ·
                  refine ⟨395525704254333580890869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054735211344889549042317 395525704254333580890869)
                  ·
                    rfl

theorem cell20_866569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_866569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866569 prefixEnd_866569 := by exact prefixLift 866569
  have htrace : WordTrace (prefixWord ++ tailWord_866569) baseStart_866569 baseEnd_866569 := by
    simpa [prefixWord, tailWord_866569, baseEnd_866569] using wordTrace_append hprefix tailTrace_866569
  have hstable : (prefixWord ++ tailWord_866569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866569).length < 2 ^ (prefixWord ++ tailWord_866569).sum := by decide
  have hdescent : baseEnd_866569 < baseStart_866569 := by decide
  rcases family_descends (prefixWord ++ tailWord_866569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866583 : List Nat := [1, 1, 3, 4, 1, 2, 3, 5]
def baseStart_866583 : Nat := 118140960795 + 866583 * 2 ^ 59
def prefixEnd_866583 : Nat := 4983230072969 + 3 ^ 40 * 866583 * 2
def baseEnd_866583 : Nat := 131844031411937251474715

theorem tailTrace_866583 : CollatzResearch.WordTrace tailWord_866583 prefixEnd_866583 131844031411937251474715 := by
  unfold tailWord_866583
  simp only [CollatzResearch.WordTrace]
  refine ⟨31606878619525266438580403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21071252413016844292386935 31606878619525266438580403)
  ·
    refine ⟨47410317929287899657870605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31606878619525266438580403 47410317929287899657870605)
    ·
      refine ⟨17778869223482962371701477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47410317929287899657870605 17778869223482962371701477)
      ·
        refine ⟨3333537979403055444694027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17778869223482962371701477 3333537979403055444694027)
        ·
          refine ⟨5000306969104583167041041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3333537979403055444694027 5000306969104583167041041)
          ·
            refine ⟨3750230226828437375280781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5000306969104583167041041 3750230226828437375280781)
            ·
              refine ⟨1406336335060664015730293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3750230226828437375280781 1406336335060664015730293)
              ·
                refine ⟨131844031411937251474715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406336335060664015730293 131844031411937251474715)
                ·
                  rfl

theorem cell20_866583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 5].length) (baseStart_866583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866583 prefixEnd_866583 := by exact prefixLift 866583
  have htrace : WordTrace (prefixWord ++ tailWord_866583) baseStart_866583 baseEnd_866583 := by
    simpa [prefixWord, tailWord_866583, baseEnd_866583] using wordTrace_append hprefix tailTrace_866583
  have hstable : (prefixWord ++ tailWord_866583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866583).length < 2 ^ (prefixWord ++ tailWord_866583).sum := by decide
  have hdescent : baseEnd_866583 < baseStart_866583 := by decide
  rcases family_descends (prefixWord ++ tailWord_866583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866604 : List Nat := [2, 2, 1, 1, 1, 3, 2, 8]
def baseStart_866604 : Nat := 118140960795 + 866604 * 2 ^ 59
def prefixEnd_866604 : Nat := 4983230072969 + 3 ^ 40 * 866604 * 2
def baseEnd_866604 : Nat := 131847226402676338241353

theorem tailTrace_866604 : CollatzResearch.WordTrace tailWord_866604 prefixEnd_866604 131847226402676338241353 := by
  unfold tailWord_866604
  simp only [CollatzResearch.WordTrace]
  refine ⟨15803822276224593512547433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21071763034966124683396577 15803822276224593512547433)
  ·
    refine ⟨11852866707168445134410575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15803822276224593512547433 11852866707168445134410575)
    ·
      refine ⟨17779300060752667701615863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11852866707168445134410575 17779300060752667701615863)
      ·
        refine ⟨26668950091129001552423795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17779300060752667701615863 26668950091129001552423795)
        ·
          refine ⟨40003425136693502328635693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26668950091129001552423795 40003425136693502328635693)
          ·
            refine ⟨15001284426260063373238385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40003425136693502328635693 15001284426260063373238385)
            ·
              refine ⟨11250963319695047529928789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15001284426260063373238385 11250963319695047529928789)
              ·
                refine ⟨131847226402676338241353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11250963319695047529928789 131847226402676338241353)
                ·
                  rfl

theorem cell20_866604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_866604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866604 prefixEnd_866604 := by exact prefixLift 866604
  have htrace : WordTrace (prefixWord ++ tailWord_866604) baseStart_866604 baseEnd_866604 := by
    simpa [prefixWord, tailWord_866604, baseEnd_866604] using wordTrace_append hprefix tailTrace_866604
  have hstable : (prefixWord ++ tailWord_866604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866604).length < 2 ^ (prefixWord ++ tailWord_866604).sum := by decide
  have hdescent : baseEnd_866604 < baseStart_866604 := by decide
  rcases family_descends (prefixWord ++ tailWord_866604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866610 : List Nat := [3, 2, 1, 1, 5, 1, 2, 3, 2]
def baseStart_866610 : Nat := 118140960795 + 866610 * 2 ^ 59
def prefixEnd_866610 : Nat := 4983230072969 + 3 ^ 40 * 866610 * 2
def baseEnd_866610 : Nat := 395544417771519660524035

theorem tailTrace_866610 : CollatzResearch.WordTrace tailWord_866610 prefixEnd_866610 395544417771519660524035 := by
  unfold tailWord_866610
  simp only [CollatzResearch.WordTrace]
  refine ⟨7901965847606862512453321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21071908926951633366542189 7901965847606862512453321)
  ·
    refine ⟨5926474385705146884339991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7901965847606862512453321 5926474385705146884339991)
    ·
      refine ⟨8889711578557720326509987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5926474385705146884339991 8889711578557720326509987)
      ·
        refine ⟨13334567367836580489764981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8889711578557720326509987 13334567367836580489764981)
        ·
          refine ⟨1250115690734679420915467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13334567367836580489764981 1250115690734679420915467)
          ·
            refine ⟨1875173536102019131373201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250115690734679420915467 1875173536102019131373201)
            ·
              refine ⟨1406380152076514348529901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875173536102019131373201 1406380152076514348529901)
              ·
                refine ⟨527392557028692880698713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406380152076514348529901 527392557028692880698713)
                ·
                  refine ⟨395544417771519660524035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527392557028692880698713 395544417771519660524035)
                  ·
                    rfl

theorem cell20_866610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_866610 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866610 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866610 prefixEnd_866610 := by exact prefixLift 866610
  have htrace : WordTrace (prefixWord ++ tailWord_866610) baseStart_866610 baseEnd_866610 := by
    simpa [prefixWord, tailWord_866610, baseEnd_866610] using wordTrace_append hprefix tailTrace_866610
  have hstable : (prefixWord ++ tailWord_866610).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866610).length < 2 ^ (prefixWord ++ tailWord_866610).sum := by decide
  have hdescent : baseEnd_866610 < baseStart_866610 := by decide
  rcases family_descends (prefixWord ++ tailWord_866610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866697 : List Nat := [1, 2, 1, 1, 6, 2, 2, 5]
def baseStart_866697 : Nat := 118140960795 + 866697 * 2 ^ 59
def prefixEnd_866697 : Nat := 4983230072969 + 3 ^ 40 * 866697 * 2
def baseEnd_866697 : Nat := 131861375647378008207893

theorem tailTrace_866697 : CollatzResearch.WordTrace tailWord_866697 prefixEnd_866697 131861375647378008207893 := by
  unfold tailWord_866697
  simp only [CollatzResearch.WordTrace]
  refine ⟨31611036541112263908230345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074024360741509272153563 31611036541112263908230345)
  ·
    refine ⟨23708277405834197931172759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31611036541112263908230345 23708277405834197931172759)
    ·
      refine ⟨35562416108751296896759139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23708277405834197931172759 35562416108751296896759139)
      ·
        refine ⟨53343624163126945345138709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35562416108751296896759139 53343624163126945345138709)
        ·
          refine ⟨2500482382646575563053377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53343624163126945345138709 2500482382646575563053377)
          ·
            refine ⟨1875361786984931672290033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500482382646575563053377 1875361786984931672290033)
            ·
              refine ⟨1406521340238698754217525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875361786984931672290033 1406521340238698754217525)
              ·
                refine ⟨131861375647378008207893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406521340238698754217525 131861375647378008207893)
                ·
                  rfl

theorem cell20_866697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 5].length) (baseStart_866697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866697 prefixEnd_866697 := by exact prefixLift 866697
  have htrace : WordTrace (prefixWord ++ tailWord_866697) baseStart_866697 baseEnd_866697 := by
    simpa [prefixWord, tailWord_866697, baseEnd_866697] using wordTrace_append hprefix tailTrace_866697
  have hstable : (prefixWord ++ tailWord_866697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866697).length < 2 ^ (prefixWord ++ tailWord_866697).sum := by decide
  have hdescent : baseEnd_866697 < baseStart_866697 := by decide
  rcases family_descends (prefixWord ++ tailWord_866697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866700 : List Nat := [2, 2, 1, 2, 1, 6, 2, 1, 3]
def baseStart_866700 : Nat := 118140960795 + 866700 * 2 ^ 59
def prefixEnd_866700 : Nat := 4983230072969 + 3 ^ 40 * 866700 * 2
def baseEnd_866700 : Nat := 395585496223879347523667

theorem tailTrace_866700 : CollatzResearch.WordTrace tailWord_866700 prefixEnd_866700 395585496223879347523667 := by
  unfold tailWord_866700
  simp only [CollatzResearch.WordTrace]
  refine ⟨15805572980050697710294777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21074097306734263613726369 15805572980050697710294777)
  ·
    refine ⟨11854179735038023282721083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15805572980050697710294777 11854179735038023282721083)
    ·
      refine ⟨17781269602557034924081625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11854179735038023282721083 17781269602557034924081625)
      ·
        refine ⟨13335952201917776193061219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17781269602557034924081625 13335952201917776193061219)
        ·
          refine ⟨20003928302876664289591829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13335952201917776193061219 20003928302876664289591829)
          ·
            refine ⟨937684139197343638574617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20003928302876664289591829 937684139197343638574617)
            ·
              refine ⟨703263104398007728930963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937684139197343638574617 703263104398007728930963)
              ·
                refine ⟨1054894656597011593396445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703263104398007728930963 1054894656597011593396445)
                ·
                  refine ⟨395585496223879347523667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1054894656597011593396445 395585496223879347523667)
                  ·
                    rfl

theorem cell20_866700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_866700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866700 prefixEnd_866700 := by exact prefixLift 866700
  have htrace : WordTrace (prefixWord ++ tailWord_866700) baseStart_866700 baseEnd_866700 := by
    simpa [prefixWord, tailWord_866700, baseEnd_866700] using wordTrace_append hprefix tailTrace_866700
  have hstable : (prefixWord ++ tailWord_866700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866700).length < 2 ^ (prefixWord ++ tailWord_866700).sum := by decide
  have hdescent : baseEnd_866700 < baseStart_866700 := by decide
  rcases family_descends (prefixWord ++ tailWord_866700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866711 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 4]
def baseStart_866711 : Nat := 118140960795 + 866711 * 2 ^ 59
def prefixEnd_866711 : Nat := 4983230072969 + 3 ^ 40 * 866711 * 2
def baseEnd_866711 : Nat := 395590516923612198156955

theorem tailTrace_866711 : CollatzResearch.WordTrace tailWord_866711 prefixEnd_866711 395590516923612198156955 := by
  unfold tailWord_866711
  simp only [CollatzResearch.WordTrace]
  refine ⟨31611547163061544299239987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21074364775374362866159991 31611547163061544299239987)
  ·
    refine ⟨47417320744592316448859981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31611547163061544299239987 47417320744592316448859981)
    ·
      refine ⟨17781495279222118668322493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47417320744592316448859981 17781495279222118668322493)
      ·
        refine ⟨6668060729708294500620935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17781495279222118668322493 6668060729708294500620935)
        ·
          refine ⟨10002091094562441750931403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6668060729708294500620935 10002091094562441750931403)
          ·
            refine ⟨15003136641843662626397105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10002091094562441750931403 15003136641843662626397105)
            ·
              refine ⟨11252352481382746969797829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15003136641843662626397105 11252352481382746969797829)
              ·
                refine ⟨2109816090259265056837093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11252352481382746969797829 2109816090259265056837093)
                ·
                  refine ⟨395590516923612198156955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2109816090259265056837093 395590516923612198156955)
                  ·
                    rfl

theorem cell20_866711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_866711 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866711 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866711 prefixEnd_866711 := by exact prefixLift 866711
  have htrace : WordTrace (prefixWord ++ tailWord_866711) baseStart_866711 baseEnd_866711 := by
    simpa [prefixWord, tailWord_866711, baseEnd_866711] using wordTrace_append hprefix tailTrace_866711
  have hstable : (prefixWord ++ tailWord_866711).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866711).length < 2 ^ (prefixWord ++ tailWord_866711).sum := by decide
  have hdescent : baseEnd_866711 < baseStart_866711 := by decide
  rcases family_descends (prefixWord ++ tailWord_866711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866741 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 2]
def baseStart_866741 : Nat := 118140960795 + 866741 * 2 ^ 59
def prefixEnd_866741 : Nat := 4983230072969 + 3 ^ 40 * 866741 * 2
def baseEnd_866741 : Nat := 395604209741065427156833

theorem tailTrace_866741 : CollatzResearch.WordTrace tailWord_866741 prefixEnd_866741 395604209741065427156833 := by
  unfold tailWord_866741
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612641352952859422832077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21075094235301906281888051 31612641352952859422832077)
  ·
    refine ⟨11854740507357322283562029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31612641352952859422832077 11854740507357322283562029)
    ·
      refine ⟨4445527690258995856335761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11854740507357322283562029 4445527690258995856335761)
      ·
        refine ⟨3334145767694246892251821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4445527690258995856335761 3334145767694246892251821)
        ·
          refine ⟨1250304662885342584594433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3334145767694246892251821 1250304662885342584594433)
          ·
            refine ⟨937728497164006938445825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1250304662885342584594433 937728497164006938445825)
            ·
              refine ⟨703296372873005203834369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937728497164006938445825 703296372873005203834369)
              ·
                refine ⟨527472279654753902875777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703296372873005203834369 527472279654753902875777)
                ·
                  refine ⟨395604209741065427156833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527472279654753902875777 395604209741065427156833)
                  ·
                    rfl

theorem cell20_866741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_866741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866741 prefixEnd_866741 := by exact prefixLift 866741
  have htrace : WordTrace (prefixWord ++ tailWord_866741) baseStart_866741 baseEnd_866741 := by
    simpa [prefixWord, tailWord_866741, baseEnd_866741] using wordTrace_append hprefix tailTrace_866741
  have hstable : (prefixWord ++ tailWord_866741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866741).length < 2 ^ (prefixWord ++ tailWord_866741).sum := by decide
  have hdescent : baseEnd_866741 < baseStart_866741 := by decide
  rcases family_descends (prefixWord ++ tailWord_866741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866745 : List Nat := [1, 2, 1, 4, 3, 2, 1, 4, 2]
def baseStart_866745 : Nat := 118140960795 + 866745 * 2 ^ 59
def prefixEnd_866745 : Nat := 4983230072969 + 3 ^ 40 * 866745 * 2
def baseEnd_866745 : Nat := 395606035450059191023483

theorem tailTrace_866745 : CollatzResearch.WordTrace tailWord_866745 prefixEnd_866745 395606035450059191023483 := by
  unfold tailWord_866745
  simp only [CollatzResearch.WordTrace]
  refine ⟨31612787244938368105977689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21075191496625578737318459 31612787244938368105977689)
  ·
    refine ⟨23709590433703776079483267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31612787244938368105977689 23709590433703776079483267)
    ·
      refine ⟨35564385650555664119224901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23709590433703776079483267 35564385650555664119224901)
      ·
        refine ⟨6668322309479187022354669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35564385650555664119224901 6668322309479187022354669)
        ·
          refine ⟨2500620866054695133383001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6668322309479187022354669 2500620866054695133383001)
          ·
            refine ⟨1875465649541021350037251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500620866054695133383001 1875465649541021350037251)
            ·
              refine ⟨2813198474311532025055877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875465649541021350037251 2813198474311532025055877)
              ·
                refine ⟨527474713933412254697977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2813198474311532025055877 527474713933412254697977)
                ·
                  refine ⟨395606035450059191023483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527474713933412254697977 395606035450059191023483)
                  ·
                    rfl

theorem cell20_866745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_866745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866745 prefixEnd_866745 := by exact prefixLift 866745
  have htrace : WordTrace (prefixWord ++ tailWord_866745) baseStart_866745 baseEnd_866745 := by
    simpa [prefixWord, tailWord_866745, baseEnd_866745] using wordTrace_append hprefix tailTrace_866745
  have hstable : (prefixWord ++ tailWord_866745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866745).length < 2 ^ (prefixWord ++ tailWord_866745).sum := by decide
  have hdescent : baseEnd_866745 < baseStart_866745 := by decide
  rcases family_descends (prefixWord ++ tailWord_866745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866763 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 7]
def baseStart_866763 : Nat := 118140960795 + 866763 * 2 ^ 59
def prefixEnd_866763 : Nat := 4983230072969 + 3 ^ 40 * 866763 * 2
def baseEnd_866763 : Nat := 395614251140531128423409

theorem tailTrace_866763 : CollatzResearch.WordTrace tailWord_866763 prefixEnd_866763 395614251140531128423409 := by
  unfold tailWord_866763
  simp only [CollatzResearch.WordTrace]
  refine ⟨31613443758873157180132943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21075629172582104786755295 31613443758873157180132943)
  ·
    refine ⟨47420165638309735770199415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31613443758873157180132943 47420165638309735770199415)
    ·
      refine ⟨71130248457464603655299123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47420165638309735770199415 71130248457464603655299123)
      ·
        refine ⟨106695372686196905482948685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71130248457464603655299123 106695372686196905482948685)
        ·
          refine ⟨40010764757323839556105757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106695372686196905482948685 40010764757323839556105757)
          ·
            refine ⟨15004036783996439833539659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40010764757323839556105757 15004036783996439833539659)
            ·
              refine ⟨22506055175994659750309489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15004036783996439833539659 22506055175994659750309489)
              ·
                refine ⟨16879541381995994812732117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22506055175994659750309489 16879541381995994812732117)
                ·
                  refine ⟨395614251140531128423409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16879541381995994812732117 395614251140531128423409)
                  ·
                    rfl

theorem cell20_866763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_866763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866763 prefixEnd_866763 := by exact prefixLift 866763
  have htrace : WordTrace (prefixWord ++ tailWord_866763) baseStart_866763 baseEnd_866763 := by
    simpa [prefixWord, tailWord_866763, baseEnd_866763] using wordTrace_append hprefix tailTrace_866763
  have hstable : (prefixWord ++ tailWord_866763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866763).length < 2 ^ (prefixWord ++ tailWord_866763).sum := by decide
  have hdescent : baseEnd_866763 < baseStart_866763 := by decide
  rcases family_descends (prefixWord ++ tailWord_866763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866783 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 2]
def baseStart_866783 : Nat := 118140960795 + 866783 * 2 ^ 59
def prefixEnd_866783 : Nat := 4983230072969 + 3 ^ 40 * 866783 * 2
def baseEnd_866783 : Nat := 395623379685499947756661

theorem tailTrace_866783 : CollatzResearch.WordTrace tailWord_866783 prefixEnd_866783 395623379685499947756661 := by
  unfold tailWord_866783
  simp only [CollatzResearch.WordTrace]
  refine ⟨31614173218800700595861003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21076115479200467063907335 31614173218800700595861003)
  ·
    refine ⟨47421259828201050893791505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31614173218800700595861003 47421259828201050893791505)
    ·
      refine ⟨35565944871150788170343629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47421259828201050893791505 35565944871150788170343629)
      ·
        refine ⟨13337229326681545563878861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35565944871150788170343629 13337229326681545563878861)
        ·
          refine ⟨5001460997505579586454573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13337229326681545563878861 5001460997505579586454573)
          ·
            refine ⟨1875547874064592344920465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5001460997505579586454573 1875547874064592344920465)
            ·
              refine ⟨1406660905548444258690349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1875547874064592344920465 1406660905548444258690349)
              ·
                refine ⟨527497839580666597008881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1406660905548444258690349 527497839580666597008881)
                ·
                  refine ⟨395623379685499947756661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527497839580666597008881 395623379685499947756661)
                  ·
                    rfl

theorem cell20_866783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 2].length) (baseStart_866783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866783 prefixEnd_866783 := by exact prefixLift 866783
  have htrace : WordTrace (prefixWord ++ tailWord_866783) baseStart_866783 baseEnd_866783 := by
    simpa [prefixWord, tailWord_866783, baseEnd_866783] using wordTrace_append hprefix tailTrace_866783
  have hstable : (prefixWord ++ tailWord_866783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866783).length < 2 ^ (prefixWord ++ tailWord_866783).sum := by decide
  have hdescent : baseEnd_866783 < baseStart_866783 := by decide
  rcases family_descends (prefixWord ++ tailWord_866783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866797 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 5]
def baseStart_866797 : Nat := 118140960795 + 866797 * 2 ^ 59
def prefixEnd_866797 : Nat := 4983230072969 + 3 ^ 40 * 866797 * 2
def baseEnd_866797 : Nat := 395629769666978121289937

theorem tailTrace_866797 : CollatzResearch.WordTrace tailWord_866797 prefixEnd_866797 395629769666978121289937 := by
  unfold tailWord_866797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31614683840749980986870645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21076455893833320657913763 31614683840749980986870645)
  ·
    refine ⟨2963876610070310717519123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31614683840749980986870645 2963876610070310717519123)
    ·
      refine ⟨4445814915105466076278685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2963876610070310717519123 4445814915105466076278685)
      ·
        refine ⟨1667180593164549778604507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4445814915105466076278685 1667180593164549778604507)
        ·
          refine ⟨2500770889746824667906761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1667180593164549778604507 2500770889746824667906761)
          ·
            refine ⟨1875578167310118500930071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2500770889746824667906761 1875578167310118500930071)
            ·
              refine ⟨2813367250965177751395107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875578167310118500930071 2813367250965177751395107)
              ·
                refine ⟨4220050876447766627092661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2813367250965177751395107 4220050876447766627092661)
                ·
                  refine ⟨395629769666978121289937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220050876447766627092661 395629769666978121289937)
                  ·
                    rfl

theorem cell20_866797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_866797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866797 prefixEnd_866797 := by exact prefixLift 866797
  have htrace : WordTrace (prefixWord ++ tailWord_866797) baseStart_866797 baseEnd_866797 := by
    simpa [prefixWord, tailWord_866797, baseEnd_866797] using wordTrace_append hprefix tailTrace_866797
  have hstable : (prefixWord ++ tailWord_866797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866797).length < 2 ^ (prefixWord ++ tailWord_866797).sum := by decide
  have hdescent : baseEnd_866797 < baseStart_866797 := by decide
  rcases family_descends (prefixWord ++ tailWord_866797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866828 : List Nat := [2, 2, 1, 2, 4, 3, 2, 4]
def baseStart_866828 : Nat := 118140960795 + 866828 * 2 ^ 59
def prefixEnd_866828 : Nat := 4983230072969 + 3 ^ 40 * 866828 * 2
def baseEnd_866828 : Nat := 131881306303893263752159

theorem tailTrace_866828 : CollatzResearch.WordTrace tailWord_866828 prefixEnd_866828 131881306303893263752159 := by
  unfold tailWord_866828
  simp only [CollatzResearch.WordTrace]
  refine ⟨15807907251818836640624569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21077209669091782187499425 15807907251818836640624569)
  ·
    refine ⟨11855930438864127480468427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15807907251818836640624569 11855930438864127480468427)
    ·
      refine ⟨17783895658296191220702641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11855930438864127480468427 17783895658296191220702641)
      ·
        refine ⟨13337921743722143415526981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17783895658296191220702641 13337921743722143415526981)
        ·
          refine ⟨2500860326947901890411309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13337921743722143415526981 2500860326947901890411309)
          ·
            refine ⟨937822622605463208904241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2500860326947901890411309 937822622605463208904241)
            ·
              refine ⟨703366966954097406678181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 937822622605463208904241 703366966954097406678181)
              ·
                refine ⟨131881306303893263752159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 703366966954097406678181 131881306303893263752159)
                ·
                  rfl

theorem cell20_866828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 4].length) (baseStart_866828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866828 prefixEnd_866828 := by exact prefixLift 866828
  have htrace : WordTrace (prefixWord ++ tailWord_866828) baseStart_866828 baseEnd_866828 := by
    simpa [prefixWord, tailWord_866828, baseEnd_866828] using wordTrace_append hprefix tailTrace_866828
  have hstable : (prefixWord ++ tailWord_866828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866828).length < 2 ^ (prefixWord ++ tailWord_866828).sum := by decide
  have hdescent : baseEnd_866828 < baseStart_866828 := by decide
  rcases family_descends (prefixWord ++ tailWord_866828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866855 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 4]
def baseStart_866855 : Nat := 118140960795 + 866855 * 2 ^ 59
def prefixEnd_866855 : Nat := 4983230072969 + 3 ^ 40 * 866855 * 2
def baseEnd_866855 : Nat := 395656242447387697356367

theorem tailTrace_866855 : CollatzResearch.WordTrace tailWord_866855 prefixEnd_866855 395656242447387697356367 := by
  unfold tailWord_866855
  simp only [CollatzResearch.WordTrace]
  refine ⟨31616799274539856892482019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21077866183026571261654679 31616799274539856892482019)
  ·
    refine ⟨47425198911809785338723029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31616799274539856892482019 47425198911809785338723029)
    ·
      refine ⟨1111528099495541843876321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 47425198911809785338723029 1111528099495541843876321)
      ·
        refine ⟨833646074621656382907241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1111528099495541843876321 833646074621656382907241)
        ·
          refine ⟨625234555966242287180431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833646074621656382907241 625234555966242287180431)
          ·
            refine ⟨937851833949363430770647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625234555966242287180431 937851833949363430770647)
            ·
              refine ⟨1406777750924045146155971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937851833949363430770647 1406777750924045146155971)
              ·
                refine ⟨2110166626386067719233957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1406777750924045146155971 2110166626386067719233957)
                ·
                  refine ⟨395656242447387697356367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110166626386067719233957 395656242447387697356367)
                  ·
                    rfl

theorem cell20_866855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4].length) (baseStart_866855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866855 prefixEnd_866855 := by exact prefixLift 866855
  have htrace : WordTrace (prefixWord ++ tailWord_866855) baseStart_866855 baseEnd_866855 := by
    simpa [prefixWord, tailWord_866855, baseEnd_866855] using wordTrace_append hprefix tailTrace_866855
  have hstable : (prefixWord ++ tailWord_866855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866855).length < 2 ^ (prefixWord ++ tailWord_866855).sum := by decide
  have hdescent : baseEnd_866855 < baseStart_866855 := by decide
  rcases family_descends (prefixWord ++ tailWord_866855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866908 : List Nat := [2, 2, 4, 1, 11]
def baseStart_866908 : Nat := 118140960795 + 866908 * 2 ^ 59
def prefixEnd_866908 : Nat := 4983230072969 + 3 ^ 40 * 866908 * 2
def baseEnd_866908 : Nat := 4884943618414260106043

theorem tailTrace_866908 : CollatzResearch.WordTrace tailWord_866908 prefixEnd_866908 4884943618414260106043 := by
  unfold tailWord_866908
  simp only [CollatzResearch.WordTrace]
  refine ⟨15809366171673923472080689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21079154895565231296107585 15809366171673923472080689)
  ·
    refine ⟨11857024628755442604060517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15809366171673923472080689 11857024628755442604060517)
    ·
      refine ⟨2223192117891645488261347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11857024628755442604060517 2223192117891645488261347)
      ·
        refine ⟨3334788176837468232392021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2223192117891645488261347 3334788176837468232392021)
        ·
          refine ⟨4884943618414260106043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3334788176837468232392021 4884943618414260106043)
          ·
            rfl

theorem cell20_866908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 11].length) (baseStart_866908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866908 prefixEnd_866908 := by exact prefixLift 866908
  have htrace : WordTrace (prefixWord ++ tailWord_866908) baseStart_866908 baseEnd_866908 := by
    simpa [prefixWord, tailWord_866908, baseEnd_866908] using wordTrace_append hprefix tailTrace_866908
  have hstable : (prefixWord ++ tailWord_866908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866908).length < 2 ^ (prefixWord ++ tailWord_866908).sum := by decide
  have hdescent : baseEnd_866908 < baseStart_866908 := by decide
  rcases family_descends (prefixWord ++ tailWord_866908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866910 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_866910 : Nat := 118140960795 + 866910 * 2 ^ 59
def prefixEnd_866910 : Nat := 4983230072969 + 3 ^ 40 * 866910 * 2
def baseEnd_866910 : Nat := 395681345946051950522809

theorem tailTrace_866910 : CollatzResearch.WordTrace tailWord_866910 prefixEnd_866910 395681345946051950522809 := by
  unfold tailWord_866910
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952350661167575160716773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21079203526227067523822789 3952350661167575160716773)
  ·
    refine ⟨741065748968920342634395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3952350661167575160716773 741065748968920342634395)
    ·
      refine ⟨1111598623453380513951593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741065748968920342634395 1111598623453380513951593)
      ·
        refine ⟨833698967590035385463695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1111598623453380513951593 833698967590035385463695)
        ·
          refine ⟨1250548451385053078195543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833698967590035385463695 1250548451385053078195543)
          ·
            refine ⟨1875822677077579617293315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250548451385053078195543 1875822677077579617293315)
            ·
              refine ⟨2813734015616369425939973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1875822677077579617293315 2813734015616369425939973)
              ·
                refine ⟨527575127928069267363745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2813734015616369425939973 527575127928069267363745)
                ·
                  refine ⟨395681345946051950522809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527575127928069267363745 395681345946051950522809)
                  ·
                    rfl

theorem cell20_866910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_866910 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866910 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866910 prefixEnd_866910 := by exact prefixLift 866910
  have htrace : WordTrace (prefixWord ++ tailWord_866910) baseStart_866910 baseEnd_866910 := by
    simpa [prefixWord, tailWord_866910, baseEnd_866910] using wordTrace_append hprefix tailTrace_866910
  have hstable : (prefixWord ++ tailWord_866910).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866910).length < 2 ^ (prefixWord ++ tailWord_866910).sum := by decide
  have hdescent : baseEnd_866910 < baseStart_866910 := by decide
  rcases family_descends (prefixWord ++ tailWord_866910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866925 : List Nat := [1, 5, 1, 1, 3, 1, 3, 5]
def baseStart_866925 : Nat := 118140960795 + 866925 * 2 ^ 59
def prefixEnd_866925 : Nat := 4983230072969 + 3 ^ 40 * 866925 * 2
def baseEnd_866925 : Nat := 131896064118259521674249

theorem tailTrace_866925 : CollatzResearch.WordTrace tailWord_866925 prefixEnd_866925 131896064118259521674249 := by
  unfold tailWord_866925
  simp only [CollatzResearch.WordTrace]
  refine ⟨31619352384286258847530229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21079568256190839231686819 31619352384286258847530229)
  ·
    refine ⟨2964314286026836766955959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31619352384286258847530229 2964314286026836766955959)
    ·
      refine ⟨4446471429040255150433939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964314286026836766955959 4446471429040255150433939)
      ·
        refine ⟨6669707143560382725650909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4446471429040255150433939 6669707143560382725650909)
        ·
          refine ⟨2501140178835143522119091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6669707143560382725650909 2501140178835143522119091)
          ·
            refine ⟨3751710268252715283178637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2501140178835143522119091 3751710268252715283178637)
            ·
              refine ⟨1406891350594768231191989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3751710268252715283178637 1406891350594768231191989)
              ·
                refine ⟨131896064118259521674249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1406891350594768231191989 131896064118259521674249)
                ·
                  rfl

theorem cell20_866925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 5].length) (baseStart_866925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866925 prefixEnd_866925 := by exact prefixLift 866925
  have htrace : WordTrace (prefixWord ++ tailWord_866925) baseStart_866925 baseEnd_866925 := by
    simpa [prefixWord, tailWord_866925, baseEnd_866925] using wordTrace_append hprefix tailTrace_866925
  have hstable : (prefixWord ++ tailWord_866925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866925).length < 2 ^ (prefixWord ++ tailWord_866925).sum := by decide
  have hdescent : baseEnd_866925 < baseStart_866925 := by decide
  rcases family_descends (prefixWord ++ tailWord_866925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866953 : List Nat := [1, 2, 1, 1, 4, 1, 1, 4, 5]
def baseStart_866953 : Nat := 118140960795 + 866953 * 2 ^ 59
def prefixEnd_866953 : Nat := 4983230072969 + 3 ^ 40 * 866953 * 2
def baseEnd_866953 : Nat := 395700972317734912089299

theorem tailTrace_866953 : CollatzResearch.WordTrace tailWord_866953 prefixEnd_866953 395700972317734912089299 := by
  unfold tailWord_866953
  simp only [CollatzResearch.WordTrace]
  refine ⟨31620373628184819629549513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21080249085456546419699675 31620373628184819629549513)
  ·
    refine ⟨23715280221138614722162135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31620373628184819629549513 23715280221138614722162135)
    ·
      refine ⟨35572920331707922083243203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23715280221138614722162135 35572920331707922083243203)
      ·
        refine ⟨53359380497561883124864805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35572920331707922083243203 53359380497561883124864805)
        ·
          refine ⟨10004883843292853085912151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53359380497561883124864805 10004883843292853085912151)
          ·
            refine ⟨15007325764939279628868227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10004883843292853085912151 15007325764939279628868227)
            ·
              refine ⟨22510988647408919443302341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15007325764939279628868227 22510988647408919443302341)
              ·
                refine ⟨4220810371389172395619189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22510988647408919443302341 4220810371389172395619189)
                ·
                  refine ⟨395700972317734912089299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4220810371389172395619189 395700972317734912089299)
                  ·
                    rfl

theorem cell20_866953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_866953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866953 prefixEnd_866953 := by exact prefixLift 866953
  have htrace : WordTrace (prefixWord ++ tailWord_866953) baseStart_866953 baseEnd_866953 := by
    simpa [prefixWord, tailWord_866953, baseEnd_866953] using wordTrace_append hprefix tailTrace_866953
  have hstable : (prefixWord ++ tailWord_866953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866953).length < 2 ^ (prefixWord ++ tailWord_866953).sum := by decide
  have hdescent : baseEnd_866953 < baseStart_866953 := by decide
  rcases family_descends (prefixWord ++ tailWord_866953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_866983 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 3]
def baseStart_866983 : Nat := 118140960795 + 866983 * 2 ^ 59
def prefixEnd_866983 : Nat := 4983230072969 + 3 ^ 40 * 866983 * 2
def baseEnd_866983 : Nat := 395714665135188141089177

theorem tailTrace_866983 : CollatzResearch.WordTrace tailWord_866983 prefixEnd_866983 395714665135188141089177 := by
  unfold tailWord_866983
  simp only [CollatzResearch.WordTrace]
  refine ⟨31621467818076134753141603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21080978545384089835427735 31621467818076134753141603)
  ·
    refine ⟨47432201727114202129712405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31621467818076134753141603 47432201727114202129712405)
    ·
      refine ⟨2223384455958478224830269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 47432201727114202129712405 2223384455958478224830269)
      ·
        refine ⟨833769170984429334311351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2223384455958478224830269 833769170984429334311351)
        ·
          refine ⟨1250653756476644001467027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833769170984429334311351 1250653756476644001467027)
          ·
            refine ⟨1875980634714966002200541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250653756476644001467027 1875980634714966002200541)
            ·
              refine ⟨703492738018112250825203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1875980634714966002200541 703492738018112250825203)
              ·
                refine ⟨1055239107027168376237805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703492738018112250825203 1055239107027168376237805)
                ·
                  refine ⟨395714665135188141089177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055239107027168376237805 395714665135188141089177)
                  ·
                    rfl

theorem cell20_866983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_866983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_866983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_866983 prefixEnd_866983 := by exact prefixLift 866983
  have htrace : WordTrace (prefixWord ++ tailWord_866983) baseStart_866983 baseEnd_866983 := by
    simpa [prefixWord, tailWord_866983, baseEnd_866983] using wordTrace_append hprefix tailTrace_866983
  have hstable : (prefixWord ++ tailWord_866983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_866983).length < 2 ^ (prefixWord ++ tailWord_866983).sum := by decide
  have hdescent : baseEnd_866983 < baseStart_866983 := by decide
  rcases family_descends (prefixWord ++ tailWord_866983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867014 : List Nat := [6, 1, 2, 1, 3, 1, 6]
def baseStart_867014 : Nat := 118140960795 + 867014 * 2 ^ 59
def prefixEnd_867014 : Nat := 4983230072969 + 3 ^ 40 * 867014 * 2
def baseEnd_867014 : Nat := 43969868264432201228413

theorem tailTrace_867014 : CollatzResearch.WordTrace tailWord_867014 prefixEnd_867014 43969868264432201228413 := by
  unfold tailWord_867014
  simp only [CollatzResearch.WordTrace]
  refine ⟨988206202530119595235003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21081732320642551365013397 988206202530119595235003)
  ·
    refine ⟨1482309303795179392852505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988206202530119595235003 1482309303795179392852505)
    ·
      refine ⟨1111731977846384544639379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1482309303795179392852505 1111731977846384544639379)
      ·
        refine ⟨1667597966769576816959069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1111731977846384544639379 1667597966769576816959069)
        ·
          refine ⟨625349237538591306359651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1667597966769576816959069 625349237538591306359651)
          ·
            refine ⟨938023856307886959539477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625349237538591306359651 938023856307886959539477)
            ·
              refine ⟨43969868264432201228413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 938023856307886959539477 43969868264432201228413)
              ·
                rfl

theorem cell20_867014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 6].length) (baseStart_867014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867014 prefixEnd_867014 := by exact prefixLift 867014
  have htrace : WordTrace (prefixWord ++ tailWord_867014) baseStart_867014 baseEnd_867014 := by
    simpa [prefixWord, tailWord_867014, baseEnd_867014] using wordTrace_append hprefix tailTrace_867014
  have hstable : (prefixWord ++ tailWord_867014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867014).length < 2 ^ (prefixWord ++ tailWord_867014).sum := by decide
  have hdescent : baseEnd_867014 < baseStart_867014 := by decide
  rcases family_descends (prefixWord ++ tailWord_867014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867022 : List Nat := [4, 1, 1, 1, 3, 2, 8]
def baseStart_867022 : Nat := 118140960795 + 867022 * 2 ^ 59
def prefixEnd_867022 : Nat := 4983230072969 + 3 ^ 40 * 867022 * 2
def baseEnd_867022 : Nat := 43970273977541926532113

theorem tailTrace_867022 : CollatzResearch.WordTrace tailWord_867022 prefixEnd_867022 43970273977541926532113 := by
  unfold tailWord_867022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3952861283116855551726415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21081926843289896275874213 3952861283116855551726415)
  ·
    refine ⟨5929291924675283327589623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3952861283116855551726415 5929291924675283327589623)
    ·
      refine ⟨8893937887012924991384435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929291924675283327589623 8893937887012924991384435)
      ·
        refine ⟨13340906830519387487076653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8893937887012924991384435 13340906830519387487076653)
        ·
          refine ⟨5002840061444770307653745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13340906830519387487076653 5002840061444770307653745)
          ·
            refine ⟨3752130046083577730740309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5002840061444770307653745 3752130046083577730740309)
            ·
              refine ⟨43970273977541926532113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3752130046083577730740309 43970273977541926532113)
              ·
                rfl

theorem cell20_867022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 8].length) (baseStart_867022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867022 prefixEnd_867022 := by exact prefixLift 867022
  have htrace : WordTrace (prefixWord ++ tailWord_867022) baseStart_867022 baseEnd_867022 := by
    simpa [prefixWord, tailWord_867022, baseEnd_867022] using wordTrace_append hprefix tailTrace_867022
  have hstable : (prefixWord ++ tailWord_867022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867022).length < 2 ^ (prefixWord ++ tailWord_867022).sum := by decide
  have hdescent : baseEnd_867022 < baseStart_867022 := by decide
  rcases family_descends (prefixWord ++ tailWord_867022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867028 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_867028 : Nat := 118140960795 + 867028 * 2 ^ 59
def prefixEnd_867028 : Nat := 4983230072969 + 3 ^ 40 * 867028 * 2
def baseEnd_867028 : Nat := 395735204361367984588993

theorem tailTrace_867028 : CollatzResearch.WordTrace tailWord_867028 prefixEnd_867028 395735204361367984588993 := by
  unfold tailWord_867028
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811554551456553719264869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21082072735275404959019825 15811554551456553719264869)
  ·
    refine ⟨2964666478398103822362163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15811554551456553719264869 2964666478398103822362163)
    ·
      refine ⟨4446999717597155733543245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964666478398103822362163 4446999717597155733543245)
      ·
        refine ⟨1667624894098933400078717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4446999717597155733543245 1667624894098933400078717)
        ·
          refine ⟨625359335287100025029519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1667624894098933400078717 625359335287100025029519)
          ·
            refine ⟨938039002930650037544279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625359335287100025029519 938039002930650037544279)
            ·
              refine ⟨1407058504395975056316419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938039002930650037544279 1407058504395975056316419)
              ·
                refine ⟨2110587756593962584474629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407058504395975056316419 2110587756593962584474629)
                ·
                  refine ⟨395735204361367984588993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110587756593962584474629 395735204361367984588993)
                  ·
                    rfl

theorem cell20_867028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_867028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867028 prefixEnd_867028 := by exact prefixLift 867028
  have htrace : WordTrace (prefixWord ++ tailWord_867028) baseStart_867028 baseEnd_867028 := by
    simpa [prefixWord, tailWord_867028, baseEnd_867028] using wordTrace_append hprefix tailTrace_867028
  have hstable : (prefixWord ++ tailWord_867028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867028).length < 2 ^ (prefixWord ++ tailWord_867028).sum := by decide
  have hdescent : baseEnd_867028 < baseStart_867028 := by decide
  rcases family_descends (prefixWord ++ tailWord_867028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867032 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 4]
def baseStart_867032 : Nat := 118140960795 + 867032 * 2 ^ 59
def prefixEnd_867032 : Nat := 4983230072969 + 3 ^ 40 * 867032 * 2
def baseEnd_867032 : Nat := 395737030070361748455643

theorem tailTrace_867032 : CollatzResearch.WordTrace tailWord_867032 prefixEnd_867032 395737030070361748455643 := by
  unfold tailWord_867032
  simp only [CollatzResearch.WordTrace]
  refine ⟨15811627497449308060837675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21082169996599077414450233 15811627497449308060837675)
  ·
    refine ⟨23717441246173962091256513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15811627497449308060837675 23717441246173962091256513)
    ·
      refine ⟨17788080934630471568442385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23717441246173962091256513 17788080934630471568442385)
      ·
        refine ⟨13341060700972853676331789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17788080934630471568442385 13341060700972853676331789)
        ·
          refine ⟨5002897762864820128624421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13341060700972853676331789 5002897762864820128624421)
          ·
            refine ⟨938043330537153774117079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5002897762864820128624421 938043330537153774117079)
            ·
              refine ⟨1407064995805730661175619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 938043330537153774117079 1407064995805730661175619)
              ·
                refine ⟨2110597493708595991763429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407064995805730661175619 2110597493708595991763429)
                ·
                  refine ⟨395737030070361748455643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110597493708595991763429 395737030070361748455643)
                  ·
                    rfl

theorem cell20_867032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_867032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867032 prefixEnd_867032 := by exact prefixLift 867032
  have htrace : WordTrace (prefixWord ++ tailWord_867032) baseStart_867032 baseEnd_867032 := by
    simpa [prefixWord, tailWord_867032, baseEnd_867032] using wordTrace_append hprefix tailTrace_867032
  have hstable : (prefixWord ++ tailWord_867032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867032).length < 2 ^ (prefixWord ++ tailWord_867032).sum := by decide
  have hdescent : baseEnd_867032 < baseStart_867032 := by decide
  rcases family_descends (prefixWord ++ tailWord_867032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867053 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 6]
def baseStart_867053 : Nat := 118140960795 + 867053 * 2 ^ 59
def prefixEnd_867053 : Nat := 4983230072969 + 3 ^ 40 * 867053 * 2
def baseEnd_867053 : Nat := 395746615042579008755557

theorem tailTrace_867053 : CollatzResearch.WordTrace tailWord_867053 prefixEnd_867053 395746615042579008755557 := by
  unfold tailWord_867053
  simp only [CollatzResearch.WordTrace]
  refine ⟨31624020927822536708189813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21082680618548357805459875 31624020927822536708189813)
  ·
    refine ⟨2964751961983362816392795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31624020927822536708189813 2964751961983362816392795)
    ·
      refine ⟨4447127942975044224589193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2964751961983362816392795 4447127942975044224589193)
      ·
        refine ⟨3335345957231283168441895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4447127942975044224589193 3335345957231283168441895)
        ·
          refine ⟨5003018935846924752662843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3335345957231283168441895 5003018935846924752662843)
          ·
            refine ⟨7504528403770387128994265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5003018935846924752662843 7504528403770387128994265)
            ·
              refine ⟨5628396302827790346745699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7504528403770387128994265 5628396302827790346745699)
              ·
                refine ⟨8442594454241685520118549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5628396302827790346745699 8442594454241685520118549)
                ·
                  refine ⟨395746615042579008755557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8442594454241685520118549 395746615042579008755557)
                  ·
                    rfl

theorem cell20_867053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_867053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867053 prefixEnd_867053 := by exact prefixLift 867053
  have htrace : WordTrace (prefixWord ++ tailWord_867053) baseStart_867053 baseEnd_867053 := by
    simpa [prefixWord, tailWord_867053, baseEnd_867053] using wordTrace_append hprefix tailTrace_867053
  have hstable : (prefixWord ++ tailWord_867053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867053).length < 2 ^ (prefixWord ++ tailWord_867053).sum := by decide
  have hdescent : baseEnd_867053 < baseStart_867053 := by decide
  rcases family_descends (prefixWord ++ tailWord_867053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867108 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 4]
def baseStart_867108 : Nat := 118140960795 + 867108 * 2 ^ 59
def prefixEnd_867108 : Nat := 4983230072969 + 3 ^ 40 * 867108 * 2
def baseEnd_867108 : Nat := 395771718541243261921999

theorem tailTrace_867108 : CollatzResearch.WordTrace tailWord_867108 prefixEnd_867108 395771718541243261921999 := by
  unfold tailWord_867108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813013471311640550720989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21084017961748854067627985 15813013471311640550720989)
  ·
    refine ⟨5929880051741865206520371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15813013471311640550720989 5929880051741865206520371)
    ·
      refine ⟨8894820077612797809780557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5929880051741865206520371 8894820077612797809780557)
      ·
        refine ⟨3335557529104799178667709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8894820077612797809780557 3335557529104799178667709)
        ·
          refine ⟨1250834073414299692000391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3335557529104799178667709 1250834073414299692000391)
          ·
            refine ⟨1876251110121449538000587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250834073414299692000391 1876251110121449538000587)
            ·
              refine ⟨2814376665182174307000881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876251110121449538000587 2814376665182174307000881)
              ·
                refine ⟨2110782498886630730250661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2814376665182174307000881 2110782498886630730250661)
                ·
                  refine ⟨395771718541243261921999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110782498886630730250661 395771718541243261921999)
                  ·
                    rfl

theorem cell20_867108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_867108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867108 prefixEnd_867108 := by exact prefixLift 867108
  have htrace : WordTrace (prefixWord ++ tailWord_867108) baseStart_867108 baseEnd_867108 := by
    simpa [prefixWord, tailWord_867108, baseEnd_867108] using wordTrace_append hprefix tailTrace_867108
  have hstable : (prefixWord ++ tailWord_867108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867108).length < 2 ^ (prefixWord ++ tailWord_867108).sum := by decide
  have hdescent : baseEnd_867108 < baseStart_867108 := by decide
  rcases family_descends (prefixWord ++ tailWord_867108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867125 : List Nat := [1, 3, 3, 1, 3, 2, 2, 3, 2]
def baseStart_867125 : Nat := 118140960795 + 867125 * 2 ^ 59
def prefixEnd_867125 : Nat := 4983230072969 + 3 ^ 40 * 867125 * 2
def baseEnd_867125 : Nat := 395779477804466758355263

theorem tailTrace_867125 : CollatzResearch.WordTrace tailWord_867125 prefixEnd_867125 395779477804466758355263 := by
  unfold tailWord_867125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31626646983561693004810829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21084431322374462003207219 31626646983561693004810829)
  ·
    refine ⟨11859992618835634876804061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31626646983561693004810829 11859992618835634876804061)
    ·
      refine ⟨4447497232063363078801523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11859992618835634876804061 4447497232063363078801523)
      ·
        refine ⟨6671245848095044618202285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447497232063363078801523 6671245848095044618202285)
        ·
          refine ⟨2501717193035641731825857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6671245848095044618202285 2501717193035641731825857)
          ·
            refine ⟨1876287894776731298869393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2501717193035641731825857 1876287894776731298869393)
            ·
              refine ⟨1407215921082548474152045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876287894776731298869393 1407215921082548474152045)
              ·
                refine ⟨527705970405955677807017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1407215921082548474152045 527705970405955677807017)
                ·
                  refine ⟨395779477804466758355263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527705970405955677807017 395779477804466758355263)
                  ·
                    rfl

theorem cell20_867125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_867125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867125 prefixEnd_867125 := by exact prefixLift 867125
  have htrace : WordTrace (prefixWord ++ tailWord_867125) baseStart_867125 baseEnd_867125 := by
    simpa [prefixWord, tailWord_867125, baseEnd_867125] using wordTrace_append hprefix tailTrace_867125
  have hstable : (prefixWord ++ tailWord_867125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867125).length < 2 ^ (prefixWord ++ tailWord_867125).sum := by decide
  have hdescent : baseEnd_867125 < baseStart_867125 := by decide
  rcases family_descends (prefixWord ++ tailWord_867125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867142 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 4]
def baseStart_867142 : Nat := 118140960795 + 867142 * 2 ^ 59
def prefixEnd_867142 : Nat := 4983230072969 + 3 ^ 40 * 867142 * 2
def baseEnd_867142 : Nat := 395787237067690254788527

theorem tailTrace_867142 : CollatzResearch.WordTrace tailWord_867142 prefixEnd_867142 395787237067690254788527 := by
  unfold tailWord_867142
  simp only [CollatzResearch.WordTrace]
  refine ⟨988352094515628278380615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21084844683000069938786453 988352094515628278380615)
  ·
    refine ⟨1482528141773442417570923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988352094515628278380615 1482528141773442417570923)
    ·
      refine ⟨2223792212660163626356385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482528141773442417570923 2223792212660163626356385)
      ·
        refine ⟨1667844159495122719767289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2223792212660163626356385 1667844159495122719767289)
        ·
          refine ⟨1250883119621342039825467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1667844159495122719767289 1250883119621342039825467)
          ·
            refine ⟨1876324679432013059738201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250883119621342039825467 1876324679432013059738201)
            ·
              refine ⟨1407243509574009794803651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1876324679432013059738201 1407243509574009794803651)
              ·
                refine ⟨2110865264361014692205477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407243509574009794803651 2110865264361014692205477)
                ·
                  refine ⟨395787237067690254788527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2110865264361014692205477 395787237067690254788527)
                  ·
                    rfl

theorem cell20_867142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_867142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867142 prefixEnd_867142 := by exact prefixLift 867142
  have htrace : WordTrace (prefixWord ++ tailWord_867142) baseStart_867142 baseEnd_867142 := by
    simpa [prefixWord, tailWord_867142, baseEnd_867142] using wordTrace_append hprefix tailTrace_867142
  have hstable : (prefixWord ++ tailWord_867142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867142).length < 2 ^ (prefixWord ++ tailWord_867142).sum := by decide
  have hdescent : baseEnd_867142 < baseStart_867142 := by decide
  rcases family_descends (prefixWord ++ tailWord_867142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867156 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 3]
def baseStart_867156 : Nat := 118140960795 + 867156 * 2 ^ 59
def prefixEnd_867156 : Nat := 4983230072969 + 3 ^ 40 * 867156 * 2
def baseEnd_867156 : Nat := 395793627049168428321803

theorem tailTrace_867156 : CollatzResearch.WordTrace tailWord_867156 prefixEnd_867156 395793627049168428321803 := by
  unfold tailWord_867156
  simp only [CollatzResearch.WordTrace]
  refine ⟨15813888823224692649594661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21085185097632923532792881 15813888823224692649594661)
  ·
    refine ⟨2965104154354629871798999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15813888823224692649594661 2965104154354629871798999)
    ·
      refine ⟨4447656231531944807698499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965104154354629871798999 4447656231531944807698499)
      ·
        refine ⟨6671484347297917211547749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4447656231531944807698499 6671484347297917211547749)
        ·
          refine ⟨1250903315118359477165203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6671484347297917211547749 1250903315118359477165203)
          ·
            refine ⟨1876354972677539215747805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1250903315118359477165203 1876354972677539215747805)
            ·
              refine ⟨703633114754077205905427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1876354972677539215747805 703633114754077205905427)
              ·
                refine ⟨1055449672131115808858141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703633114754077205905427 1055449672131115808858141)
                ·
                  refine ⟨395793627049168428321803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055449672131115808858141 395793627049168428321803)
                  ·
                    rfl

theorem cell20_867156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_867156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867156 prefixEnd_867156 := by exact prefixLift 867156
  have htrace : WordTrace (prefixWord ++ tailWord_867156) baseStart_867156 baseEnd_867156 := by
    simpa [prefixWord, tailWord_867156, baseEnd_867156] using wordTrace_append hprefix tailTrace_867156
  have hstable : (prefixWord ++ tailWord_867156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867156).length < 2 ^ (prefixWord ++ tailWord_867156).sum := by decide
  have hdescent : baseEnd_867156 < baseStart_867156 := by decide
  rcases family_descends (prefixWord ++ tailWord_867156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867184 : List Nat := [2, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_867184 : Nat := 118140960795 + 867184 * 2 ^ 59
def prefixEnd_867184 : Nat := 4983230072969 + 3 ^ 40 * 867184 * 2
def baseEnd_867184 : Nat := 395806407012124775388355

theorem tailTrace_867184 : CollatzResearch.WordTrace tailWord_867184 prefixEnd_867184 395806407012124775388355 := by
  unfold tailWord_867184
  simp only [CollatzResearch.WordTrace]
  refine ⟨15814399445173973040604303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21085865926898630720805737 15814399445173973040604303)
  ·
    refine ⟨23721599167760959560906455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15814399445173973040604303 23721599167760959560906455)
    ·
      refine ⟨35582398751641439341359683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23721599167760959560906455 35582398751641439341359683)
      ·
        refine ⟨53373598127462159012039525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35582398751641439341359683 53373598127462159012039525)
        ·
          refine ⟨10007549648899154814757411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53373598127462159012039525 10007549648899154814757411)
          ·
            refine ⟨15011324473348732222136117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10007549648899154814757411 15011324473348732222136117)
            ·
              refine ⟨1407311669376443645825261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15011324473348732222136117 1407311669376443645825261)
              ·
                refine ⟨527741876016166367184473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1407311669376443645825261 527741876016166367184473)
                ·
                  refine ⟨395806407012124775388355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527741876016166367184473 395806407012124775388355)
                  ·
                    rfl

theorem cell20_867184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_867184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867184 prefixEnd_867184 := by exact prefixLift 867184
  have htrace : WordTrace (prefixWord ++ tailWord_867184) baseStart_867184 baseEnd_867184 := by
    simpa [prefixWord, tailWord_867184, baseEnd_867184] using wordTrace_append hprefix tailTrace_867184
  have hstable : (prefixWord ++ tailWord_867184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867184).length < 2 ^ (prefixWord ++ tailWord_867184).sum := by decide
  have hdescent : baseEnd_867184 < baseStart_867184 := by decide
  rcases family_descends (prefixWord ++ tailWord_867184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867195 : List Nat := [1, 1, 1, 1, 1, 5, 10]
def baseStart_867195 : Nat := 118140960795 + 867195 * 2 ^ 59
def prefixEnd_867195 : Nat := 4983230072969 + 3 ^ 40 * 867195 * 2
def baseEnd_867195 : Nat := 43979047523539736224627

theorem tailTrace_867195 : CollatzResearch.WordTrace tailWord_867195 prefixEnd_867195 43979047523539736224627 := by
  unfold tailWord_867195
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629200093308094959859039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21086133395538729973239359 31629200093308094959859039)
  ·
    refine ⟨47443800139962142439788559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31629200093308094959859039 47443800139962142439788559)
    ·
      refine ⟨71165700209943213659682839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47443800139962142439788559 71165700209943213659682839)
      ·
        refine ⟨106748550314914820489524259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71165700209943213659682839 106748550314914820489524259)
        ·
          refine ⟨160122825472372230734286389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106748550314914820489524259 160122825472372230734286389)
          ·
            refine ⟨15011514888034896631339349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 160122825472372230734286389 15011514888034896631339349)
            ·
              refine ⟨43979047523539736224627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15011514888034896631339349 43979047523539736224627)
              ·
                rfl

theorem cell20_867195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 10].length) (baseStart_867195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867195 prefixEnd_867195 := by exact prefixLift 867195
  have htrace : WordTrace (prefixWord ++ tailWord_867195) baseStart_867195 baseEnd_867195 := by
    simpa [prefixWord, tailWord_867195, baseEnd_867195] using wordTrace_append hprefix tailTrace_867195
  have hstable : (prefixWord ++ tailWord_867195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867195).length < 2 ^ (prefixWord ++ tailWord_867195).sum := by decide
  have hdescent : baseEnd_867195 < baseStart_867195 := by decide
  rcases family_descends (prefixWord ++ tailWord_867195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867205 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 4]
def baseStart_867205 : Nat := 118140960795 + 867205 * 2 ^ 59
def prefixEnd_867205 : Nat := 4983230072969 + 3 ^ 40 * 867205 * 2
def baseEnd_867205 : Nat := 395815991984342035688269

theorem tailTrace_867205 : CollatzResearch.WordTrace tailWord_867205 prefixEnd_867205 395815991984342035688269 := by
  unfold tailWord_867205
  simp only [CollatzResearch.WordTrace]
  refine ⟨31629564823271866667723069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21086376548847911111815379 31629564823271866667723069)
  ·
    refine ⟨11861086808726950000396151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31629564823271866667723069 11861086808726950000396151)
    ·
      refine ⟨17791630213090425000594227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11861086808726950000396151 17791630213090425000594227)
      ·
        refine ⟨26687445319635637500891341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17791630213090425000594227 26687445319635637500891341)
        ·
          refine ⟨10007791994863364062834253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26687445319635637500891341 10007791994863364062834253)
          ·
            refine ⟨3752921998073761523562845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10007791994863364062834253 3752921998073761523562845)
            ·
              refine ⟨1407345749277660571336067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3752921998073761523562845 1407345749277660571336067)
              ·
                refine ⟨2111018623916490857004101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1407345749277660571336067 2111018623916490857004101)
                ·
                  refine ⟨395815991984342035688269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2111018623916490857004101 395815991984342035688269)
                  ·
                    rfl

theorem cell20_867205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_867205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867205 prefixEnd_867205 := by exact prefixLift 867205
  have htrace : WordTrace (prefixWord ++ tailWord_867205) baseStart_867205 baseEnd_867205 := by
    simpa [prefixWord, tailWord_867205, baseEnd_867205] using wordTrace_append hprefix tailTrace_867205
  have hstable : (prefixWord ++ tailWord_867205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867205).length < 2 ^ (prefixWord ++ tailWord_867205).sum := by decide
  have hdescent : baseEnd_867205 < baseStart_867205 := by decide
  rcases family_descends (prefixWord ++ tailWord_867205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867329 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 3]
def baseStart_867329 : Nat := 118140960795 + 867329 * 2 ^ 59
def prefixEnd_867329 : Nat := 4983230072969 + 3 ^ 40 * 867329 * 2
def baseEnd_867329 : Nat := 395872588963148715554429

theorem tailTrace_867329 : CollatzResearch.WordTrace tailWord_867329 prefixEnd_867329 395872588963148715554429 := by
  unfold tailWord_867329
  simp only [CollatzResearch.WordTrace]
  refine ⟨31634087474822635845237041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21089391649881757230158027 31634087474822635845237041)
  ·
    refine ⟨23725565606116976883927781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31634087474822635845237041 23725565606116976883927781)
    ·
      refine ⟨4448543551146933165736459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23725565606116976883927781 4448543551146933165736459)
      ·
        refine ⟨6672815326720399748604689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4448543551146933165736459 6672815326720399748604689)
        ·
          refine ⟨5004611495040299811453517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6672815326720399748604689 5004611495040299811453517)
          ·
            refine ⟨1876729310640112429295069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5004611495040299811453517 1876729310640112429295069)
            ·
              refine ⟨703773491490042160985651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1876729310640112429295069 703773491490042160985651)
              ·
                refine ⟨1055660237235063241478477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703773491490042160985651 1055660237235063241478477)
                ·
                  refine ⟨395872588963148715554429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055660237235063241478477 395872588963148715554429)
                  ·
                    rfl

theorem cell20_867329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_867329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867329 prefixEnd_867329 := by exact prefixLift 867329
  have htrace : WordTrace (prefixWord ++ tailWord_867329) baseStart_867329 baseEnd_867329 := by
    simpa [prefixWord, tailWord_867329, baseEnd_867329] using wordTrace_append hprefix tailTrace_867329
  have hstable : (prefixWord ++ tailWord_867329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867329).length < 2 ^ (prefixWord ++ tailWord_867329).sum := by decide
  have hdescent : baseEnd_867329 < baseStart_867329 := by decide
  rcases family_descends (prefixWord ++ tailWord_867329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867360 : List Nat := [2, 1, 1, 7, 2, 1, 6]
def baseStart_867360 : Nat := 118140960795 + 867360 * 2 ^ 59
def prefixEnd_867360 : Nat := 4983230072969 + 3 ^ 40 * 867360 * 2
def baseEnd_867360 : Nat := 43987415356427820613441

theorem tailTrace_867360 : CollatzResearch.WordTrace tailWord_867360 prefixEnd_867360 43987415356427820613441 := by
  unfold tailWord_867360
  simp only [CollatzResearch.WordTrace]
  refine ⟨15817609068855164069807767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21090145425140218759743689 15817609068855164069807767)
  ·
    refine ⟨23726413603282746104711651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15817609068855164069807767 23726413603282746104711651)
    ·
      refine ⟨35589620404924119157067477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23726413603282746104711651 35589620404924119157067477)
      ·
        refine ⟨834131728240409042743769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35589620404924119157067477 834131728240409042743769)
        ·
          refine ⟨625598796180306782057827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834131728240409042743769 625598796180306782057827)
          ·
            refine ⟨938398194270460173086741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625598796180306782057827 938398194270460173086741)
            ·
              refine ⟨43987415356427820613441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 938398194270460173086741 43987415356427820613441)
              ·
                rfl

theorem cell20_867360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 6].length) (baseStart_867360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867360 prefixEnd_867360 := by exact prefixLift 867360
  have htrace : WordTrace (prefixWord ++ tailWord_867360) baseStart_867360 baseEnd_867360 := by
    simpa [prefixWord, tailWord_867360, baseEnd_867360] using wordTrace_append hprefix tailTrace_867360
  have hstable : (prefixWord ++ tailWord_867360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867360).length < 2 ^ (prefixWord ++ tailWord_867360).sum := by decide
  have hdescent : baseEnd_867360 < baseStart_867360 := by decide
  rcases family_descends (prefixWord ++ tailWord_867360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867364 : List Nat := [2, 3, 1, 4, 1, 1, 8]
def baseStart_867364 : Nat := 118140960795 + 867364 * 2 ^ 59
def prefixEnd_867364 : Nat := 4983230072969 + 3 ^ 40 * 867364 * 2
def baseEnd_867364 : Nat := 43987618212982683265291

theorem tailTrace_867364 : CollatzResearch.WordTrace tailWord_867364 prefixEnd_867364 43987618212982683265291 := by
  unfold tailWord_867364
  simp only [CollatzResearch.WordTrace]
  refine ⟨15817682014847918411380573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21090242686463891215174097 15817682014847918411380573)
  ·
    refine ⟨5931630755567969404267715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15817682014847918411380573 5931630755567969404267715)
    ·
      refine ⟨8897446133351954106401573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5931630755567969404267715 8897446133351954106401573)
      ·
        refine ⟨1668271150003491394950295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8897446133351954106401573 1668271150003491394950295)
        ·
          refine ⟨2502406725005237092425443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668271150003491394950295 2502406725005237092425443)
          ·
            refine ⟨3753610087507855638638165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502406725005237092425443 3753610087507855638638165)
            ·
              refine ⟨43987618212982683265291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3753610087507855638638165 43987618212982683265291)
              ·
                rfl

theorem cell20_867364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 8].length) (baseStart_867364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867364 prefixEnd_867364 := by exact prefixLift 867364
  have htrace : WordTrace (prefixWord ++ tailWord_867364) baseStart_867364 baseEnd_867364 := by
    simpa [prefixWord, tailWord_867364, baseEnd_867364] using wordTrace_append hprefix tailTrace_867364
  have hstable : (prefixWord ++ tailWord_867364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867364).length < 2 ^ (prefixWord ++ tailWord_867364).sum := by decide
  have hdescent : baseEnd_867364 < baseStart_867364 := by decide
  rcases family_descends (prefixWord ++ tailWord_867364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867370 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_867370 : Nat := 118140960795 + 867370 * 2 ^ 59
def prefixEnd_867370 : Nat := 4983230072969 + 3 ^ 40 * 867370 * 2
def baseEnd_867370 : Nat := 395891302480334795187595

theorem tailTrace_867370 : CollatzResearch.WordTrace tailWord_867370 prefixEnd_867370 395891302480334795187595 := by
  unfold tailWord_867370
  simp only [CollatzResearch.WordTrace]
  refine ⟨7908895716918524961869891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21090388578449399898319709 7908895716918524961869891)
  ·
    refine ⟨11863343575377787442804837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7908895716918524961869891 11863343575377787442804837)
    ·
      refine ⟨2224376920383335145525907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11863343575377787442804837 2224376920383335145525907)
      ·
        refine ⟨3336565380575002718288861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2224376920383335145525907 3336565380575002718288861)
        ·
          refine ⟨1251212017715626019358323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3336565380575002718288861 1251212017715626019358323)
          ·
            refine ⟨1876818026573439029037485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1251212017715626019358323 1876818026573439029037485)
            ·
              refine ⟨703806759965039635889057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1876818026573439029037485 703806759965039635889057)
              ·
                refine ⟨527855069973779726916793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 703806759965039635889057 527855069973779726916793)
                ·
                  refine ⟨395891302480334795187595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 527855069973779726916793 395891302480334795187595)
                  ·
                    rfl

theorem cell20_867370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_867370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867370 prefixEnd_867370 := by exact prefixLift 867370
  have htrace : WordTrace (prefixWord ++ tailWord_867370) baseStart_867370 baseEnd_867370 := by
    simpa [prefixWord, tailWord_867370, baseEnd_867370] using wordTrace_append hprefix tailTrace_867370
  have hstable : (prefixWord ++ tailWord_867370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867370).length < 2 ^ (prefixWord ++ tailWord_867370).sum := by decide
  have hdescent : baseEnd_867370 < baseStart_867370 := by decide
  rcases family_descends (prefixWord ++ tailWord_867370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867371 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 3]
def baseStart_867371 : Nat := 118140960795 + 867371 * 2 ^ 59
def prefixEnd_867371 : Nat := 4983230072969 + 3 ^ 40 * 867371 * 2
def baseEnd_867371 : Nat := 395891758907583236154257

theorem tailTrace_867371 : CollatzResearch.WordTrace tailWord_867371 prefixEnd_867371 395891758907583236154257 := by
  unfold tailWord_867371
  simp only [CollatzResearch.WordTrace]
  refine ⟨31635619340670477018265967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21090412893780318012177311 31635619340670477018265967)
  ·
    refine ⟨47453429011005715527398951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31635619340670477018265967 47453429011005715527398951)
    ·
      refine ⟨71180143516508573291098427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47453429011005715527398951 71180143516508573291098427)
      ·
        refine ⟨106770215274762859936647641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71180143516508573291098427 106770215274762859936647641)
        ·
          refine ⟨80077661456072144952485731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106770215274762859936647641 80077661456072144952485731)
          ·
            refine ⟨120116492184108217428728597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80077661456072144952485731 120116492184108217428728597)
            ·
              refine ⟨5630460571130072691971653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120116492184108217428728597 5630460571130072691971653)
              ·
                refine ⟨1055711357086888629744685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5630460571130072691971653 1055711357086888629744685)
                ·
                  refine ⟨395891758907583236154257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055711357086888629744685 395891758907583236154257)
                  ·
                    rfl

theorem cell20_867371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 3].length) (baseStart_867371 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867371 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867371 prefixEnd_867371 := by exact prefixLift 867371
  have htrace : WordTrace (prefixWord ++ tailWord_867371) baseStart_867371 baseEnd_867371 := by
    simpa [prefixWord, tailWord_867371, baseEnd_867371] using wordTrace_append hprefix tailTrace_867371
  have hstable : (prefixWord ++ tailWord_867371).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867371).length < 2 ^ (prefixWord ++ tailWord_867371).sum := by decide
  have hdescent : baseEnd_867371 < baseStart_867371 := by decide
  rcases family_descends (prefixWord ++ tailWord_867371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867388 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_867388 : Nat := 118140960795 + 867388 * 2 ^ 59
def prefixEnd_867388 : Nat := 4983230072969 + 3 ^ 40 * 867388 * 2
def baseEnd_867388 : Nat := 395899518170806732587521

theorem tailTrace_867388 : CollatzResearch.WordTrace tailWord_867388 prefixEnd_867388 395899518170806732587521 := by
  unfold tailWord_867388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15818119690804444460817409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21090826254405925947756545 15818119690804444460817409)
  ·
    refine ⟨11863589768103333345613057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15818119690804444460817409 11863589768103333345613057)
    ·
      refine ⟨8897692326077500009209793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11863589768103333345613057 8897692326077500009209793)
      ·
        refine ⟨6673269244558125006907345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8897692326077500009209793 6673269244558125006907345)
        ·
          refine ⟨5004951933418593755180509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6673269244558125006907345 5004951933418593755180509)
          ·
            refine ⟨1876856975031972658192691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5004951933418593755180509 1876856975031972658192691)
            ·
              refine ⟨2815285462547958987289037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1876856975031972658192691 2815285462547958987289037)
              ·
                refine ⟨1055732048455484620233389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2815285462547958987289037 1055732048455484620233389)
                ·
                  refine ⟨395899518170806732587521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055732048455484620233389 395899518170806732587521)
                  ·
                    rfl

theorem cell20_867388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_867388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867388 prefixEnd_867388 := by exact prefixLift 867388
  have htrace : WordTrace (prefixWord ++ tailWord_867388) baseStart_867388 baseEnd_867388 := by
    simpa [prefixWord, tailWord_867388, baseEnd_867388] using wordTrace_append hprefix tailTrace_867388
  have hstable : (prefixWord ++ tailWord_867388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867388).length < 2 ^ (prefixWord ++ tailWord_867388).sum := by decide
  have hdescent : baseEnd_867388 < baseStart_867388 := by decide
  rcases family_descends (prefixWord ++ tailWord_867388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867422 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 3]
def baseStart_867422 : Nat := 118140960795 + 867422 * 2 ^ 59
def prefixEnd_867422 : Nat := 4983230072969 + 3 ^ 40 * 867422 * 2
def baseEnd_867422 : Nat := 395915036697253725454049

theorem tailTrace_867422 : CollatzResearch.WordTrace tailWord_867422 prefixEnd_867422 395915036697253725454049 := by
  unfold tailWord_867422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954684932935714091046565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21091652975657141818915013 3954684932935714091046565)
  ·
    refine ⟨741503424925446392071231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3954684932935714091046565 741503424925446392071231)
    ·
      refine ⟨1112255137388169588106847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741503424925446392071231 1112255137388169588106847)
      ·
        refine ⟨1668382706082254382160271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112255137388169588106847 1668382706082254382160271)
        ·
          refine ⟨2502574059123381573240407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668382706082254382160271 2502574059123381573240407)
          ·
            refine ⟨3753861088685072359860611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2502574059123381573240407 3753861088685072359860611)
            ·
              refine ⟨5630791633027608539790917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3753861088685072359860611 5630791633027608539790917)
              ·
                refine ⟨1055773431192676601210797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5630791633027608539790917 1055773431192676601210797)
                ·
                  refine ⟨395915036697253725454049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055773431192676601210797 395915036697253725454049)
                  ·
                    rfl

theorem cell20_867422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_867422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867422 prefixEnd_867422 := by exact prefixLift 867422
  have htrace : WordTrace (prefixWord ++ tailWord_867422) baseStart_867422 baseEnd_867422 := by
    simpa [prefixWord, tailWord_867422, baseEnd_867422] using wordTrace_append hprefix tailTrace_867422
  have hstable : (prefixWord ++ tailWord_867422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867422).length < 2 ^ (prefixWord ++ tailWord_867422).sum := by decide
  have hdescent : baseEnd_867422 < baseStart_867422 := by decide
  rcases family_descends (prefixWord ++ tailWord_867422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867447 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 3]
def baseStart_867447 : Nat := 118140960795 + 867447 * 2 ^ 59
def prefixEnd_867447 : Nat := 4983230072969 + 3 ^ 40 * 867447 * 2
def baseEnd_867447 : Nat := 395926447378464749620613

theorem tailTrace_867447 : CollatzResearch.WordTrace tailWord_867447 prefixEnd_867447 395926447378464749620613 := by
  unfold tailWord_867447
  simp only [CollatzResearch.WordTrace]
  refine ⟨31638391288395141998032595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21092260858930094665355063 31638391288395141998032595)
  ·
    refine ⟨47457586932592712997048893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31638391288395141998032595 47457586932592712997048893)
    ·
      refine ⟨17796595099722267373893335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47457586932592712997048893 17796595099722267373893335)
      ·
        refine ⟨26694892649583401060840003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17796595099722267373893335 26694892649583401060840003)
        ·
          refine ⟨40042338974375101591260005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26694892649583401060840003 40042338974375101591260005)
          ·
            refine ⟨7507938557695331548361251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40042338974375101591260005 7507938557695331548361251)
            ·
              refine ⟨11261907836542997322541877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7507938557695331548361251 11261907836542997322541877)
              ·
                refine ⟨1055803859675905998988301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11261907836542997322541877 1055803859675905998988301)
                ·
                  refine ⟨395926447378464749620613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055803859675905998988301 395926447378464749620613)
                  ·
                    rfl

theorem cell20_867447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 3].length) (baseStart_867447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867447 prefixEnd_867447 := by exact prefixLift 867447
  have htrace : WordTrace (prefixWord ++ tailWord_867447) baseStart_867447 baseEnd_867447 := by
    simpa [prefixWord, tailWord_867447, baseEnd_867447] using wordTrace_append hprefix tailTrace_867447
  have hstable : (prefixWord ++ tailWord_867447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867447).length < 2 ^ (prefixWord ++ tailWord_867447).sum := by decide
  have hdescent : baseEnd_867447 < baseStart_867447 := by decide
  rcases family_descends (prefixWord ++ tailWord_867447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867457 : List Nat := [1, 2, 4, 2, 2, 2, 3, 4]
def baseStart_867457 : Nat := 118140960795 + 867457 * 2 ^ 59
def prefixEnd_867457 : Nat := 4983230072969 + 3 ^ 40 * 867457 * 2
def baseEnd_867457 : Nat := 131977003883649719762413

theorem tailTrace_867457 : CollatzResearch.WordTrace tailWord_867457 prefixEnd_867457 131977003883649719762413 := by
  unfold tailWord_867457
  simp only [CollatzResearch.WordTrace]
  refine ⟨31638756018358913705896625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21092504012239275803931083 31638756018358913705896625)
  ·
    refine ⟨23729067013769185279422469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31638756018358913705896625 23729067013769185279422469)
    ·
      refine ⟨4449200065081722239891713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23729067013769185279422469 4449200065081722239891713)
      ·
        refine ⟨3336900048811291679918785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4449200065081722239891713 3336900048811291679918785)
        ·
          refine ⟨2502675036608468759939089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3336900048811291679918785 2502675036608468759939089)
          ·
            refine ⟨1877006277456351569954317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502675036608468759939089 1877006277456351569954317)
            ·
              refine ⟨703877354046131838732869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877006277456351569954317 703877354046131838732869)
              ·
                refine ⟨131977003883649719762413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 703877354046131838732869 131977003883649719762413)
                ·
                  rfl

theorem cell20_867457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 4].length) (baseStart_867457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867457 prefixEnd_867457 := by exact prefixLift 867457
  have htrace : WordTrace (prefixWord ++ tailWord_867457) baseStart_867457 baseEnd_867457 := by
    simpa [prefixWord, tailWord_867457, baseEnd_867457] using wordTrace_append hprefix tailTrace_867457
  have hstable : (prefixWord ++ tailWord_867457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867457).length < 2 ^ (prefixWord ++ tailWord_867457).sum := by decide
  have hdescent : baseEnd_867457 < baseStart_867457 := by decide
  rcases family_descends (prefixWord ++ tailWord_867457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867485 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 5]
def baseStart_867485 : Nat := 118140960795 + 867485 * 2 ^ 59
def prefixEnd_867485 : Nat := 4983230072969 + 3 ^ 40 * 867485 * 2
def baseEnd_867485 : Nat := 395943791613905506353791

theorem tailTrace_867485 : CollatzResearch.WordTrace tailWord_867485 prefixEnd_867485 395943791613905506353791 := by
  unfold tailWord_867485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31639777262257474487915909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21093184841504982991943939 31639777262257474487915909)
  ·
    refine ⟨5932458236673276466484233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31639777262257474487915909 5932458236673276466484233)
    ·
      refine ⟨4449343677504957349863175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5932458236673276466484233 4449343677504957349863175)
      ·
        refine ⟨6674015516257436024794763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4449343677504957349863175 6674015516257436024794763)
        ·
          refine ⟨10011023274386154037192145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6674015516257436024794763 10011023274386154037192145)
          ·
            refine ⟨7508267455789615527894109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10011023274386154037192145 7508267455789615527894109)
            ·
              refine ⟨2815600295921105822960291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7508267455789615527894109 2815600295921105822960291)
              ·
                refine ⟨4223400443881658734440437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2815600295921105822960291 4223400443881658734440437)
                ·
                  refine ⟨395943791613905506353791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4223400443881658734440437 395943791613905506353791)
                  ·
                    rfl

theorem cell20_867485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_867485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867485 prefixEnd_867485 := by exact prefixLift 867485
  have htrace : WordTrace (prefixWord ++ tailWord_867485) baseStart_867485 baseEnd_867485 := by
    simpa [prefixWord, tailWord_867485, baseEnd_867485] using wordTrace_append hprefix tailTrace_867485
  have hstable : (prefixWord ++ tailWord_867485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867485).length < 2 ^ (prefixWord ++ tailWord_867485).sum := by decide
  have hdescent : baseEnd_867485 < baseStart_867485 := by decide
  rcases family_descends (prefixWord ++ tailWord_867485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867498 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_867498 : Nat := 118140960795 + 867498 * 2 ^ 59
def prefixEnd_867498 : Nat := 4983230072969 + 3 ^ 40 * 867498 * 2
def baseEnd_867498 : Nat := 395949725168135238920405

theorem tailTrace_867498 : CollatzResearch.WordTrace tailWord_867498 prefixEnd_867498 395949725168135238920405 := by
  unfold tailWord_867498
  simp only [CollatzResearch.WordTrace]
  refine ⟨7910062852802594427034787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21093500940806918472092765 7910062852802594427034787)
  ·
    refine ⟨11865094279203891640552181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7910062852802594427034787 11865094279203891640552181)
    ·
      refine ⟨1112352588675364841301767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11865094279203891640552181 1112352588675364841301767)
      ·
        refine ⟨1668528883013047261952651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1112352588675364841301767 1668528883013047261952651)
        ·
          refine ⟨2502793324519570892928977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1668528883013047261952651 2502793324519570892928977)
          ·
            refine ⟨1877094993389678169696733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502793324519570892928977 1877094993389678169696733)
            ·
              refine ⟨703910622521129313636275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1877094993389678169696733 703910622521129313636275)
              ·
                refine ⟨1055865933781693970454413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 703910622521129313636275 1055865933781693970454413)
                ·
                  refine ⟨395949725168135238920405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1055865933781693970454413 395949725168135238920405)
                  ·
                    rfl

theorem cell20_867498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_867498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867498 prefixEnd_867498 := by exact prefixLift 867498
  have htrace : WordTrace (prefixWord ++ tailWord_867498) baseStart_867498 baseEnd_867498 := by
    simpa [prefixWord, tailWord_867498, baseEnd_867498] using wordTrace_append hprefix tailTrace_867498
  have hstable : (prefixWord ++ tailWord_867498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867498).length < 2 ^ (prefixWord ++ tailWord_867498).sum := by decide
  have hdescent : baseEnd_867498 < baseStart_867498 := by decide
  rcases family_descends (prefixWord ++ tailWord_867498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867516 : List Nat := [2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_867516 : Nat := 118140960795 + 867516 * 2 ^ 59
def prefixEnd_867516 : Nat := 4983230072969 + 3 ^ 40 * 867516 * 2
def baseEnd_867516 : Nat := 131985980286202392106777

theorem tailTrace_867516 : CollatzResearch.WordTrace tailWord_867516 prefixEnd_867516 131985980286202392106777 := by
  unfold tailWord_867516
  simp only [CollatzResearch.WordTrace]
  refine ⟨15820453962572583391147201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21093938616763444521529601 15820453962572583391147201)
  ·
    refine ⟨11865340471929437543360401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15820453962572583391147201 11865340471929437543360401)
    ·
      refine ⟨8899005353947078157520301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11865340471929437543360401 8899005353947078157520301)
      ·
        refine ⟨3337127007730154309070113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8899005353947078157520301 3337127007730154309070113)
        ·
          refine ⟨2502845255797615731802585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3337127007730154309070113 2502845255797615731802585)
          ·
            refine ⟨1877133941848211798851939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2502845255797615731802585 1877133941848211798851939)
            ·
              refine ⟨2815700912772317698277909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877133941848211798851939 2815700912772317698277909)
              ·
                refine ⟨131985980286202392106777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2815700912772317698277909 131985980286202392106777)
                ·
                  rfl

theorem cell20_867516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_867516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867516 prefixEnd_867516 := by exact prefixLift 867516
  have htrace : WordTrace (prefixWord ++ tailWord_867516) baseStart_867516 baseEnd_867516 := by
    simpa [prefixWord, tailWord_867516, baseEnd_867516] using wordTrace_append hprefix tailTrace_867516
  have hstable : (prefixWord ++ tailWord_867516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867516).length < 2 ^ (prefixWord ++ tailWord_867516).sum := by decide
  have hdescent : baseEnd_867516 < baseStart_867516 := by decide
  rcases family_descends (prefixWord ++ tailWord_867516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867592 : List Nat := [2, 1, 3, 2, 5, 7]
def baseStart_867592 : Nat := 118140960795 + 867592 * 2 ^ 59
def prefixEnd_867592 : Nat := 4983230072969 + 3 ^ 40 * 867592 * 2
def baseEnd_867592 : Nat := 14666393678869951473581

theorem tailTrace_867592 : CollatzResearch.WordTrace tailWord_867592 prefixEnd_867592 14666393678869951473581 := by
  unfold tailWord_867592
  simp only [CollatzResearch.WordTrace]
  refine ⟨15821839936434915881030515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21095786581913221174707353 15821839936434915881030515)
  ·
    refine ⟨23732759904652373821545773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15821839936434915881030515 23732759904652373821545773)
    ·
      refine ⟨8899784964244640183079665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23732759904652373821545773 8899784964244640183079665)
      ·
        refine ⟨6674838723183480137309749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8899784964244640183079665 6674838723183480137309749)
        ·
          refine ⟨625766130298451262872789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6674838723183480137309749 625766130298451262872789)
          ·
            refine ⟨14666393678869951473581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 625766130298451262872789 14666393678869951473581)
            ·
              rfl

theorem cell20_867592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 7].length) (baseStart_867592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867592 prefixEnd_867592 := by exact prefixLift 867592
  have htrace : WordTrace (prefixWord ++ tailWord_867592) baseStart_867592 baseEnd_867592 := by
    simpa [prefixWord, tailWord_867592, baseEnd_867592] using wordTrace_append hprefix tailTrace_867592
  have hstable : (prefixWord ++ tailWord_867592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867592).length < 2 ^ (prefixWord ++ tailWord_867592).sum := by decide
  have hdescent : baseEnd_867592 < baseStart_867592 := by decide
  rcases family_descends (prefixWord ++ tailWord_867592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867696 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 7]
def baseStart_867696 : Nat := 118140960795 + 867696 * 2 ^ 59
def prefixEnd_867696 : Nat := 4983230072969 + 3 ^ 40 * 867696 * 2
def baseEnd_867696 : Nat := 396040097763326550319595

theorem tailTrace_867696 : CollatzResearch.WordTrace tailWord_867696 prefixEnd_867696 396040097763326550319595 := by
  unfold tailWord_867696
  simp only [CollatzResearch.WordTrace]
  refine ⟨15823736532246528761923471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21098315376328705015897961 15823736532246528761923471)
  ·
    refine ⟨23735604798369793142885207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15823736532246528761923471 23735604798369793142885207)
    ·
      refine ⟨35603407197554689714327811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23735604798369793142885207 35603407197554689714327811)
      ·
        refine ⟨53405110796332034571491717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35603407197554689714327811 53405110796332034571491717)
        ·
          refine ⟨10013458274312256482154697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53405110796332034571491717 10013458274312256482154697)
          ·
            refine ⟨7510093705734192361616023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10013458274312256482154697 7510093705734192361616023)
            ·
              refine ⟨11265140558601288542424035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7510093705734192361616023 11265140558601288542424035)
              ·
                refine ⟨16897710837901932813636053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11265140558601288542424035 16897710837901932813636053)
                ·
                  refine ⟨396040097763326550319595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16897710837901932813636053 396040097763326550319595)
                  ·
                    rfl

theorem cell20_867696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_867696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867696 prefixEnd_867696 := by exact prefixLift 867696
  have htrace : WordTrace (prefixWord ++ tailWord_867696) baseStart_867696 baseEnd_867696 := by
    simpa [prefixWord, tailWord_867696, baseEnd_867696] using wordTrace_append hprefix tailTrace_867696
  have hstable : (prefixWord ++ tailWord_867696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867696).length < 2 ^ (prefixWord ++ tailWord_867696).sum := by decide
  have hdescent : baseEnd_867696 < baseStart_867696 := by decide
  rcases family_descends (prefixWord ++ tailWord_867696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867726 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 3]
def baseStart_867726 : Nat := 118140960795 + 867726 * 2 ^ 59
def prefixEnd_867726 : Nat := 4983230072969 + 3 ^ 40 * 867726 * 2
def baseEnd_867726 : Nat := 396053790580779779319473

theorem tailTrace_867726 : CollatzResearch.WordTrace tailWord_867726 prefixEnd_867726 396053790580779779319473 := by
  unfold tailWord_867726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956070906798046580929879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21099044836256248431626021 3956070906798046580929879)
  ·
    refine ⟨5934106360197069871394819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956070906798046580929879 5934106360197069871394819)
    ·
      refine ⟨8901159540295604807092229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934106360197069871394819 8901159540295604807092229)
      ·
        refine ⟨1668967413805425901329793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8901159540295604807092229 1668967413805425901329793)
        ·
          refine ⟨1251725560354069425997345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1668967413805425901329793 1251725560354069425997345)
          ·
            refine ⟨938794170265552069498009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1251725560354069425997345 938794170265552069498009)
            ·
              refine ⟨704095627699164052123507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938794170265552069498009 704095627699164052123507)
              ·
                refine ⟨1056143441548746078185261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704095627699164052123507 1056143441548746078185261)
                ·
                  refine ⟨396053790580779779319473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056143441548746078185261 396053790580779779319473)
                  ·
                    rfl

theorem cell20_867726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_867726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867726 prefixEnd_867726 := by exact prefixLift 867726
  have htrace : WordTrace (prefixWord ++ tailWord_867726) baseStart_867726 baseEnd_867726 := by
    simpa [prefixWord, tailWord_867726, baseEnd_867726] using wordTrace_append hprefix tailTrace_867726
  have hstable : (prefixWord ++ tailWord_867726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867726).length < 2 ^ (prefixWord ++ tailWord_867726).sum := by decide
  have hdescent : baseEnd_867726 < baseStart_867726 := by decide
  rcases family_descends (prefixWord ++ tailWord_867726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867765 : List Nat := [1, 3, 3, 2, 2, 9]
def baseStart_867765 : Nat := 118140960795 + 867765 * 2 ^ 59
def prefixEnd_867765 : Nat := 4983230072969 + 3 ^ 40 * 867765 * 2
def baseEnd_867765 : Nat := 14669318194202554704419

theorem tailTrace_867765 : CollatzResearch.WordTrace tailWord_867765 prefixEnd_867765 14669318194202554704419 := by
  unfold tailWord_867765
  simp only [CollatzResearch.WordTrace]
  refine ⟨31649989701243082308108749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21099993134162054872072499 31649989701243082308108749)
  ·
    refine ⟨11868746137966155865540781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31649989701243082308108749 11868746137966155865540781)
    ·
      refine ⟨4450779801737308449577793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11868746137966155865540781 4450779801737308449577793)
      ·
        refine ⟨3338084851302981337183345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4450779801737308449577793 3338084851302981337183345)
        ·
          refine ⟨2503563638477236002887509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3338084851302981337183345 2503563638477236002887509)
          ·
            refine ⟨14669318194202554704419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2503563638477236002887509 14669318194202554704419)
            ·
              rfl

theorem cell20_867765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 9].length) (baseStart_867765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867765 prefixEnd_867765 := by exact prefixLift 867765
  have htrace : WordTrace (prefixWord ++ tailWord_867765) baseStart_867765 baseEnd_867765 := by
    simpa [prefixWord, tailWord_867765, baseEnd_867765] using wordTrace_append hprefix tailTrace_867765
  have hstable : (prefixWord ++ tailWord_867765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867765).length < 2 ^ (prefixWord ++ tailWord_867765).sum := by decide
  have hdescent : baseEnd_867765 < baseStart_867765 := by decide
  rcases family_descends (prefixWord ++ tailWord_867765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867830 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_867830 : Nat := 118140960795 + 867830 * 2 ^ 59
def prefixEnd_867830 : Nat := 4983230072969 + 3 ^ 40 * 867830 * 2
def baseEnd_867830 : Nat := 396101259014617639852381

theorem tailTrace_867830 : CollatzResearch.WordTrace tailWord_867830 prefixEnd_867830 396101259014617639852381 := by
  unfold tailWord_867830
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978272527875474900576559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21101573630671732272816629 1978272527875474900576559)
  ·
    refine ⟨2967408791813212350864839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978272527875474900576559 2967408791813212350864839)
    ·
      refine ⟨4451113187719818526297259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967408791813212350864839 4451113187719818526297259)
      ·
        refine ⟨6676669781579727789445889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4451113187719818526297259 6676669781579727789445889)
        ·
          refine ⟨5007502336184795842084417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6676669781579727789445889 5007502336184795842084417)
          ·
            refine ⟨3755626752138596881563313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5007502336184795842084417 3755626752138596881563313)
            ·
              refine ⟨2816720064103947661172485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3755626752138596881563313 2816720064103947661172485)
              ·
                refine ⟨528135012019490186469841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2816720064103947661172485 528135012019490186469841)
                ·
                  refine ⟨396101259014617639852381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528135012019490186469841 396101259014617639852381)
                  ·
                    rfl

theorem cell20_867830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_867830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867830 prefixEnd_867830 := by exact prefixLift 867830
  have htrace : WordTrace (prefixWord ++ tailWord_867830) baseStart_867830 baseEnd_867830 := by
    simpa [prefixWord, tailWord_867830, baseEnd_867830] using wordTrace_append hprefix tailTrace_867830
  have hstable : (prefixWord ++ tailWord_867830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867830).length < 2 ^ (prefixWord ++ tailWord_867830).sum := by decide
  have hdescent : baseEnd_867830 < baseStart_867830 := by decide
  rcases family_descends (prefixWord ++ tailWord_867830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867834 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 4]
def baseStart_867834 : Nat := 118140960795 + 867834 * 2 ^ 59
def prefixEnd_867834 : Nat := 4983230072969 + 3 ^ 40 * 867834 * 2
def baseEnd_867834 : Nat := 396103084723611403719031

theorem tailTrace_867834 : CollatzResearch.WordTrace tailWord_867834 prefixEnd_867834 396103084723611403719031 := by
  unfold tailWord_867834
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913126584498276773092639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21101670891995404728247037 7913126584498276773092639)
  ·
    refine ⟨11869689876747415159638959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7913126584498276773092639 11869689876747415159638959)
    ·
      refine ⟨17804534815121122739458439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11869689876747415159638959 17804534815121122739458439)
      ·
        refine ⟨26706802222681684109187659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17804534815121122739458439 26706802222681684109187659)
        ·
          refine ⟨40060203334022526163781489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26706802222681684109187659 40060203334022526163781489)
          ·
            refine ⟨30045152500516894622836117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40060203334022526163781489 30045152500516894622836117)
            ·
              refine ⟨1408366523461729435445443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 30045152500516894622836117 1408366523461729435445443)
              ·
                refine ⟨2112549785192594153168165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408366523461729435445443 2112549785192594153168165)
                ·
                  refine ⟨396103084723611403719031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2112549785192594153168165 396103084723611403719031)
                  ·
                    rfl

theorem cell20_867834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_867834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867834 prefixEnd_867834 := by exact prefixLift 867834
  have htrace : WordTrace (prefixWord ++ tailWord_867834) baseStart_867834 baseEnd_867834 := by
    simpa [prefixWord, tailWord_867834, baseEnd_867834] using wordTrace_append hprefix tailTrace_867834
  have hstable : (prefixWord ++ tailWord_867834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867834).length < 2 ^ (prefixWord ++ tailWord_867834).sum := by decide
  have hdescent : baseEnd_867834 < baseStart_867834 := by decide
  rcases family_descends (prefixWord ++ tailWord_867834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867854 : List Nat := [4, 1, 1, 2, 5, 1, 2, 4]
def baseStart_867854 : Nat := 118140960795 + 867854 * 2 ^ 59
def prefixEnd_867854 : Nat := 4983230072969 + 3 ^ 40 * 867854 * 2
def baseEnd_867854 : Nat := 132037404422860074350761

theorem tailTrace_867854 : CollatzResearch.WordTrace tailWord_867854 prefixEnd_867854 132037404422860074350761 := by
  unfold tailWord_867854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3956654474740081313512327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21102157198613767005399077 3956654474740081313512327)
  ·
    refine ⟨5934981712110121970268491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3956654474740081313512327 5934981712110121970268491)
    ·
      refine ⟨8902472568165182955402737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5934981712110121970268491 8902472568165182955402737)
      ·
        refine ⟨6676854426123887216552053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8902472568165182955402737 6676854426123887216552053)
        ·
          refine ⟨625955102449114426551755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6676854426123887216552053 625955102449114426551755)
          ·
            refine ⟨938932653673671639827633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 625955102449114426551755 938932653673671639827633)
            ·
              refine ⟨704199490255253729870725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 938932653673671639827633 704199490255253729870725)
              ·
                refine ⟨132037404422860074350761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704199490255253729870725 132037404422860074350761)
                ·
                  rfl

theorem cell20_867854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_867854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867854 prefixEnd_867854 := by exact prefixLift 867854
  have htrace : WordTrace (prefixWord ++ tailWord_867854) baseStart_867854 baseEnd_867854 := by
    simpa [prefixWord, tailWord_867854, baseEnd_867854] using wordTrace_append hprefix tailTrace_867854
  have hstable : (prefixWord ++ tailWord_867854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867854).length < 2 ^ (prefixWord ++ tailWord_867854).sum := by decide
  have hdescent : baseEnd_867854 < baseStart_867854 := by decide
  rcases family_descends (prefixWord ++ tailWord_867854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867903 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 3]
def baseStart_867903 : Nat := 118140960795 + 867903 * 2 ^ 59
def prefixEnd_867903 : Nat := 4983230072969 + 3 ^ 40 * 867903 * 2
def baseEnd_867903 : Nat := 396134578203753830418749

theorem tailTrace_867903 : CollatzResearch.WordTrace tailWord_867903 prefixEnd_867903 396134578203753830418749 := by
  unfold tailWord_867903
  simp only [CollatzResearch.WordTrace]
  refine ⟨31655022974743131876632363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21103348649828754584421575 31655022974743131876632363)
  ·
    refine ⟨47482534462114697814948545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31655022974743131876632363 47482534462114697814948545)
    ·
      refine ⟨35611900846586023361211409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47482534462114697814948545 35611900846586023361211409)
      ·
        refine ⟨26708925634939517520908557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35611900846586023361211409 26708925634939517520908557)
        ·
          refine ⟨10015847113102319070340709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26708925634939517520908557 10015847113102319070340709)
          ·
            refine ⟨1877971333706684825688883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10015847113102319070340709 1877971333706684825688883)
            ·
              refine ⟨2816957000560027238533325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1877971333706684825688883 2816957000560027238533325)
              ·
                refine ⟨1056358875210010214449997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2816957000560027238533325 1056358875210010214449997)
                ·
                  refine ⟨396134578203753830418749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056358875210010214449997 396134578203753830418749)
                  ·
                    rfl

theorem cell20_867903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 3].length) (baseStart_867903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867903 prefixEnd_867903 := by exact prefixLift 867903
  have htrace : WordTrace (prefixWord ++ tailWord_867903) baseStart_867903 baseEnd_867903 := by
    simpa [prefixWord, tailWord_867903, baseEnd_867903] using wordTrace_append hprefix tailTrace_867903
  have hstable : (prefixWord ++ tailWord_867903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867903).length < 2 ^ (prefixWord ++ tailWord_867903).sum := by decide
  have hdescent : baseEnd_867903 < baseStart_867903 := by decide
  rcases family_descends (prefixWord ++ tailWord_867903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867934 : List Nat := [4, 4, 1, 11]
def baseStart_867934 : Nat := 118140960795 + 867934 * 2 ^ 59
def prefixEnd_867934 : Nat := 4983230072969 + 3 ^ 40 * 867934 * 2
def baseEnd_867934 : Nat := 1630241676742615227923

theorem tailTrace_867934 : CollatzResearch.WordTrace tailWord_867934 prefixEnd_867934 1630241676742615227923 := by
  unfold tailWord_867934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957019204703853021376357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21104102425087216114007237 3957019204703853021376357)
  ·
    refine ⟨741941100881972441508067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3957019204703853021376357 741941100881972441508067)
    ·
      refine ⟨1112911651322958662262101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 741941100881972441508067 1112911651322958662262101)
      ·
        refine ⟨1630241676742615227923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1112911651322958662262101 1630241676742615227923)
        ·
          rfl

theorem cell20_867934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 11].length) (baseStart_867934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867934 prefixEnd_867934 := by exact prefixLift 867934
  have htrace : WordTrace (prefixWord ++ tailWord_867934) baseStart_867934 baseEnd_867934 := by
    simpa [prefixWord, tailWord_867934, baseEnd_867934] using wordTrace_append hprefix tailTrace_867934
  have hstable : (prefixWord ++ tailWord_867934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867934).length < 2 ^ (prefixWord ++ tailWord_867934).sum := by decide
  have hdescent : baseEnd_867934 < baseStart_867934 := by decide
  rcases family_descends (prefixWord ++ tailWord_867934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867941 : List Nat := [1, 3, 1, 3, 3, 1, 1, 4, 3]
def baseStart_867941 : Nat := 118140960795 + 867941 * 2 ^ 59
def prefixEnd_867941 : Nat := 4983230072969 + 3 ^ 40 * 867941 * 2
def baseEnd_867941 : Nat := 396151922439194587151927

theorem tailTrace_867941 : CollatzResearch.WordTrace tailWord_867941 prefixEnd_867941 396151922439194587151927 := by
  unfold tailWord_867941
  simp only [CollatzResearch.WordTrace]
  refine ⟨31656408948605464366515677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21104272632403642911010451 31656408948605464366515677)
  ·
    refine ⟨11871153355727049137443379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31656408948605464366515677 11871153355727049137443379)
    ·
      refine ⟨17806730033590573706165069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11871153355727049137443379 17806730033590573706165069)
      ·
        refine ⟨6677523762596465139811901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17806730033590573706165069 6677523762596465139811901)
        ·
          refine ⟨2504071410973674427429463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6677523762596465139811901 2504071410973674427429463)
          ·
            refine ⟨3756107116460511641144195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504071410973674427429463 3756107116460511641144195)
            ·
              refine ⟨5634160674690767461716293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3756107116460511641144195 5634160674690767461716293)
              ·
                refine ⟨1056405126504518899071805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5634160674690767461716293 1056405126504518899071805)
                ·
                  refine ⟨396151922439194587151927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056405126504518899071805 396151922439194587151927)
                  ·
                    rfl

theorem cell20_867941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_867941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867941 prefixEnd_867941 := by exact prefixLift 867941
  have htrace : WordTrace (prefixWord ++ tailWord_867941) baseStart_867941 baseEnd_867941 := by
    simpa [prefixWord, tailWord_867941, baseEnd_867941] using wordTrace_append hprefix tailTrace_867941
  have hstable : (prefixWord ++ tailWord_867941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867941).length < 2 ^ (prefixWord ++ tailWord_867941).sum := by decide
  have hdescent : baseEnd_867941 < baseStart_867941 := by decide
  rcases family_descends (prefixWord ++ tailWord_867941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867944 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 2]
def baseStart_867944 : Nat := 118140960795 + 867944 * 2 ^ 59
def prefixEnd_867944 : Nat := 4983230072969 + 3 ^ 40 * 867944 * 2
def baseEnd_867944 : Nat := 396153291720939910051915

theorem tailTrace_867944 : CollatzResearch.WordTrace tailWord_867944 prefixEnd_867944 396153291720939910051915 := by
  unfold tailWord_867944
  simp only [CollatzResearch.WordTrace]
  refine ⟨15828259183797297939437443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21104345578396397252583257 15828259183797297939437443)
  ·
    refine ⟨23742388775695946909156165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15828259183797297939437443 23742388775695946909156165)
    ·
      refine ⟨4451697895442990045466781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23742388775695946909156165 4451697895442990045466781)
      ·
        refine ⟨1669386710791121267050043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4451697895442990045466781 1669386710791121267050043)
        ·
          refine ⟨2504080066186681900575065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1669386710791121267050043 2504080066186681900575065)
          ·
            refine ⟨1878060049640011425431299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2504080066186681900575065 1878060049640011425431299)
            ·
              refine ⟨2817090074460017138146949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878060049640011425431299 2817090074460017138146949)
              ·
                refine ⟨528204388961253213402553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2817090074460017138146949 528204388961253213402553)
                ·
                  refine ⟨396153291720939910051915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528204388961253213402553 396153291720939910051915)
                  ·
                    rfl

theorem cell20_867944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 2].length) (baseStart_867944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867944 prefixEnd_867944 := by exact prefixLift 867944
  have htrace : WordTrace (prefixWord ++ tailWord_867944) baseStart_867944 baseEnd_867944 := by
    simpa [prefixWord, tailWord_867944, baseEnd_867944] using wordTrace_append hprefix tailTrace_867944
  have hstable : (prefixWord ++ tailWord_867944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867944).length < 2 ^ (prefixWord ++ tailWord_867944).sum := by decide
  have hdescent : baseEnd_867944 < baseStart_867944 := by decide
  rcases family_descends (prefixWord ++ tailWord_867944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867958 : List Nat := [5, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_867958 : Nat := 118140960795 + 867958 * 2 ^ 59
def prefixEnd_867958 : Nat := 4983230072969 + 3 ^ 40 * 867958 * 2
def baseEnd_867958 : Nat := 396159681702418083585191

theorem tailTrace_867958 : CollatzResearch.WordTrace tailWord_867958 prefixEnd_867958 396159681702418083585191 := by
  unfold tailWord_867958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978564311846492266867783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21104685993029250846589685 1978564311846492266867783)
  ·
    refine ⟨2967846467769738400301675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1978564311846492266867783 2967846467769738400301675)
    ·
      refine ⟨4451769701654607600452513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2967846467769738400301675 4451769701654607600452513)
      ·
        refine ⟨3338827276240955700339385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4451769701654607600452513 3338827276240955700339385)
        ·
          refine ⟨2504120457180716775254539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3338827276240955700339385 2504120457180716775254539)
          ·
            refine ⟨3756180685771075162881809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504120457180716775254539 3756180685771075162881809)
            ·
              refine ⟨2817135514328306372161357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3756180685771075162881809 2817135514328306372161357)
              ·
                refine ⟨1056425817873114889560509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2817135514328306372161357 1056425817873114889560509)
                ·
                  refine ⟨396159681702418083585191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056425817873114889560509 396159681702418083585191)
                  ·
                    rfl

theorem cell20_867958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_867958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867958 prefixEnd_867958 := by exact prefixLift 867958
  have htrace : WordTrace (prefixWord ++ tailWord_867958) baseStart_867958 baseEnd_867958 := by
    simpa [prefixWord, tailWord_867958, baseEnd_867958] using wordTrace_append hprefix tailTrace_867958
  have hstable : (prefixWord ++ tailWord_867958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867958).length < 2 ^ (prefixWord ++ tailWord_867958).sum := by decide
  have hdescent : baseEnd_867958 < baseStart_867958 := by decide
  rcases family_descends (prefixWord ++ tailWord_867958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_867982 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_867982 : Nat := 118140960795 + 867982 * 2 ^ 59
def prefixEnd_867982 : Nat := 4983230072969 + 3 ^ 40 * 867982 * 2
def baseEnd_867982 : Nat := 396170635956380666785093

theorem tailTrace_867982 : CollatzResearch.WordTrace tailWord_867982 prefixEnd_867982 396170635956380666785093 := by
  unfold tailWord_867982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3957238042682116046094775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21105269560971285579172133 3957238042682116046094775)
  ·
    refine ⟨5935857064023174069142163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3957238042682116046094775 5935857064023174069142163)
    ·
      refine ⟨8903785596034761103713245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5935857064023174069142163 8903785596034761103713245)
      ·
        refine ⟨3338919598513035413892467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8903785596034761103713245 3338919598513035413892467)
        ·
          refine ⟨5008379397769553120838701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3338919598513035413892467 5008379397769553120838701)
          ·
            refine ⟨1878142274163582420314513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5008379397769553120838701 1878142274163582420314513)
            ·
              refine ⟨1408606705622686815235885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878142274163582420314513 1408606705622686815235885)
              ·
                refine ⟨528227514608507555713457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1408606705622686815235885 528227514608507555713457)
                ·
                  refine ⟨396170635956380666785093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528227514608507555713457 396170635956380666785093)
                  ·
                    rfl

theorem cell20_867982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_867982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_867982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_867982 prefixEnd_867982 := by exact prefixLift 867982
  have htrace : WordTrace (prefixWord ++ tailWord_867982) baseStart_867982 baseEnd_867982 := by
    simpa [prefixWord, tailWord_867982, baseEnd_867982] using wordTrace_append hprefix tailTrace_867982
  have hstable : (prefixWord ++ tailWord_867982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_867982).length < 2 ^ (prefixWord ++ tailWord_867982).sum := by decide
  have hdescent : baseEnd_867982 < baseStart_867982 := by decide
  rcases family_descends (prefixWord ++ tailWord_867982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868054 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_868054 : Nat := 118140960795 + 868054 * 2 ^ 59
def prefixEnd_868054 : Nat := 4983230072969 + 3 ^ 40 * 868054 * 2
def baseEnd_868054 : Nat := 396203498718268416384799

theorem tailTrace_868054 : CollatzResearch.WordTrace tailWord_868054 prefixEnd_868054 396203498718268416384799 := by
  unfold tailWord_868054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1978783149824755291586201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21107020264797389776919477 1978783149824755291586201)
  ·
    refine ⟨1484087362368566468689651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1978783149824755291586201 1484087362368566468689651)
    ·
      refine ⟨2226131043552849703034477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484087362368566468689651 2226131043552849703034477)
      ·
        refine ⟨834799141332318638637929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2226131043552849703034477 834799141332318638637929)
        ·
          refine ⟨626099355999238978978447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834799141332318638637929 626099355999238978978447)
          ·
            refine ⟨939149033998858468467671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 626099355999238978978447 939149033998858468467671)
            ·
              refine ⟨1408723550998287702701507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939149033998858468467671 1408723550998287702701507)
              ·
                refine ⟨2113085326497431554052261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1408723550998287702701507 2113085326497431554052261)
                ·
                  refine ⟨396203498718268416384799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113085326497431554052261 396203498718268416384799)
                  ·
                    rfl

theorem cell20_868054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_868054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868054 prefixEnd_868054 := by exact prefixLift 868054
  have htrace : WordTrace (prefixWord ++ tailWord_868054) baseStart_868054 baseEnd_868054 := by
    simpa [prefixWord, tailWord_868054, baseEnd_868054] using wordTrace_append hprefix tailTrace_868054
  have hstable : (prefixWord ++ tailWord_868054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868054).length < 2 ^ (prefixWord ++ tailWord_868054).sum := by decide
  have hdescent : baseEnd_868054 < baseStart_868054 := by decide
  rcases family_descends (prefixWord ++ tailWord_868054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868058 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 2]
def baseStart_868058 : Nat := 118140960795 + 868058 * 2 ^ 59
def prefixEnd_868058 : Nat := 4983230072969 + 3 ^ 40 * 868058 * 2
def baseEnd_868058 : Nat := 396205324427262180251449

theorem tailTrace_868058 : CollatzResearch.WordTrace tailWord_868058 prefixEnd_868058 396205324427262180251449 := by
  unfold tailWord_868058
  simp only [CollatzResearch.WordTrace]
  refine ⟨7915169072295398337131207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21107117526121062232349885 7915169072295398337131207)
  ·
    refine ⟨11872753608443097505696811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7915169072295398337131207 11872753608443097505696811)
    ·
      refine ⟨17809130412664646258545217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11872753608443097505696811 17809130412664646258545217)
      ·
        refine ⟨13356847809498484693908913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17809130412664646258545217 13356847809498484693908913)
        ·
          refine ⟨10017635857123863520431685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13356847809498484693908913 10017635857123863520431685)
          ·
            refine ⟨1878306723210724410080941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10017635857123863520431685 1878306723210724410080941)
            ·
              refine ⟨704365021204021653780353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1878306723210724410080941 704365021204021653780353)
              ·
                refine ⟨528273765903016240335265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704365021204021653780353 528273765903016240335265)
                ·
                  refine ⟨396205324427262180251449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528273765903016240335265 396205324427262180251449)
                  ·
                    rfl

theorem cell20_868058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_868058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868058 prefixEnd_868058 := by exact prefixLift 868058
  have htrace : WordTrace (prefixWord ++ tailWord_868058) baseStart_868058 baseEnd_868058 := by
    simpa [prefixWord, tailWord_868058, baseEnd_868058] using wordTrace_append hprefix tailTrace_868058
  have hstable : (prefixWord ++ tailWord_868058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868058).length < 2 ^ (prefixWord ++ tailWord_868058).sum := by decide
  have hdescent : baseEnd_868058 < baseStart_868058 := by decide
  rcases family_descends (prefixWord ++ tailWord_868058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868069 : List Nat := [1, 3, 1, 4, 1, 1, 4, 5]
def baseStart_868069 : Nat := 118140960795 + 868069 * 2 ^ 59
def prefixEnd_868069 : Nat := 4983230072969 + 3 ^ 40 * 868069 * 2
def baseEnd_868069 : Nat := 132070115042331676961579

theorem tailTrace_868069 : CollatzResearch.WordTrace tailWord_868069 prefixEnd_868069 132070115042331676961579 := by
  unfold tailWord_868069
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661077492141742227175261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21107384994761161484783507 31661077492141742227175261)
  ·
    refine ⟨11872904059553153335190723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31661077492141742227175261 11872904059553153335190723)
    ·
      refine ⟨17809356089329730002786085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11872904059553153335190723 17809356089329730002786085)
      ·
        refine ⟨3339254266749324375522391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17809356089329730002786085 3339254266749324375522391)
        ·
          refine ⟨5008881400123986563283587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3339254266749324375522391 5008881400123986563283587)
          ·
            refine ⟨7513322100185979844925381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008881400123986563283587 7513322100185979844925381)
            ·
              refine ⟨1408747893784871220923509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7513322100185979844925381 1408747893784871220923509)
              ·
                refine ⟨132070115042331676961579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1408747893784871220923509 132070115042331676961579)
                ·
                  rfl

theorem cell20_868069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 5].length) (baseStart_868069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868069 prefixEnd_868069 := by exact prefixLift 868069
  have htrace : WordTrace (prefixWord ++ tailWord_868069) baseStart_868069 baseEnd_868069 := by
    simpa [prefixWord, tailWord_868069, baseEnd_868069] using wordTrace_append hprefix tailTrace_868069
  have hstable : (prefixWord ++ tailWord_868069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868069).length < 2 ^ (prefixWord ++ tailWord_868069).sum := by decide
  have hdescent : baseEnd_868069 < baseStart_868069 := by decide
  rcases family_descends (prefixWord ++ tailWord_868069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868072 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_868072 : Nat := 118140960795 + 868072 * 2 ^ 59
def prefixEnd_868072 : Nat := 4983230072969 + 3 ^ 40 * 868072 * 2
def baseEnd_868072 : Nat := 396211714408740353784725

theorem tailTrace_868072 : CollatzResearch.WordTrace tailWord_868072 prefixEnd_868072 396211714408740353784725 := by
  unfold tailWord_868072
  simp only [CollatzResearch.WordTrace]
  refine ⟨15830593455565436869767235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21107457940753915826356313 15830593455565436869767235)
  ·
    refine ⟨23745890183348155304650853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15830593455565436869767235 23745890183348155304650853)
    ·
      refine ⟨4452354409377779119622035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23745890183348155304650853 4452354409377779119622035)
      ·
        refine ⟨6678531614066668679433053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4452354409377779119622035 6678531614066668679433053)
        ·
          refine ⟨2504449355275000754787395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6678531614066668679433053 2504449355275000754787395)
          ·
            refine ⟨3756674032912501132181093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2504449355275000754787395 3756674032912501132181093)
            ·
              refine ⟨704376381171093962283955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3756674032912501132181093 704376381171093962283955)
              ·
                refine ⟨1056564571756640943425933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 704376381171093962283955 1056564571756640943425933)
                ·
                  refine ⟨396211714408740353784725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056564571756640943425933 396211714408740353784725)
                  ·
                    rfl

theorem cell20_868072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_868072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868072 prefixEnd_868072 := by exact prefixLift 868072
  have htrace : WordTrace (prefixWord ++ tailWord_868072) baseStart_868072 baseEnd_868072 := by
    simpa [prefixWord, tailWord_868072, baseEnd_868072] using wordTrace_append hprefix tailTrace_868072
  have hstable : (prefixWord ++ tailWord_868072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868072).length < 2 ^ (prefixWord ++ tailWord_868072).sum := by decide
  have hdescent : baseEnd_868072 < baseStart_868072 := by decide
  rcases family_descends (prefixWord ++ tailWord_868072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868083 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 4]
def baseStart_868083 : Nat := 118140960795 + 868083 * 2 ^ 59
def prefixEnd_868083 : Nat := 4983230072969 + 3 ^ 40 * 868083 * 2
def baseEnd_868083 : Nat := 396216735108473204418013

theorem tailTrace_868083 : CollatzResearch.WordTrace tailWord_868083 prefixEnd_868083 396216735108473204418013 := by
  unfold tailWord_868083
  simp only [CollatzResearch.WordTrace]
  refine ⟨31661588114091022618184903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21107725409394015078789935 31661588114091022618184903)
  ·
    refine ⟨47492382171136533927277355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31661588114091022618184903 47492382171136533927277355)
    ·
      refine ⟨71238573256704800890916033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47492382171136533927277355 71238573256704800890916033)
      ·
        refine ⟨53428929942528600668187025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71238573256704800890916033 53428929942528600668187025)
        ·
          refine ⟨40071697456896450501140269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53428929942528600668187025 40071697456896450501140269)
          ·
            refine ⟨15026886546336168937927601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40071697456896450501140269 15026886546336168937927601)
            ·
              refine ⟨11270164909752126703445701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15026886546336168937927601 11270164909752126703445701)
              ·
                refine ⟨2113155920578523756896069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11270164909752126703445701 2113155920578523756896069)
                ·
                  refine ⟨396216735108473204418013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113155920578523756896069 396216735108473204418013)
                  ·
                    rfl

theorem cell20_868083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 4].length) (baseStart_868083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868083 prefixEnd_868083 := by exact prefixLift 868083
  have htrace : WordTrace (prefixWord ++ tailWord_868083) baseStart_868083 baseEnd_868083 := by
    simpa [prefixWord, tailWord_868083, baseEnd_868083] using wordTrace_append hprefix tailTrace_868083
  have hstable : (prefixWord ++ tailWord_868083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868083).length < 2 ^ (prefixWord ++ tailWord_868083).sum := by decide
  have hdescent : baseEnd_868083 < baseStart_868083 := by decide
  rcases family_descends (prefixWord ++ tailWord_868083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868102 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_868102 : Nat := 118140960795 + 868102 * 2 ^ 59
def prefixEnd_868102 : Nat := 4983230072969 + 3 ^ 40 * 868102 * 2
def baseEnd_868102 : Nat := 396225407226193582784603

theorem tailTrace_868102 : CollatzResearch.WordTrace tailWord_868102 prefixEnd_868102 396225407226193582784603 := by
  unfold tailWord_868102
  simp only [CollatzResearch.WordTrace]
  refine ⟨989446284406943401972705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21108187400681459242084373 989446284406943401972705)
  ·
    refine ⟨742084713305207551479529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 989446284406943401972705 742084713305207551479529)
    ·
      refine ⟨556563534978905663609647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742084713305207551479529 556563534978905663609647)
      ·
        refine ⟨834845302468358495414471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556563534978905663609647 834845302468358495414471)
        ·
          refine ⟨1252267953702537743121707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834845302468358495414471 1252267953702537743121707)
          ·
            refine ⟨1878401930553806614682561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252267953702537743121707 1878401930553806614682561)
            ·
              refine ⟨1408801447915354961011921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1878401930553806614682561 1408801447915354961011921)
              ·
                refine ⟨1056601085936516220758941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1408801447915354961011921 1056601085936516220758941)
                ·
                  refine ⟨396225407226193582784603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056601085936516220758941 396225407226193582784603)
                  ·
                    rfl

theorem cell20_868102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_868102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868102 prefixEnd_868102 := by exact prefixLift 868102
  have htrace : WordTrace (prefixWord ++ tailWord_868102) baseStart_868102 baseEnd_868102 := by
    simpa [prefixWord, tailWord_868102, baseEnd_868102] using wordTrace_append hprefix tailTrace_868102
  have hstable : (prefixWord ++ tailWord_868102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868102).length < 2 ^ (prefixWord ++ tailWord_868102).sum := by decide
  have hdescent : baseEnd_868102 < baseStart_868102 := by decide
  rcases family_descends (prefixWord ++ tailWord_868102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868109 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 2]
def baseStart_868109 : Nat := 118140960795 + 868109 * 2 ^ 59
def prefixEnd_868109 : Nat := 4983230072969 + 3 ^ 40 * 868109 * 2
def baseEnd_868109 : Nat := 396228602216932669551241

theorem tailTrace_868109 : CollatzResearch.WordTrace tailWord_868109 prefixEnd_868109 396228602216932669551241 := by
  unfold tailWord_868109
  simp only [CollatzResearch.WordTrace]
  refine ⟨31662536411996829058631381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21108357607997886039087587 31662536411996829058631381)
  ·
    refine ⟨742090697156175681061673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31662536411996829058631381 742090697156175681061673)
    ·
      refine ⟨556568022867131760796255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742090697156175681061673 556568022867131760796255)
      ·
        refine ⟨834852034300697641194383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 556568022867131760796255 834852034300697641194383)
        ·
          refine ⟨1252278051451046461791575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 834852034300697641194383 1252278051451046461791575)
          ·
            refine ⟨1878417077176569692687363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252278051451046461791575 1878417077176569692687363)
            ·
              refine ⟨2817625615764854539031045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878417077176569692687363 2817625615764854539031045)
              ·
                refine ⟨528304802955910226068321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2817625615764854539031045 528304802955910226068321)
                ·
                  refine ⟨396228602216932669551241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528304802955910226068321 396228602216932669551241)
                  ·
                    rfl

theorem cell20_868109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_868109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868109 prefixEnd_868109 := by exact prefixLift 868109
  have htrace : WordTrace (prefixWord ++ tailWord_868109) baseStart_868109 baseEnd_868109 := by
    simpa [prefixWord, tailWord_868109, baseEnd_868109] using wordTrace_append hprefix tailTrace_868109
  have hstable : (prefixWord ++ tailWord_868109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868109).length < 2 ^ (prefixWord ++ tailWord_868109).sum := by decide
  have hdescent : baseEnd_868109 < baseStart_868109 := by decide
  rcases family_descends (prefixWord ++ tailWord_868109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868117 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 2]
def baseStart_868117 : Nat := 118140960795 + 868117 * 2 ^ 59
def prefixEnd_868117 : Nat := 4983230072969 + 3 ^ 40 * 868117 * 2
def baseEnd_868117 : Nat := 396232253634920197284541

theorem tailTrace_868117 : CollatzResearch.WordTrace tailWord_868117 prefixEnd_868117 396232253634920197284541 := by
  unfold tailWord_868117
  simp only [CollatzResearch.WordTrace]
  refine ⟨31662828195967846424922605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21108552130645230949948403 31662828195967846424922605)
  ·
    refine ⟨11873560573487942409345977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31662828195967846424922605 11873560573487942409345977)
    ·
      refine ⟨8905170430115956807009483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11873560573487942409345977 8905170430115956807009483)
      ·
        refine ⟨13357755645173935210514225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8905170430115956807009483 13357755645173935210514225)
        ·
          refine ⟨10018316733880451407885669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13357755645173935210514225 10018316733880451407885669)
          ·
            refine ⟨1878434387602584638978563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10018316733880451407885669 1878434387602584638978563)
            ·
              refine ⟨2817651581403876958467845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878434387602584638978563 2817651581403876958467845)
              ·
                refine ⟨528309671513226929712721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2817651581403876958467845 528309671513226929712721)
                ·
                  refine ⟨396232253634920197284541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528309671513226929712721 396232253634920197284541)
                  ·
                    rfl

theorem cell20_868117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_868117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868117 prefixEnd_868117 := by exact prefixLift 868117
  have htrace : WordTrace (prefixWord ++ tailWord_868117) baseStart_868117 baseEnd_868117 := by
    simpa [prefixWord, tailWord_868117, baseEnd_868117] using wordTrace_append hprefix tailTrace_868117
  have hstable : (prefixWord ++ tailWord_868117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868117).length < 2 ^ (prefixWord ++ tailWord_868117).sum := by decide
  have hdescent : baseEnd_868117 < baseStart_868117 := by decide
  rcases family_descends (prefixWord ++ tailWord_868117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868228 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 5]
def baseStart_868228 : Nat := 118140960795 + 868228 * 2 ^ 59
def prefixEnd_868228 : Nat := 4983230072969 + 3 ^ 40 * 868228 * 2
def baseEnd_868228 : Nat := 396282917059497144584087

theorem tailTrace_868228 : CollatzResearch.WordTrace tailWord_868228 prefixEnd_868228 396282917059497144584087 := by
  unfold tailWord_868228
  simp only [CollatzResearch.WordTrace]
  refine ⟨15833438349282856191106669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21111251132377141588142225 15833438349282856191106669)
  ·
    refine ⟨5937539380981071071665001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15833438349282856191106669 5937539380981071071665001)
    ·
      refine ⟨4453154535735803303748751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5937539380981071071665001 4453154535735803303748751)
      ·
        refine ⟨6679731803603704955623127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453154535735803303748751 6679731803603704955623127)
        ·
          refine ⟨10019597705405557433434691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679731803603704955623127 10019597705405557433434691)
          ·
            refine ⟨15029396558108336150152037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019597705405557433434691 15029396558108336150152037)
            ·
              refine ⟨2818011854645313028153507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15029396558108336150152037 2818011854645313028153507)
              ·
                refine ⟨4227017781967969542230261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2818011854645313028153507 4227017781967969542230261)
                ·
                  refine ⟨396282917059497144584087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227017781967969542230261 396282917059497144584087)
                  ·
                    rfl

theorem cell20_868228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_868228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868228 prefixEnd_868228 := by exact prefixLift 868228
  have htrace : WordTrace (prefixWord ++ tailWord_868228) baseStart_868228 baseEnd_868228 := by
    simpa [prefixWord, tailWord_868228, baseEnd_868228] using wordTrace_append hprefix tailTrace_868228
  have hstable : (prefixWord ++ tailWord_868228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868228).length < 2 ^ (prefixWord ++ tailWord_868228).sum := by decide
  have hdescent : baseEnd_868228 < baseStart_868228 := by decide
  rcases family_descends (prefixWord ++ tailWord_868228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868231 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 4]
def baseStart_868231 : Nat := 118140960795 + 868231 * 2 ^ 59
def prefixEnd_868231 : Nat := 4983230072969 + 3 ^ 40 * 868231 * 2
def baseEnd_868231 : Nat := 396284286341242467484075

theorem tailTrace_868231 : CollatzResearch.WordTrace tailWord_868231 prefixEnd_868231 396284286341242467484075 := by
  unfold tailWord_868231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31666986117554843894572547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21111324078369895929715031 31666986117554843894572547)
  ·
    refine ⟨47500479176332265841858821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31666986117554843894572547 47500479176332265841858821)
    ·
      refine ⟨8906339845562299845348529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47500479176332265841858821 8906339845562299845348529)
      ·
        refine ⟨6679754884171724884011397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8906339845562299845348529 6679754884171724884011397)
        ·
          refine ⟨1252454040782198415752137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6679754884171724884011397 1252454040782198415752137)
          ·
            refine ⟨939340530586648811814103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252454040782198415752137 939340530586648811814103)
            ·
              refine ⟨1409010795879973217721155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939340530586648811814103 1409010795879973217721155)
              ·
                refine ⟨2113516193819959826581733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409010795879973217721155 2113516193819959826581733)
                ·
                  refine ⟨396284286341242467484075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113516193819959826581733 396284286341242467484075)
                  ·
                    rfl

theorem cell20_868231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 4].length) (baseStart_868231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868231 prefixEnd_868231 := by exact prefixLift 868231
  have htrace : WordTrace (prefixWord ++ tailWord_868231) baseStart_868231 baseEnd_868231 := by
    simpa [prefixWord, tailWord_868231, baseEnd_868231] using wordTrace_append hprefix tailTrace_868231
  have hstable : (prefixWord ++ tailWord_868231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868231).length < 2 ^ (prefixWord ++ tailWord_868231).sum := by decide
  have hdescent : baseEnd_868231 < baseStart_868231 := by decide
  rcases family_descends (prefixWord ++ tailWord_868231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868276 : List Nat := [2, 5, 2, 1, 2, 8]
def baseStart_868276 : Nat := 118140960795 + 868276 * 2 ^ 59
def prefixEnd_868276 : Nat := 4983230072969 + 3 ^ 40 * 868276 * 2
def baseEnd_868276 : Nat := 14677956502497122629033

theorem tailTrace_868276 : CollatzResearch.WordTrace tailWord_868276 prefixEnd_868276 14677956502497122629033 := by
  unfold tailWord_868276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834313701195908289980341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21112418268261211053307121 15834313701195908289980341)
  ·
    refine ⟨1484466909487116402185657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15834313701195908289980341 1484466909487116402185657)
    ·
      refine ⟨1113350182115337301639243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1484466909487116402185657 1113350182115337301639243)
      ·
        refine ⟨1670025273173005952458865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1113350182115337301639243 1670025273173005952458865)
        ·
          refine ⟨1252518954879754464344149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670025273173005952458865 1252518954879754464344149)
          ·
            refine ⟨14677956502497122629033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1252518954879754464344149 14677956502497122629033)
            ·
              rfl

theorem cell20_868276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 8].length) (baseStart_868276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868276 prefixEnd_868276 := by exact prefixLift 868276
  have htrace : WordTrace (prefixWord ++ tailWord_868276) baseStart_868276 baseEnd_868276 := by
    simpa [prefixWord, tailWord_868276, baseEnd_868276] using wordTrace_append hprefix tailTrace_868276
  have hstable : (prefixWord ++ tailWord_868276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868276).length < 2 ^ (prefixWord ++ tailWord_868276).sum := by decide
  have hdescent : baseEnd_868276 < baseStart_868276 := by decide
  rcases family_descends (prefixWord ++ tailWord_868276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868286 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 2]
def baseStart_868286 : Nat := 118140960795 + 868286 * 2 ^ 59
def prefixEnd_868286 : Nat := 4983230072969 + 3 ^ 40 * 868286 * 2
def baseEnd_868286 : Nat := 396309389839906720650517

theorem tailTrace_868286 : CollatzResearch.WordTrace tailWord_868286 prefixEnd_868286 396309389839906720650517 := by
  unfold tailWord_868286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3958624016544448535978089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21112661421570392191883141 3958624016544448535978089)
  ·
    refine ⟨2968968012408336401983567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3958624016544448535978089 2968968012408336401983567)
    ·
      refine ⟨4453452018612504602975351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2968968012408336401983567 4453452018612504602975351)
      ·
        refine ⟨6680178027918756904463027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453452018612504602975351 6680178027918756904463027)
        ·
          refine ⟨10020267041878135356694541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6680178027918756904463027 10020267041878135356694541)
          ·
            refine ⟨3757600140704300758760453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10020267041878135356694541 3757600140704300758760453)
            ·
              refine ⟨704550026382056392267585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3757600140704300758760453 704550026382056392267585)
              ·
                refine ⟨528412519786542294200689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 704550026382056392267585 528412519786542294200689)
                ·
                  refine ⟨396309389839906720650517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528412519786542294200689 396309389839906720650517)
                  ·
                    rfl

theorem cell20_868286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_868286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868286 prefixEnd_868286 := by exact prefixLift 868286
  have htrace : WordTrace (prefixWord ++ tailWord_868286) baseStart_868286 baseEnd_868286 := by
    simpa [prefixWord, tailWord_868286, baseEnd_868286] using wordTrace_append hprefix tailTrace_868286
  have hstable : (prefixWord ++ tailWord_868286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868286).length < 2 ^ (prefixWord ++ tailWord_868286).sum := by decide
  have hdescent : baseEnd_868286 < baseStart_868286 := by decide
  rcases family_descends (prefixWord ++ tailWord_868286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868304 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 3]
def baseStart_868304 : Nat := 118140960795 + 868304 * 2 ^ 59
def prefixEnd_868304 : Nat := 4983230072969 + 3 ^ 40 * 868304 * 2
def baseEnd_868304 : Nat := 396317605530378658050443

theorem tailTrace_868304 : CollatzResearch.WordTrace tailWord_868304 prefixEnd_868304 396317605530378658050443 := by
  unfold tailWord_868304
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834824323145188680989983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21113099097526918241319977 15834824323145188680989983)
  ·
    refine ⟨23752236484717783021484975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15834824323145188680989983 23752236484717783021484975)
    ·
      refine ⟨35628354727076674532227463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23752236484717783021484975 35628354727076674532227463)
      ·
        refine ⟨53442532090615011798341195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35628354727076674532227463 53442532090615011798341195)
        ·
          refine ⟨80163798135922517697511793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53442532090615011798341195 80163798135922517697511793)
          ·
            refine ⟨60122848601941888273133845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80163798135922517697511793 60122848601941888273133845)
            ·
              refine ⟨2818258528216026012803149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60122848601941888273133845 2818258528216026012803149)
              ·
                refine ⟨1056846948081009754801181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2818258528216026012803149 1056846948081009754801181)
                ·
                  refine ⟨396317605530378658050443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056846948081009754801181 396317605530378658050443)
                  ·
                    rfl

theorem cell20_868304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 3].length) (baseStart_868304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868304 prefixEnd_868304 := by exact prefixLift 868304
  have htrace : WordTrace (prefixWord ++ tailWord_868304) baseStart_868304 baseEnd_868304 := by
    simpa [prefixWord, tailWord_868304, baseEnd_868304] using wordTrace_append hprefix tailTrace_868304
  have hstable : (prefixWord ++ tailWord_868304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868304).length < 2 ^ (prefixWord ++ tailWord_868304).sum := by decide
  have hdescent : baseEnd_868304 < baseStart_868304 := by decide
  rcases family_descends (prefixWord ++ tailWord_868304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868311 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 4]
def baseStart_868311 : Nat := 118140960795 + 868311 * 2 ^ 59
def prefixEnd_868311 : Nat := 4983230072969 + 3 ^ 40 * 868311 * 2
def baseEnd_868311 : Nat := 396320800521117744817081

theorem tailTrace_868311 : CollatzResearch.WordTrace tailWord_868311 prefixEnd_868311 396320800521117744817081 := by
  unfold tailWord_868311
  simp only [CollatzResearch.WordTrace]
  refine ⟨31669903957265017557484787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21113269304843345038323191 31669903957265017557484787)
  ·
    refine ⟨47504855935897526336227181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31669903957265017557484787 47504855935897526336227181)
    ·
      refine ⟨17814320975961572376085193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47504855935897526336227181 17814320975961572376085193)
      ·
        refine ⟨13360740731971179282063895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17814320975961572376085193 13360740731971179282063895)
        ·
          refine ⟨20041111097956768923095843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360740731971179282063895 20041111097956768923095843)
          ·
            refine ⟨30061666646935153384643765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20041111097956768923095843 30061666646935153384643765)
            ·
              refine ⟨2818281248150170629810353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30061666646935153384643765 2818281248150170629810353)
              ·
                refine ⟨2113710936112627972357765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2818281248150170629810353 2113710936112627972357765)
                ·
                  refine ⟨396320800521117744817081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113710936112627972357765 396320800521117744817081)
                  ·
                    rfl

theorem cell20_868311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 4].length) (baseStart_868311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868311 prefixEnd_868311 := by exact prefixLift 868311
  have htrace : WordTrace (prefixWord ++ tailWord_868311) baseStart_868311 baseEnd_868311 := by
    simpa [prefixWord, tailWord_868311, baseEnd_868311] using wordTrace_append hprefix tailTrace_868311
  have hstable : (prefixWord ++ tailWord_868311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868311).length < 2 ^ (prefixWord ++ tailWord_868311).sum := by decide
  have hdescent : baseEnd_868311 < baseStart_868311 := by decide
  rcases family_descends (prefixWord ++ tailWord_868311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868314 : List Nat := [3, 1, 1, 2, 5, 1, 3, 4]
def baseStart_868314 : Nat := 118140960795 + 868314 * 2 ^ 59
def prefixEnd_868314 : Nat := 4983230072969 + 3 ^ 40 * 868314 * 2
def baseEnd_868314 : Nat := 132107389934287689239023

theorem tailTrace_868314 : CollatzResearch.WordTrace tailWord_868314 prefixEnd_868314 132107389934287689239023 := by
  unfold tailWord_868314
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917503344063537267460999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21113342250836099379895997 7917503344063537267460999)
  ·
    refine ⟨11876255016095305901191499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917503344063537267460999 11876255016095305901191499)
    ·
      refine ⟨17814382524142958851787249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876255016095305901191499 17814382524142958851787249)
      ·
        refine ⟨13360786893107219138840437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17814382524142958851787249 13360786893107219138840437)
        ·
          refine ⟨1252573771228801794266291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13360786893107219138840437 1252573771228801794266291)
          ·
            refine ⟨1878860656843202691399437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252573771228801794266291 1878860656843202691399437)
            ·
              refine ⟨704572746316201009274789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1878860656843202691399437 704572746316201009274789)
              ·
                refine ⟨132107389934287689239023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704572746316201009274789 132107389934287689239023)
                ·
                  rfl

theorem cell20_868314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_868314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868314 prefixEnd_868314 := by exact prefixLift 868314
  have htrace : WordTrace (prefixWord ++ tailWord_868314) baseStart_868314 baseEnd_868314 := by
    simpa [prefixWord, tailWord_868314, baseEnd_868314] using wordTrace_append hprefix tailTrace_868314
  have hstable : (prefixWord ++ tailWord_868314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868314).length < 2 ^ (prefixWord ++ tailWord_868314).sum := by decide
  have hdescent : baseEnd_868314 < baseStart_868314 := by decide
  rcases family_descends (prefixWord ++ tailWord_868314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868349 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 4]
def baseStart_868349 : Nat := 118140960795 + 868349 * 2 ^ 59
def prefixEnd_868349 : Nat := 4983230072969 + 3 ^ 40 * 868349 * 2
def baseEnd_868349 : Nat := 396338144756558501550259

theorem tailTrace_868349 : CollatzResearch.WordTrace tailWord_868349 prefixEnd_868349 396338144756558501550259 := by
  unfold tailWord_868349
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671289931127350047368101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21114193287418233364912067 31671289931127350047368101)
  ·
    refine ⟨5938366862086378133881519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31671289931127350047368101 5938366862086378133881519)
    ·
      refine ⟨8907550293129567200822279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938366862086378133881519 8907550293129567200822279)
      ·
        refine ⟨13361325439694350801233419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907550293129567200822279 13361325439694350801233419)
        ·
          refine ⟨20041988159541526201850129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13361325439694350801233419 20041988159541526201850129)
          ·
            refine ⟨15031491119656144651387597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20041988159541526201850129 15031491119656144651387597)
            ·
              refine ⟨5636809169871054244270349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15031491119656144651387597 5636809169871054244270349)
              ·
                refine ⟨2113803438701645341601381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5636809169871054244270349 2113803438701645341601381)
                ·
                  refine ⟨396338144756558501550259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2113803438701645341601381 396338144756558501550259)
                  ·
                    rfl

theorem cell20_868349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_868349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868349 prefixEnd_868349 := by exact prefixLift 868349
  have htrace : WordTrace (prefixWord ++ tailWord_868349) baseStart_868349 baseEnd_868349 := by
    simpa [prefixWord, tailWord_868349, baseEnd_868349] using wordTrace_append hprefix tailTrace_868349
  have hstable : (prefixWord ++ tailWord_868349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868349).length < 2 ^ (prefixWord ++ tailWord_868349).sum := by decide
  have hdescent : baseEnd_868349 < baseStart_868349 := by decide
  rcases family_descends (prefixWord ++ tailWord_868349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868365 : List Nat := [1, 7, 1, 2, 1, 2, 2, 4]
def baseStart_868365 : Nat := 118140960795 + 868365 * 2 ^ 59
def prefixEnd_868365 : Nat := 4983230072969 + 3 ^ 40 * 868365 * 2
def baseEnd_868365 : Nat := 132115149197511185672287

theorem tailTrace_868365 : CollatzResearch.WordTrace tailWord_868365 prefixEnd_868365 132115149197511185672287 := by
  unfold tailWord_868365
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671873499069384779950549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21114582332712923186633699 31671873499069384779950549)
  ·
    refine ⟨742309535134438705780091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31671873499069384779950549 742309535134438705780091)
    ·
      refine ⟨1113464302701658058670137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742309535134438705780091 1113464302701658058670137)
      ·
        refine ⟨835098227026243544002603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1113464302701658058670137 835098227026243544002603)
        ·
          refine ⟨1252647340539365316003905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835098227026243544002603 1252647340539365316003905)
          ·
            refine ⟨939485505404523987002929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1252647340539365316003905 939485505404523987002929)
            ·
              refine ⟨704614129053392990252197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 939485505404523987002929 704614129053392990252197)
              ·
                refine ⟨132115149197511185672287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704614129053392990252197 132115149197511185672287)
                ·
                  rfl

theorem cell20_868365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 4].length) (baseStart_868365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868365 prefixEnd_868365 := by exact prefixLift 868365
  have htrace : WordTrace (prefixWord ++ tailWord_868365) baseStart_868365 baseEnd_868365 := by
    simpa [prefixWord, tailWord_868365, baseEnd_868365] using wordTrace_append hprefix tailTrace_868365
  have hstable : (prefixWord ++ tailWord_868365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868365).length < 2 ^ (prefixWord ++ tailWord_868365).sum := by decide
  have hdescent : baseEnd_868365 < baseStart_868365 := by decide
  rcases family_descends (prefixWord ++ tailWord_868365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868373 : List Nat := [1, 3, 2, 1, 5, 1, 1, 6]
def baseStart_868373 : Nat := 118140960795 + 868373 * 2 ^ 59
def prefixEnd_868373 : Nat := 4983230072969 + 3 ^ 40 * 868373 * 2
def baseEnd_868373 : Nat := 132116366336840361583387

theorem tailTrace_868373 : CollatzResearch.WordTrace tailWord_868373 prefixEnd_868373 132116366336840361583387 := by
  unfold tailWord_868373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31672165283040402146241773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21114776855360268097494515 31672165283040402146241773)
  ·
    refine ⟨11877061981140150804840665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31672165283040402146241773 11877061981140150804840665)
    ·
      refine ⟨8907796485855113103630499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11877061981140150804840665 8907796485855113103630499)
      ·
        refine ⟨13361694728782669655445749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907796485855113103630499 13361694728782669655445749)
        ·
          refine ⟨1252658880823375280198039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13361694728782669655445749 1252658880823375280198039)
          ·
            refine ⟨1878988321235062920297059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252658880823375280198039 1878988321235062920297059)
            ·
              refine ⟨2818482481852594380445589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1878988321235062920297059 2818482481852594380445589)
              ·
                refine ⟨132116366336840361583387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2818482481852594380445589 132116366336840361583387)
                ·
                  rfl

theorem cell20_868373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 6].length) (baseStart_868373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868373 prefixEnd_868373 := by exact prefixLift 868373
  have htrace : WordTrace (prefixWord ++ tailWord_868373) baseStart_868373 baseEnd_868373 := by
    simpa [prefixWord, tailWord_868373, baseEnd_868373] using wordTrace_append hprefix tailTrace_868373
  have hstable : (prefixWord ++ tailWord_868373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868373).length < 2 ^ (prefixWord ++ tailWord_868373).sum := by decide
  have hdescent : baseEnd_868373 < baseStart_868373 := by decide
  rcases family_descends (prefixWord ++ tailWord_868373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868380 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 5]
def baseStart_868380 : Nat := 118140960795 + 868380 * 2 ^ 59
def prefixEnd_868380 : Nat := 4983230072969 + 3 ^ 40 * 868380 * 2
def baseEnd_868380 : Nat := 396352294001260171516799

theorem tailTrace_868380 : CollatzResearch.WordTrace tailWord_868380 prefixEnd_868380 396352294001260171516799 := by
  unfold tailWord_868380
  simp only [CollatzResearch.WordTrace]
  refine ⟨15836210297007521170873297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21114947062676694894497729 15836210297007521170873297)
  ·
    refine ⟨11877157722755640878154973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15836210297007521170873297 11877157722755640878154973)
    ·
      refine ⟨4453934146033365329308115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11877157722755640878154973 4453934146033365329308115)
      ·
        refine ⟨6680901219050047993962173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4453934146033365329308115 6680901219050047993962173)
        ·
          refine ⟨2505337957143767997735815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6680901219050047993962173 2505337957143767997735815)
          ·
            refine ⟨3758006935715651996603723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505337957143767997735815 3758006935715651996603723)
            ·
              refine ⟨5637010403573477994905585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758006935715651996603723 5637010403573477994905585)
              ·
                refine ⟨4227757802680108496179189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5637010403573477994905585 4227757802680108496179189)
                ·
                  refine ⟨396352294001260171516799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227757802680108496179189 396352294001260171516799)
                  ·
                    rfl

theorem cell20_868380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 5].length) (baseStart_868380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868380 prefixEnd_868380 := by exact prefixLift 868380
  have htrace : WordTrace (prefixWord ++ tailWord_868380) baseStart_868380 baseEnd_868380 := by
    simpa [prefixWord, tailWord_868380, baseEnd_868380] using wordTrace_append hprefix tailTrace_868380
  have hstable : (prefixWord ++ tailWord_868380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868380).length < 2 ^ (prefixWord ++ tailWord_868380).sum := by decide
  have hdescent : baseEnd_868380 < baseStart_868380 := by decide
  rcases family_descends (prefixWord ++ tailWord_868380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868414 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_868414 : Nat := 118140960795 + 868414 * 2 ^ 59
def prefixEnd_868414 : Nat := 4983230072969 + 3 ^ 40 * 868414 * 2
def baseEnd_868414 : Nat := 396367812527707164383327

theorem tailTrace_868414 : CollatzResearch.WordTrace tailWord_868414 prefixEnd_868414 396367812527707164383327 := by
  unfold tailWord_868414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3959207584486483268560537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21115773783927910765656197 3959207584486483268560537)
  ·
    refine ⟨2969405688364862451420403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3959207584486483268560537 2969405688364862451420403)
    ·
      refine ⟨4454108532547293677130605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2969405688364862451420403 4454108532547293677130605)
      ·
        refine ⟨1670290699705235128923977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4454108532547293677130605 1670290699705235128923977)
        ·
          refine ⟨1252718024778926346692983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1670290699705235128923977 1252718024778926346692983)
          ·
            refine ⟨1879077037168389520039475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1252718024778926346692983 1879077037168389520039475)
            ·
              refine ⟨2818615555752584280059213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1879077037168389520039475 2818615555752584280059213)
              ·
                refine ⟨1056980833407219105022205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2818615555752584280059213 1056980833407219105022205)
                ·
                  refine ⟨396367812527707164383327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1056980833407219105022205 396367812527707164383327)
                  ·
                    rfl

theorem cell20_868414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_868414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868414 prefixEnd_868414 := by exact prefixLift 868414
  have htrace : WordTrace (prefixWord ++ tailWord_868414) baseStart_868414 baseEnd_868414 := by
    simpa [prefixWord, tailWord_868414, baseEnd_868414] using wordTrace_append hprefix tailTrace_868414
  have hstable : (prefixWord ++ tailWord_868414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868414).length < 2 ^ (prefixWord ++ tailWord_868414).sum := by decide
  have hdescent : baseEnd_868414 < baseStart_868414 := by decide
  rcases family_descends (prefixWord ++ tailWord_868414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868439 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 7]
def baseStart_868439 : Nat := 118140960795 + 868439 * 2 ^ 59
def prefixEnd_868439 : Nat := 4983230072969 + 3 ^ 40 * 868439 * 2
def baseEnd_868439 : Nat := 396379223208918188549891

theorem tailTrace_868439 : CollatzResearch.WordTrace tailWord_868439 prefixEnd_868439 396379223208918188549891 := by
  unfold tailWord_868439
  simp only [CollatzResearch.WordTrace]
  refine ⟨31674572500801295418144371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21116381667200863612096247 31674572500801295418144371)
  ·
    refine ⟨47511858751201943127216557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31674572500801295418144371 47511858751201943127216557)
    ·
      refine ⟨17816947031700728672706209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47511858751201943127216557 17816947031700728672706209)
      ·
        refine ⟨13362710273775546504529657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17816947031700728672706209 13362710273775546504529657)
        ·
          refine ⟨10022032705331659878397243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13362710273775546504529657 10022032705331659878397243)
          ·
            refine ⟨15033049057997489817595865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10022032705331659878397243 15033049057997489817595865)
            ·
              refine ⟨11274786793498117363196899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15033049057997489817595865 11274786793498117363196899)
              ·
                refine ⟨16912180190247176044795349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11274786793498117363196899 16912180190247176044795349)
                ·
                  refine ⟨396379223208918188549891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16912180190247176044795349 396379223208918188549891)
                  ·
                    rfl

theorem cell20_868439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_868439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868439 prefixEnd_868439 := by exact prefixLift 868439
  have htrace : WordTrace (prefixWord ++ tailWord_868439) baseStart_868439 baseEnd_868439 := by
    simpa [prefixWord, tailWord_868439, baseEnd_868439] using wordTrace_append hprefix tailTrace_868439
  have hstable : (prefixWord ++ tailWord_868439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868439).length < 2 ^ (prefixWord ++ tailWord_868439).sum := by decide
  have hdescent : baseEnd_868439 < baseStart_868439 := by decide
  rcases family_descends (prefixWord ++ tailWord_868439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868442 : List Nat := [3, 1, 1, 2, 1, 1, 4, 5, 2]
def baseStart_868442 : Nat := 118140960795 + 868442 * 2 ^ 59
def prefixEnd_868442 : Nat := 4983230072969 + 3 ^ 40 * 868442 * 2
def baseEnd_868442 : Nat := 396380592490663511449879

theorem tailTrace_868442 : CollatzResearch.WordTrace tailWord_868442 prefixEnd_868442 396380592490663511449879 := by
  unfold tailWord_868442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7918670479947606732625895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21116454613193617953669053 7918670479947606732625895)
  ·
    refine ⟨11878005719921410098938843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7918670479947606732625895 11878005719921410098938843)
    ·
      refine ⟨17817008579882115148408265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11878005719921410098938843 17817008579882115148408265)
      ·
        refine ⟨13362756434911586361306199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17817008579882115148408265 13362756434911586361306199)
        ·
          refine ⟨20044134652367379541959299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13362756434911586361306199 20044134652367379541959299)
          ·
            refine ⟨30066201978551069312938949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20044134652367379541959299 30066201978551069312938949)
            ·
              refine ⟨5637412870978325496176053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30066201978551069312938949 5637412870978325496176053)
              ·
                refine ⟨528507456654218015266505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5637412870978325496176053 528507456654218015266505)
                ·
                  refine ⟨396380592490663511449879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528507456654218015266505 396380592490663511449879)
                  ·
                    rfl

theorem cell20_868442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_868442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868442 prefixEnd_868442 := by exact prefixLift 868442
  have htrace : WordTrace (prefixWord ++ tailWord_868442) baseStart_868442 baseEnd_868442 := by
    simpa [prefixWord, tailWord_868442, baseEnd_868442] using wordTrace_append hprefix tailTrace_868442
  have hstable : (prefixWord ++ tailWord_868442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868442).length < 2 ^ (prefixWord ++ tailWord_868442).sum := by decide
  have hdescent : baseEnd_868442 < baseStart_868442 := by decide
  rcases family_descends (prefixWord ++ tailWord_868442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868508 : List Nat := [2, 2, 3, 2, 1, 1, 9]
def baseStart_868508 : Nat := 118140960795 + 868508 * 2 ^ 59
def prefixEnd_868508 : Nat := 4983230072969 + 3 ^ 40 * 868508 * 2
def baseEnd_868508 : Nat := 44045635187673401694401

theorem tailTrace_868508 : CollatzResearch.WordTrace tailWord_868508 prefixEnd_868508 44045635187673401694401 := by
  unfold tailWord_868508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15838544568775660101203089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21118059425034213468270785 15838544568775660101203089)
  ·
    refine ⟨11878908426581745075902317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15838544568775660101203089 11878908426581745075902317)
    ·
      refine ⟨4454590659968154403463369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11878908426581745075902317 4454590659968154403463369)
      ·
        refine ⟨3340942994976115802597527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4454590659968154403463369 3340942994976115802597527)
        ·
          refine ⟨5011414492464173703896291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340942994976115802597527 5011414492464173703896291)
          ·
            refine ⟨7517121738696260555844437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011414492464173703896291 7517121738696260555844437)
            ·
              refine ⟨44045635187673401694401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7517121738696260555844437 44045635187673401694401)
              ·
                rfl

theorem cell20_868508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 9].length) (baseStart_868508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868508 prefixEnd_868508 := by exact prefixLift 868508
  have htrace : WordTrace (prefixWord ++ tailWord_868508) baseStart_868508 baseEnd_868508 := by
    simpa [prefixWord, tailWord_868508, baseEnd_868508] using wordTrace_append hprefix tailTrace_868508
  have hstable : (prefixWord ++ tailWord_868508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868508).length < 2 ^ (prefixWord ++ tailWord_868508).sum := by decide
  have hdescent : baseEnd_868508 < baseStart_868508 := by decide
  rcases family_descends (prefixWord ++ tailWord_868508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868511 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 3]
def baseStart_868511 : Nat := 118140960795 + 868511 * 2 ^ 59
def prefixEnd_868511 : Nat := 4983230072969 + 3 ^ 40 * 868511 * 2
def baseEnd_868511 : Nat := 396412085970805938149597

theorem tailTrace_868511 : CollatzResearch.WordTrace tailWord_868511 prefixEnd_868511 396412085970805938149597 := by
  unfold tailWord_868511
  simp only [CollatzResearch.WordTrace]
  refine ⟨31677198556540451714765387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21118132371026967809843591 31677198556540451714765387)
  ·
    refine ⟨47515797834810677572148081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31677198556540451714765387 47515797834810677572148081)
    ·
      refine ⟨35636848376108008179111061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47515797834810677572148081 35636848376108008179111061)
      ·
        refine ⟨1670477267630062883395831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35636848376108008179111061 1670477267630062883395831)
        ·
          refine ⟨2505715901445094325093747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670477267630062883395831 2505715901445094325093747)
          ·
            refine ⟨3758573852167641487640621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2505715901445094325093747 3758573852167641487640621)
            ·
              refine ⟨1409465194562865557865233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3758573852167641487640621 1409465194562865557865233)
              ·
                refine ⟨1057098895922149168398925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1409465194562865557865233 1057098895922149168398925)
                ·
                  refine ⟨396412085970805938149597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057098895922149168398925 396412085970805938149597)
                  ·
                    rfl

theorem cell20_868511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 3].length) (baseStart_868511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868511 prefixEnd_868511 := by exact prefixLift 868511
  have htrace : WordTrace (prefixWord ++ tailWord_868511) baseStart_868511 baseEnd_868511 := by
    simpa [prefixWord, tailWord_868511, baseEnd_868511] using wordTrace_append hprefix tailTrace_868511
  have hstable : (prefixWord ++ tailWord_868511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868511).length < 2 ^ (prefixWord ++ tailWord_868511).sum := by decide
  have hdescent : baseEnd_868511 < baseStart_868511 := by decide
  rcases family_descends (prefixWord ++ tailWord_868511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868573 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 4]
def baseStart_868573 : Nat := 118140960795 + 868573 * 2 ^ 59
def prefixEnd_868573 : Nat := 4983230072969 + 3 ^ 40 * 868573 * 2
def baseEnd_868573 : Nat := 396440384460209278082677

theorem tailTrace_868573 : CollatzResearch.WordTrace tailWord_868573 prefixEnd_868573 396440384460209278082677 := by
  unfold tailWord_868573
  simp only [CollatzResearch.WordTrace]
  refine ⟨31679459882315836303522373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21119639921543890869014915 31679459882315836303522373)
  ·
    refine ⟨5939898727934219306910445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31679459882315836303522373 5939898727934219306910445)
    ·
      refine ⟨2227462022975332240091417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5939898727934219306910445 2227462022975332240091417)
      ·
        refine ⟨1670596517231499180068563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2227462022975332240091417 1670596517231499180068563)
        ·
          refine ⟨2505894775847248770102845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1670596517231499180068563 2505894775847248770102845)
          ·
            refine ⟨939710540942718288788567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2505894775847248770102845 939710540942718288788567)
            ·
              refine ⟨1409565811414077433182851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939710540942718288788567 1409565811414077433182851)
              ·
                refine ⟨2114348717121116149774277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1409565811414077433182851 2114348717121116149774277)
                ·
                  refine ⟨396440384460209278082677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114348717121116149774277 396440384460209278082677)
                  ·
                    rfl

theorem cell20_868573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_868573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868573 prefixEnd_868573 := by exact prefixLift 868573
  have htrace : WordTrace (prefixWord ++ tailWord_868573) baseStart_868573 baseEnd_868573 := by
    simpa [prefixWord, tailWord_868573, baseEnd_868573] using wordTrace_append hprefix tailTrace_868573
  have hstable : (prefixWord ++ tailWord_868573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868573).length < 2 ^ (prefixWord ++ tailWord_868573).sum := by decide
  have hdescent : baseEnd_868573 < baseStart_868573 := by decide
  rcases family_descends (prefixWord ++ tailWord_868573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868584 : List Nat := [2, 1, 4, 1, 2, 2, 1, 7]
def baseStart_868584 : Nat := 118140960795 + 868584 * 2 ^ 59
def prefixEnd_868584 : Nat := 4983230072969 + 3 ^ 40 * 868584 * 2
def baseEnd_868584 : Nat := 132148468386647376238655

theorem tailTrace_868584 : CollatzResearch.WordTrace tailWord_868584 prefixEnd_868584 132148468386647376238655 := by
  unfold tailWord_868584
  simp only [CollatzResearch.WordTrace]
  refine ⟨15839930542637992591086403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21119907390183990121448537 15839930542637992591086403)
  ·
    refine ⟨23759895813956988886629605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15839930542637992591086403 23759895813956988886629605)
    ·
      refine ⟨4454980465116935416243051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23759895813956988886629605 4454980465116935416243051)
      ·
        refine ⟨6682470697675403124364577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4454980465116935416243051 6682470697675403124364577)
        ·
          refine ⟨5011853023256552343273433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6682470697675403124364577 5011853023256552343273433)
          ·
            refine ⟨3758889767442414257455075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5011853023256552343273433 3758889767442414257455075)
            ·
              refine ⟨5638334651163621386182613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3758889767442414257455075 5638334651163621386182613)
              ·
                refine ⟨132148468386647376238655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5638334651163621386182613 132148468386647376238655)
                ·
                  rfl

theorem cell20_868584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_868584 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868584 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868584 prefixEnd_868584 := by exact prefixLift 868584
  have htrace : WordTrace (prefixWord ++ tailWord_868584) baseStart_868584 baseEnd_868584 := by
    simpa [prefixWord, tailWord_868584, baseEnd_868584] using wordTrace_append hprefix tailTrace_868584
  have hstable : (prefixWord ++ tailWord_868584).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868584).length < 2 ^ (prefixWord ++ tailWord_868584).sum := by decide
  have hdescent : baseEnd_868584 < baseStart_868584 := by decide
  rcases family_descends (prefixWord ++ tailWord_868584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868629 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 5]
def baseStart_868629 : Nat := 118140960795 + 868629 * 2 ^ 59
def prefixEnd_868629 : Nat := 4983230072969 + 3 ^ 40 * 868629 * 2
def baseEnd_868629 : Nat := 396465944386121972215781

theorem tailTrace_868629 : CollatzResearch.WordTrace tailWord_868629 prefixEnd_868629 396465944386121972215781 := by
  unfold tailWord_868629
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681502370112957867560941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21121001580075305245040627 31681502370112957867560941)
  ·
    refine ⟨11880563388792359200335353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31681502370112957867560941 11880563388792359200335353)
    ·
      refine ⟨8910422541594269400251515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11880563388792359200335353 8910422541594269400251515)
      ·
        refine ⟨13365633812391404100377273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8910422541594269400251515 13365633812391404100377273)
        ·
          refine ⟨10024225359293553075282955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13365633812391404100377273 10024225359293553075282955)
          ·
            refine ⟨15036338038940329612924433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024225359293553075282955 15036338038940329612924433)
            ·
              refine ⟨11277253529205247209693325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15036338038940329612924433 11277253529205247209693325)
              ·
                refine ⟨4228970073451967703634997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11277253529205247209693325 4228970073451967703634997)
                ·
                  refine ⟨396465944386121972215781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4228970073451967703634997 396465944386121972215781)
                  ·
                    rfl

theorem cell20_868629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_868629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868629 prefixEnd_868629 := by exact prefixLift 868629
  have htrace : WordTrace (prefixWord ++ tailWord_868629) baseStart_868629 baseEnd_868629 := by
    simpa [prefixWord, tailWord_868629, baseEnd_868629] using wordTrace_append hprefix tailTrace_868629
  have hstable : (prefixWord ++ tailWord_868629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868629).length < 2 ^ (prefixWord ++ tailWord_868629).sum := by decide
  have hdescent : baseEnd_868629 < baseStart_868629 := by decide
  rcases family_descends (prefixWord ++ tailWord_868629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868632 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 2]
def baseStart_868632 : Nat := 118140960795 + 868632 * 2 ^ 59
def prefixEnd_868632 : Nat := 4983230072969 + 3 ^ 40 * 868632 * 2
def baseEnd_868632 : Nat := 396467313667867295115769

theorem tailTrace_868632 : CollatzResearch.WordTrace tailWord_868632 prefixEnd_868632 396467313667867295115769 := by
  unfold tailWord_868632
  simp only [CollatzResearch.WordTrace]
  refine ⟨15840805894551044689960075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21121074526068059586613433 15840805894551044689960075)
  ·
    refine ⟨23761208841826567034940113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15840805894551044689960075 23761208841826567034940113)
    ·
      refine ⟨17820906631369925276205085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23761208841826567034940113 17820906631369925276205085)
      ·
        refine ⟨6682839986763721978576907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17820906631369925276205085 6682839986763721978576907)
        ·
          refine ⟨10024259980145582967865361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682839986763721978576907 10024259980145582967865361)
          ·
            refine ⟨7518194985109187225899021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10024259980145582967865361 7518194985109187225899021)
            ·
              refine ⟨2819323119415945209712133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7518194985109187225899021 2819323119415945209712133)
              ·
                refine ⟨528623084890489726821025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2819323119415945209712133 528623084890489726821025)
                ·
                  refine ⟨396467313667867295115769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528623084890489726821025 396467313667867295115769)
                  ·
                    rfl

theorem cell20_868632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 2].length) (baseStart_868632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868632 prefixEnd_868632 := by exact prefixLift 868632
  have htrace : WordTrace (prefixWord ++ tailWord_868632) baseStart_868632 baseEnd_868632 := by
    simpa [prefixWord, tailWord_868632, baseEnd_868632] using wordTrace_append hprefix tailTrace_868632
  have hstable : (prefixWord ++ tailWord_868632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868632).length < 2 ^ (prefixWord ++ tailWord_868632).sum := by decide
  have hdescent : baseEnd_868632 < baseStart_868632 := by decide
  rcases family_descends (prefixWord ++ tailWord_868632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868639 : List Nat := [1, 1, 2, 4, 3, 3, 1, 5]
def baseStart_868639 : Nat := 118140960795 + 868639 * 2 ^ 59
def prefixEnd_868639 : Nat := 4983230072969 + 3 ^ 40 * 868639 * 2
def baseEnd_868639 : Nat := 132156836219535460627469

theorem tailTrace_868639 : CollatzResearch.WordTrace tailWord_868639 prefixEnd_868639 132156836219535460627469 := by
  unfold tailWord_868639
  simp only [CollatzResearch.WordTrace]
  refine ⟨31681867100076729575424971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21121244733384486383616647 31681867100076729575424971)
  ·
    refine ⟨47522800650115094363137457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31681867100076729575424971 47522800650115094363137457)
    ·
      refine ⟨35642100487586320772353093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47522800650115094363137457 35642100487586320772353093)
      ·
        refine ⟨6682893841422435144816205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35642100487586320772353093 6682893841422435144816205)
        ·
          refine ⟨2506085190533413179306077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6682893841422435144816205 2506085190533413179306077)
          ·
            refine ⟨939781946450029942239779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2506085190533413179306077 939781946450029942239779)
            ·
              refine ⟨1409672919675044913359669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 939781946450029942239779 1409672919675044913359669)
              ·
                refine ⟨132156836219535460627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1409672919675044913359669 132156836219535460627469)
                ·
                  rfl

theorem cell20_868639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 5].length) (baseStart_868639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868639 prefixEnd_868639 := by exact prefixLift 868639
  have htrace : WordTrace (prefixWord ++ tailWord_868639) baseStart_868639 baseEnd_868639 := by
    simpa [prefixWord, tailWord_868639, baseEnd_868639] using wordTrace_append hprefix tailTrace_868639
  have hstable : (prefixWord ++ tailWord_868639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868639).length < 2 ^ (prefixWord ++ tailWord_868639).sum := by decide
  have hdescent : baseEnd_868639 < baseStart_868639 := by decide
  rcases family_descends (prefixWord ++ tailWord_868639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868725 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 2]
def baseStart_868725 : Nat := 118140960795 + 868725 * 2 ^ 59
def prefixEnd_868725 : Nat := 4983230072969 + 3 ^ 40 * 868725 * 2
def baseEnd_868725 : Nat := 396509761401972305015389

theorem tailTrace_868725 : CollatzResearch.WordTrace tailWord_868725 prefixEnd_868725 396509761401972305015389 := by
  unfold tailWord_868725
  simp only [CollatzResearch.WordTrace]
  refine ⟨31685003777765166263055629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21123335851843444175370419 31685003777765166263055629)
  ·
    refine ⟨11881876416661937348645861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31685003777765166263055629 11881876416661937348645861)
    ·
      refine ⟨2227851828124113252871099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11881876416661937348645861 2227851828124113252871099)
      ·
        refine ⟨3341777742186169879306649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227851828124113252871099 3341777742186169879306649)
        ·
          refine ⟨2506333306639627409479987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341777742186169879306649 2506333306639627409479987)
          ·
            refine ⟨3759499959959441114219981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506333306639627409479987 3759499959959441114219981)
            ·
              refine ⟨1409812484984790417832493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3759499959959441114219981 1409812484984790417832493)
              ·
                refine ⟨528679681869296406687185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1409812484984790417832493 528679681869296406687185)
                ·
                  refine ⟨396509761401972305015389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528679681869296406687185 396509761401972305015389)
                  ·
                    rfl

theorem cell20_868725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_868725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868725 prefixEnd_868725 := by exact prefixLift 868725
  have htrace : WordTrace (prefixWord ++ tailWord_868725) baseStart_868725 baseEnd_868725 := by
    simpa [prefixWord, tailWord_868725, baseEnd_868725] using wordTrace_append hprefix tailTrace_868725
  have hstable : (prefixWord ++ tailWord_868725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868725).length < 2 ^ (prefixWord ++ tailWord_868725).sum := by decide
  have hdescent : baseEnd_868725 < baseStart_868725 := by decide
  rcases family_descends (prefixWord ++ tailWord_868725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868743 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 5]
def baseStart_868743 : Nat := 118140960795 + 868743 * 2 ^ 59
def prefixEnd_868743 : Nat := 4983230072969 + 3 ^ 40 * 868743 * 2
def baseEnd_868743 : Nat := 396517977092444242415315

theorem tailTrace_868743 : CollatzResearch.WordTrace tailWord_868743 prefixEnd_868743 396517977092444242415315 := by
  unfold tailWord_868743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31685660291699955337210883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21123773527799970224807255 31685660291699955337210883)
  ·
    refine ⟨47528490437549933005816325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31685660291699955337210883 47528490437549933005816325)
    ·
      refine ⟨8911591957040612438590561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47528490437549933005816325 8911591957040612438590561)
      ·
        refine ⟨6683693967780459328942921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8911591957040612438590561 6683693967780459328942921)
        ·
          refine ⟨5012770475835344496707191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6683693967780459328942921 5012770475835344496707191)
          ·
            refine ⟨7519155713753016745060787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012770475835344496707191 7519155713753016745060787)
            ·
              refine ⟨11278733570629525117591181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519155713753016745060787 11278733570629525117591181)
              ·
                refine ⟨4229525088986071919096693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11278733570629525117591181 4229525088986071919096693)
                ·
                  refine ⟨396517977092444242415315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4229525088986071919096693 396517977092444242415315)
                  ·
                    rfl

theorem cell20_868743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 5].length) (baseStart_868743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868743 prefixEnd_868743 := by exact prefixLift 868743
  have htrace : WordTrace (prefixWord ++ tailWord_868743) baseStart_868743 baseEnd_868743 := by
    simpa [prefixWord, tailWord_868743, baseEnd_868743] using wordTrace_append hprefix tailTrace_868743
  have hstable : (prefixWord ++ tailWord_868743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868743).length < 2 ^ (prefixWord ++ tailWord_868743).sum := by decide
  have hdescent : baseEnd_868743 < baseStart_868743 := by decide
  rcases family_descends (prefixWord ++ tailWord_868743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868798 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_868798 : Nat := 118140960795 + 868798 * 2 ^ 59
def prefixEnd_868798 : Nat := 4983230072969 + 3 ^ 40 * 868798 * 2
def baseEnd_868798 : Nat := 396543080591108495581757

theorem tailTrace_868798 : CollatzResearch.WordTrace tailWord_868798 prefixEnd_868798 396543080591108495581757 := by
  unfold tailWord_868798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3960958288312587466307881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21125110871000466486975365 3960958288312587466307881)
  ·
    refine ⟨2970718716234440599730911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3960958288312587466307881 2970718716234440599730911)
    ·
      refine ⟨4456078074351660899596367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970718716234440599730911 4456078074351660899596367)
      ·
        refine ⟨6684117111527491349394551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4456078074351660899596367 6684117111527491349394551)
        ·
          refine ⟨10026175667291237024091827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6684117111527491349394551 10026175667291237024091827)
          ·
            refine ⟨15039263500936855536137741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10026175667291237024091827 15039263500936855536137741)
            ·
              refine ⟨5639723812851320826051653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15039263500936855536137741 5639723812851320826051653)
              ·
                refine ⟨1057448214909622654884685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5639723812851320826051653 1057448214909622654884685)
                ·
                  refine ⟨396543080591108495581757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057448214909622654884685 396543080591108495581757)
                  ·
                    rfl

theorem cell20_868798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_868798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868798 prefixEnd_868798 := by exact prefixLift 868798
  have htrace : WordTrace (prefixWord ++ tailWord_868798) baseStart_868798 baseEnd_868798 := by
    simpa [prefixWord, tailWord_868798, baseEnd_868798] using wordTrace_append hprefix tailTrace_868798
  have hstable : (prefixWord ++ tailWord_868798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868798).length < 2 ^ (prefixWord ++ tailWord_868798).sum := by decide
  have hdescent : baseEnd_868798 < baseStart_868798 := by decide
  rcases family_descends (prefixWord ++ tailWord_868798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868822 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 4]
def baseStart_868822 : Nat := 118140960795 + 868822 * 2 ^ 59
def prefixEnd_868822 : Nat := 4983230072969 + 3 ^ 40 * 868822 * 2
def baseEnd_868822 : Nat := 396554034845071078781659

theorem tailTrace_868822 : CollatzResearch.WordTrace tailWord_868822 prefixEnd_868822 396554034845071078781659 := by
  unfold tailWord_868822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980533853650859489333545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21125694438942501219557813 1980533853650859489333545)
  ·
    refine ⟨1485400390238144617000159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1980533853650859489333545 1485400390238144617000159)
    ·
      refine ⟨2228100585357216925500239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1485400390238144617000159 2228100585357216925500239)
      ·
        refine ⟨3342150878035825388250359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228100585357216925500239 3342150878035825388250359)
        ·
          refine ⟨5013226317053738082375539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342150878035825388250359 5013226317053738082375539)
          ·
            refine ⟨7519839475580607123563309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013226317053738082375539 7519839475580607123563309)
            ·
              refine ⟨2819939803342727671336241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7519839475580607123563309 2819939803342727671336241)
              ·
                refine ⟨2114954852507045753502181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2819939803342727671336241 2114954852507045753502181)
                ·
                  refine ⟨396554034845071078781659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2114954852507045753502181 396554034845071078781659)
                  ·
                    rfl

theorem cell20_868822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_868822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868822 prefixEnd_868822 := by exact prefixLift 868822
  have htrace : WordTrace (prefixWord ++ tailWord_868822) baseStart_868822 baseEnd_868822 := by
    simpa [prefixWord, tailWord_868822, baseEnd_868822] using wordTrace_append hprefix tailTrace_868822
  have hstable : (prefixWord ++ tailWord_868822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868822).length < 2 ^ (prefixWord ++ tailWord_868822).sum := by decide
  have hdescent : baseEnd_868822 < baseStart_868822 := by decide
  rcases family_descends (prefixWord ++ tailWord_868822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868829 : List Nat := [1, 4, 3, 1, 1, 1, 5, 4]
def baseStart_868829 : Nat := 118140960795 + 868829 * 2 ^ 59
def prefixEnd_868829 : Nat := 4983230072969 + 3 ^ 40 * 868829 * 2
def baseEnd_868829 : Nat := 132185743278603388516099

theorem tailTrace_868829 : CollatzResearch.WordTrace tailWord_868829 prefixEnd_868829 132185743278603388516099 := by
  unfold tailWord_868829
  simp only [CollatzResearch.WordTrace]
  refine ⟨31688796969388392024841541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21125864646258928016561027 31688796969388392024841541)
  ·
    refine ⟨5941649431760323504657789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31688796969388392024841541 5941649431760323504657789)
    ·
      refine ⟨2228118536910121314246671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5941649431760323504657789 2228118536910121314246671)
      ·
        refine ⟨3342177805365181971370007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228118536910121314246671 3342177805365181971370007)
        ·
          refine ⟨5013266708047772957055011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342177805365181971370007 5013266708047772957055011)
          ·
            refine ⟨7519900062071659435582517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5013266708047772957055011 7519900062071659435582517)
            ·
              refine ⟨704990630819218072085861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7519900062071659435582517 704990630819218072085861)
              ·
                refine ⟨132185743278603388516099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 704990630819218072085861 132185743278603388516099)
                ·
                  rfl

theorem cell20_868829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 4].length) (baseStart_868829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868829 prefixEnd_868829 := by exact prefixLift 868829
  have htrace : WordTrace (prefixWord ++ tailWord_868829) baseStart_868829 baseEnd_868829 := by
    simpa [prefixWord, tailWord_868829, baseEnd_868829] using wordTrace_append hprefix tailTrace_868829
  have hstable : (prefixWord ++ tailWord_868829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868829).length < 2 ^ (prefixWord ++ tailWord_868829).sum := by decide
  have hdescent : baseEnd_868829 < baseStart_868829 := by decide
  rcases family_descends (prefixWord ++ tailWord_868829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868853 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 5]
def baseStart_868853 : Nat := 118140960795 + 868853 * 2 ^ 59
def prefixEnd_868853 : Nat := 4983230072969 + 3 ^ 40 * 868853 * 2
def baseEnd_868853 : Nat := 396568184089772748748199

theorem tailTrace_868853 : CollatzResearch.WordTrace tailWord_868853 prefixEnd_868853 396568184089772748748199 := by
  unfold tailWord_868853
  simp only [CollatzResearch.WordTrace]
  refine ⟨31689672321301444123715213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21126448214200962749143475 31689672321301444123715213)
  ·
    refine ⟨11883627120488041546393205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31689672321301444123715213 11883627120488041546393205)
    ·
      refine ⟨1114090042545753894974363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11883627120488041546393205 1114090042545753894974363)
      ·
        refine ⟨1671135063818630842461545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114090042545753894974363 1671135063818630842461545)
        ·
          refine ⟨1253351297863973131846159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671135063818630842461545 1253351297863973131846159)
          ·
            refine ⟨1880026946795959697769239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253351297863973131846159 1880026946795959697769239)
            ·
              refine ⟨2820040420193939546653859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880026946795959697769239 2820040420193939546653859)
              ·
                refine ⟨4230060630290909319980789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2820040420193939546653859 4230060630290909319980789)
                ·
                  refine ⟨396568184089772748748199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4230060630290909319980789 396568184089772748748199)
                  ·
                    rfl

theorem cell20_868853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_868853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868853 prefixEnd_868853 := by exact prefixLift 868853
  have htrace : WordTrace (prefixWord ++ tailWord_868853) baseStart_868853 baseEnd_868853 := by
    simpa [prefixWord, tailWord_868853, baseEnd_868853] using wordTrace_append hprefix tailTrace_868853
  have hstable : (prefixWord ++ tailWord_868853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868853).length < 2 ^ (prefixWord ++ tailWord_868853).sum := by decide
  have hdescent : baseEnd_868853 < baseStart_868853 := by decide
  rcases family_descends (prefixWord ++ tailWord_868853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868877 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 4]
def baseStart_868877 : Nat := 118140960795 + 868877 * 2 ^ 59
def prefixEnd_868877 : Nat := 4983230072969 + 3 ^ 40 * 868877 * 2
def baseEnd_868877 : Nat := 396579138343735331948101

theorem tailTrace_868877 : CollatzResearch.WordTrace tailWord_868877 prefixEnd_868877 396579138343735331948101 := by
  unfold tailWord_868877
  simp only [CollatzResearch.WordTrace]
  refine ⟨31690547673214496222588885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21127031782142997481725923 31690547673214496222588885)
  ·
    refine ⟨742747211090964755216927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31690547673214496222588885 742747211090964755216927)
    ·
      refine ⟨1114120816636447132825391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742747211090964755216927 1114120816636447132825391)
      ·
        refine ⟨1671181224954670699238087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114120816636447132825391 1671181224954670699238087)
        ·
          refine ⟨2506771837432006048857131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671181224954670699238087 2506771837432006048857131)
          ·
            refine ⟨3760157756148009073285697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506771837432006048857131 3760157756148009073285697)
            ·
              refine ⟨2820118317111006804964273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3760157756148009073285697 2820118317111006804964273)
              ·
                refine ⟨2115088737833255103723205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2820118317111006804964273 2115088737833255103723205)
                ·
                  refine ⟨396579138343735331948101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2115088737833255103723205 396579138343735331948101)
                  ·
                    rfl

theorem cell20_868877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_868877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868877 prefixEnd_868877 := by exact prefixLift 868877
  have htrace : WordTrace (prefixWord ++ tailWord_868877) baseStart_868877 baseEnd_868877 := by
    simpa [prefixWord, tailWord_868877, baseEnd_868877] using wordTrace_append hprefix tailTrace_868877
  have hstable : (prefixWord ++ tailWord_868877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868877).length < 2 ^ (prefixWord ++ tailWord_868877).sum := by decide
  have hdescent : baseEnd_868877 < baseStart_868877 := by decide
  rcases family_descends (prefixWord ++ tailWord_868877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868884 : List Nat := [2, 4, 3, 1, 1, 1, 4, 4]
def baseStart_868884 : Nat := 118140960795 + 868884 * 2 ^ 59
def prefixEnd_868884 : Nat := 4983230072969 + 3 ^ 40 * 868884 * 2
def baseEnd_868884 : Nat := 132194111111491472904913

theorem tailTrace_868884 : CollatzResearch.WordTrace tailWord_868884 prefixEnd_868884 132194111111491472904913 := by
  unfold tailWord_868884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845401492094568209046853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21127201989459424278729137 15845401492094568209046853)
  ·
    refine ⟨2971012779767731539196285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15845401492094568209046853 2971012779767731539196285)
    ·
      refine ⟨1114129792412899327198607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2971012779767731539196285 1114129792412899327198607)
      ·
        refine ⟨1671194688619348990797911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114129792412899327198607 1671194688619348990797911)
        ·
          refine ⟨2506792032929023486196867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671194688619348990797911 2506792032929023486196867)
          ·
            refine ⟨3760188049393535229295301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2506792032929023486196867 3760188049393535229295301)
            ·
              refine ⟨705035259261287855492869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3760188049393535229295301 705035259261287855492869)
              ·
                refine ⟨132194111111491472904913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705035259261287855492869 132194111111491472904913)
                ·
                  rfl

theorem cell20_868884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 4].length) (baseStart_868884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868884 prefixEnd_868884 := by exact prefixLift 868884
  have htrace : WordTrace (prefixWord ++ tailWord_868884) baseStart_868884 baseEnd_868884 := by
    simpa [prefixWord, tailWord_868884, baseEnd_868884] using wordTrace_append hprefix tailTrace_868884
  have hstable : (prefixWord ++ tailWord_868884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868884).length < 2 ^ (prefixWord ++ tailWord_868884).sum := by decide
  have hdescent : baseEnd_868884 < baseStart_868884 := by decide
  rcases family_descends (prefixWord ++ tailWord_868884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868888 : List Nat := [2, 1, 2, 3, 3, 2, 1, 6]
def baseStart_868888 : Nat := 118140960795 + 868888 * 2 ^ 59
def prefixEnd_868888 : Nat := 4983230072969 + 3 ^ 40 * 868888 * 2
def baseEnd_868888 : Nat := 132194719681156060860463

theorem tailTrace_868888 : CollatzResearch.WordTrace tailWord_868888 prefixEnd_868888 132194719681156060860463 := by
  unfold tailWord_868888
  simp only [CollatzResearch.WordTrace]
  refine ⟨15845474438087322550619659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21127299250783096734159545 15845474438087322550619659)
  ·
    refine ⟨23768211657130983825929489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15845474438087322550619659 23768211657130983825929489)
    ·
      refine ⟨17826158742848237869447117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23768211657130983825929489 17826158742848237869447117)
      ·
        refine ⟨6684809528568089201042669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17826158742848237869447117 6684809528568089201042669)
        ·
          refine ⟨2506803573213033450391001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6684809528568089201042669 2506803573213033450391001)
          ·
            refine ⟨1880102679909775087793251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2506803573213033450391001 1880102679909775087793251)
            ·
              refine ⟨2820154019864662631689877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880102679909775087793251 2820154019864662631689877)
              ·
                refine ⟨132194719681156060860463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2820154019864662631689877 132194719681156060860463)
                ·
                  rfl

theorem cell20_868888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 6].length) (baseStart_868888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868888 prefixEnd_868888 := by exact prefixLift 868888
  have htrace : WordTrace (prefixWord ++ tailWord_868888) baseStart_868888 baseEnd_868888 := by
    simpa [prefixWord, tailWord_868888, baseEnd_868888] using wordTrace_append hprefix tailTrace_868888
  have hstable : (prefixWord ++ tailWord_868888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868888).length < 2 ^ (prefixWord ++ tailWord_868888).sum := by decide
  have hdescent : baseEnd_868888 < baseStart_868888 := by decide
  rcases family_descends (prefixWord ++ tailWord_868888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868929 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 3]
def baseStart_868929 : Nat := 118140960795 + 868929 * 2 ^ 59
def prefixEnd_868929 : Nat := 4983230072969 + 3 ^ 40 * 868929 * 2
def baseEnd_868929 : Nat := 396602872560654262214555

theorem tailTrace_868929 : CollatzResearch.WordTrace tailWord_868929 prefixEnd_868929 396602872560654262214555 := by
  unfold tailWord_868929
  simp only [CollatzResearch.WordTrace]
  refine ⟨31692444269026109103481841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21128296179350739402321227 31692444269026109103481841)
  ·
    refine ⟨23769333201769581827611381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31692444269026109103481841 23769333201769581827611381)
    ·
      refine ⟨2228374987665898296338567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23769333201769581827611381 2228374987665898296338567)
      ·
        refine ⟨3342562481498847444507851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228374987665898296338567 3342562481498847444507851)
        ·
          refine ⟨5013843722248271166761777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342562481498847444507851 5013843722248271166761777)
          ·
            refine ⟨3760382791686203375071333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5013843722248271166761777 3760382791686203375071333)
            ·
              refine ⟨705071773441163132825875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3760382791686203375071333 705071773441163132825875)
              ·
                refine ⟨1057607660161744699238813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705071773441163132825875 1057607660161744699238813)
                ·
                  refine ⟨396602872560654262214555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057607660161744699238813 396602872560654262214555)
                  ·
                    rfl

theorem cell20_868929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_868929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868929 prefixEnd_868929 := by exact prefixLift 868929
  have htrace : WordTrace (prefixWord ++ tailWord_868929) baseStart_868929 baseEnd_868929 := by
    simpa [prefixWord, tailWord_868929, baseEnd_868929] using wordTrace_append hprefix tailTrace_868929
  have hstable : (prefixWord ++ tailWord_868929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868929).length < 2 ^ (prefixWord ++ tailWord_868929).sum := by decide
  have hdescent : baseEnd_868929 < baseStart_868929 := by decide
  rcases family_descends (prefixWord ++ tailWord_868929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868940 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_868940 : Nat := 118140960795 + 868940 * 2 ^ 59
def prefixEnd_868940 : Nat := 4983230072969 + 3 ^ 40 * 868940 * 2
def baseEnd_868940 : Nat := 396607893260387112847843

theorem tailTrace_868940 : CollatzResearch.WordTrace tailWord_868940 prefixEnd_868940 396607893260387112847843 := by
  unfold tailWord_868940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15846422735993128991066137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21128563647990838654754849 15846422735993128991066137)
  ·
    refine ⟨11884817051994846743299603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15846422735993128991066137 11884817051994846743299603)
    ·
      refine ⟨17827225577992270114949405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11884817051994846743299603 17827225577992270114949405)
      ·
        refine ⟨6685209591747101293106027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17827225577992270114949405 6685209591747101293106027)
        ·
          refine ⟨10027814387620651939659041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6685209591747101293106027 10027814387620651939659041)
          ·
            refine ⟨7520860790715488954744281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10027814387620651939659041 7520860790715488954744281)
            ·
              refine ⟨5640645593036616716058211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7520860790715488954744281 5640645593036616716058211)
              ·
                refine ⟨8460968389554925074087317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5640645593036616716058211 8460968389554925074087317)
                ·
                  refine ⟨396607893260387112847843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8460968389554925074087317 396607893260387112847843)
                  ·
                    rfl

theorem cell20_868940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_868940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868940 prefixEnd_868940 := by exact prefixLift 868940
  have htrace : WordTrace (prefixWord ++ tailWord_868940) baseStart_868940 baseEnd_868940 := by
    simpa [prefixWord, tailWord_868940, baseEnd_868940] using wordTrace_append hprefix tailTrace_868940
  have hstable : (prefixWord ++ tailWord_868940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868940).length < 2 ^ (prefixWord ++ tailWord_868940).sum := by decide
  have hdescent : baseEnd_868940 < baseStart_868940 := by decide
  rcases family_descends (prefixWord ++ tailWord_868940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_868994 : List Nat := [3, 4, 3, 1, 1, 1, 3, 4]
def baseStart_868994 : Nat := 118140960795 + 868994 * 2 ^ 59
def prefixEnd_868994 : Nat := 4983230072969 + 3 ^ 40 * 868994 * 2
def baseEnd_868994 : Nat := 132210846777267641682541

theorem tailTrace_868994 : CollatzResearch.WordTrace tailWord_868994 prefixEnd_868994 132210846777267641682541 := by
  unfold tailWord_868994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7923703753447656301149509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21129876675860416803065357 7923703753447656301149509)
  ·
    refine ⟨1485694453771435556465533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7923703753447656301149509 1485694453771435556465533)
    ·
      refine ⟨557135420164288333674575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1485694453771435556465533 557135420164288333674575)
      ·
        refine ⟨835703130246432500511863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557135420164288333674575 835703130246432500511863)
        ·
          refine ⟨1253554695369648750767795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835703130246432500511863 1253554695369648750767795)
          ·
            refine ⟨1880332043054473126151693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253554695369648750767795 1880332043054473126151693)
            ·
              refine ⟨705124516145427422306885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880332043054473126151693 705124516145427422306885)
              ·
                refine ⟨132210846777267641682541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705124516145427422306885 132210846777267641682541)
                ·
                  rfl

theorem cell20_868994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_868994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_868994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_868994 prefixEnd_868994 := by exact prefixLift 868994
  have htrace : WordTrace (prefixWord ++ tailWord_868994) baseStart_868994 baseEnd_868994 := by
    simpa [prefixWord, tailWord_868994, baseEnd_868994] using wordTrace_append hprefix tailTrace_868994
  have hstable : (prefixWord ++ tailWord_868994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_868994).length < 2 ^ (prefixWord ++ tailWord_868994).sum := by decide
  have hdescent : baseEnd_868994 < baseStart_868994 := by decide
  rcases family_descends (prefixWord ++ tailWord_868994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869016 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 6]
def baseStart_869016 : Nat := 118140960795 + 869016 * 2 ^ 59
def prefixEnd_869016 : Nat := 4983230072969 + 3 ^ 40 * 869016 * 2
def baseEnd_869016 : Nat := 396642581731268626314199

theorem tailTrace_869016 : CollatzResearch.WordTrace tailWord_869016 prefixEnd_869016 396642581731268626314199 := by
  unfold tailWord_869016
  simp only [CollatzResearch.WordTrace]
  refine ⟨15847808709855461480949451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21130411613140615307932601 15847808709855461480949451)
  ·
    refine ⟨23771713064783192221424177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15847808709855461480949451 23771713064783192221424177)
    ·
      refine ⟨17828784798587394166068133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23771713064783192221424177 17828784798587394166068133)
      ·
        refine ⟨3342897149735136406137775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17828784798587394166068133 3342897149735136406137775)
        ·
          refine ⟨5014345724602704609206663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342897149735136406137775 5014345724602704609206663)
          ·
            refine ⟨7521518586904056913809995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5014345724602704609206663 7521518586904056913809995)
            ·
              refine ⟨11282277880356085370714993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7521518586904056913809995 11282277880356085370714993)
              ·
                refine ⟨8461708410267064028036245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11282277880356085370714993 8461708410267064028036245)
                ·
                  refine ⟨396642581731268626314199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8461708410267064028036245 396642581731268626314199)
                  ·
                    rfl

theorem cell20_869016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 6].length) (baseStart_869016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869016 prefixEnd_869016 := by exact prefixLift 869016
  have htrace : WordTrace (prefixWord ++ tailWord_869016) baseStart_869016 baseEnd_869016 := by
    simpa [prefixWord, tailWord_869016, baseEnd_869016] using wordTrace_append hprefix tailTrace_869016
  have hstable : (prefixWord ++ tailWord_869016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869016).length < 2 ^ (prefixWord ++ tailWord_869016).sum := by decide
  have hdescent : baseEnd_869016 < baseStart_869016 := by decide
  rcases family_descends (prefixWord ++ tailWord_869016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869084 : List Nat := [2, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_869084 : Nat := 118140960795 + 869084 * 2 ^ 59
def prefixEnd_869084 : Nat := 4983230072969 + 3 ^ 40 * 869084 * 2
def baseEnd_869084 : Nat := 396673618784162612047255

theorem tailTrace_869084 : CollatzResearch.WordTrace tailWord_869084 prefixEnd_869084 396673618784162612047255 := by
  unfold tailWord_869084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15849048791732285287687153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21132065055643047050249537 15849048791732285287687153)
  ·
    refine ⟨11886786593799213965765365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15849048791732285287687153 11886786593799213965765365)
    ·
      refine ⟨1114386243168676309290503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11886786593799213965765365 1114386243168676309290503)
      ·
        refine ⟨1671579364753014463935755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1114386243168676309290503 1671579364753014463935755)
        ·
          refine ⟨2507369047129521695903633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671579364753014463935755 2507369047129521695903633)
          ·
            refine ⟨1880526785347141271927725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507369047129521695903633 1880526785347141271927725)
            ·
              refine ⟨705197544505177976972897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1880526785347141271927725 705197544505177976972897)
              ·
                refine ⟨528898158378883482729673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705197544505177976972897 528898158378883482729673)
                ·
                  refine ⟨396673618784162612047255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528898158378883482729673 396673618784162612047255)
                  ·
                    rfl

theorem cell20_869084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_869084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869084 prefixEnd_869084 := by exact prefixLift 869084
  have htrace : WordTrace (prefixWord ++ tailWord_869084) baseStart_869084 baseEnd_869084 := by
    simpa [prefixWord, tailWord_869084, baseEnd_869084] using wordTrace_append hprefix tailTrace_869084
  have hstable : (prefixWord ++ tailWord_869084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869084).length < 2 ^ (prefixWord ++ tailWord_869084).sum := by decide
  have hdescent : baseEnd_869084 < baseStart_869084 := by decide
  rcases family_descends (prefixWord ++ tailWord_869084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869102 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_869102 : Nat := 118140960795 + 869102 * 2 ^ 59
def prefixEnd_869102 : Nat := 4983230072969 + 3 ^ 40 * 869102 * 2
def baseEnd_869102 : Nat := 396681834474634549447181

theorem tailTrace_869102 : CollatzResearch.WordTrace tailWord_869102 prefixEnd_869102 396681834474634549447181 := by
  unfold tailWord_869102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3962344262174919956191195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21132502731599573099686373 3962344262174919956191195)
  ·
    refine ⟨5943516393262379934286793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3962344262174919956191195 5943516393262379934286793)
    ·
      refine ⟨4457637294946784950715095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5943516393262379934286793 4457637294946784950715095)
      ·
        refine ⟨6686455942420177426072643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457637294946784950715095 6686455942420177426072643)
        ·
          refine ⟨10029683913630266139108965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6686455942420177426072643 10029683913630266139108965)
          ·
            refine ⟨1880565733805674901082931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10029683913630266139108965 1880565733805674901082931)
            ·
              refine ⟨2820848600708512351624397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880565733805674901082931 2820848600708512351624397)
              ·
                refine ⟨1057818225265692131859149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2820848600708512351624397 1057818225265692131859149)
                ·
                  refine ⟨396681834474634549447181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057818225265692131859149 396681834474634549447181)
                  ·
                    rfl

theorem cell20_869102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_869102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869102 prefixEnd_869102 := by exact prefixLift 869102
  have htrace : WordTrace (prefixWord ++ tailWord_869102) baseStart_869102 baseEnd_869102 := by
    simpa [prefixWord, tailWord_869102, baseEnd_869102] using wordTrace_append hprefix tailTrace_869102
  have hstable : (prefixWord ++ tailWord_869102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869102).length < 2 ^ (prefixWord ++ tailWord_869102).sum := by decide
  have hdescent : baseEnd_869102 < baseStart_869102 := by decide
  rcases family_descends (prefixWord ++ tailWord_869102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869133 : List Nat := [1, 7, 2, 10]
def baseStart_869133 : Nat := 118140960795 + 869133 * 2 ^ 59
def prefixEnd_869133 : Nat := 4983230072969 + 3 ^ 40 * 869133 * 2
def baseEnd_869133 : Nat := 1632493760161877446147

theorem tailTrace_869133 : CollatzResearch.WordTrace tailWord_869133 prefixEnd_869133 1632493760161877446147 := by
  unfold tailWord_869133
  simp only [CollatzResearch.WordTrace]
  refine ⟨31699884760287051943908053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21133256506858034629272035 31699884760287051943908053)
  ·
    refine ⟨742966049069227779935345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 31699884760287051943908053 742966049069227779935345)
    ·
      refine ⟨557224536801920834951509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 742966049069227779935345 557224536801920834951509)
      ·
        refine ⟨1632493760161877446147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 557224536801920834951509 1632493760161877446147)
        ·
          rfl

theorem cell20_869133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 10].length) (baseStart_869133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869133 prefixEnd_869133 := by exact prefixLift 869133
  have htrace : WordTrace (prefixWord ++ tailWord_869133) baseStart_869133 baseEnd_869133 := by
    simpa [prefixWord, tailWord_869133, baseEnd_869133] using wordTrace_append hprefix tailTrace_869133
  have hstable : (prefixWord ++ tailWord_869133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869133).length < 2 ^ (prefixWord ++ tailWord_869133).sum := by decide
  have hdescent : baseEnd_869133 < baseStart_869133 := by decide
  rcases family_descends (prefixWord ++ tailWord_869133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869154 : List Nat := [3, 3, 1, 1, 2, 2, 3, 5]
def baseStart_869154 : Nat := 118140960795 + 869154 * 2 ^ 59
def prefixEnd_869154 : Nat := 4983230072969 + 3 ^ 40 * 869154 * 2
def baseEnd_869154 : Nat := 132235189563851159904545

theorem tailTrace_869154 : CollatzResearch.WordTrace tailWord_869154 prefixEnd_869154 132235189563851159904545 := by
  unfold tailWord_869154
  simp only [CollatzResearch.WordTrace]
  refine ⟨7925162673302743132605629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21133767128807315020281677 7925162673302743132605629)
  ·
    refine ⟨2971936002488528674727111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7925162673302743132605629 2971936002488528674727111)
    ·
      refine ⟨4457904003732793012090667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2971936002488528674727111 4457904003732793012090667)
      ·
        refine ⟨6686856005599189518136001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4457904003732793012090667 6686856005599189518136001)
        ·
          refine ⟨5015142004199392138602001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6686856005599189518136001 5015142004199392138602001)
          ·
            refine ⟨3761356503149544103951501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5015142004199392138602001 3761356503149544103951501)
            ·
              refine ⟨1410508688681079038981813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3761356503149544103951501 1410508688681079038981813)
              ·
                refine ⟨132235189563851159904545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410508688681079038981813 132235189563851159904545)
                ·
                  rfl

theorem cell20_869154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_869154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869154 prefixEnd_869154 := by exact prefixLift 869154
  have htrace : WordTrace (prefixWord ++ tailWord_869154) baseStart_869154 baseEnd_869154 := by
    simpa [prefixWord, tailWord_869154, baseEnd_869154] using wordTrace_append hprefix tailTrace_869154
  have hstable : (prefixWord ++ tailWord_869154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869154).length < 2 ^ (prefixWord ++ tailWord_869154).sum := by decide
  have hdescent : baseEnd_869154 < baseStart_869154 := by decide
  rcases family_descends (prefixWord ++ tailWord_869154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869181 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 2]
def baseStart_869181 : Nat := 118140960795 + 869181 * 2 ^ 59
def prefixEnd_869181 : Nat := 4983230072969 + 3 ^ 40 * 869181 * 2
def baseEnd_869181 : Nat := 396717892227261385813525

theorem tailTrace_869181 : CollatzResearch.WordTrace tailWord_869181 prefixEnd_869181 396717892227261385813525 := by
  unfold tailWord_869181
  simp only [CollatzResearch.WordTrace]
  refine ⟨31701635464113156141655397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21134423642742104094436931 31701635464113156141655397)
  ·
    refine ⟨5944056649521216776560387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31701635464113156141655397 5944056649521216776560387)
    ·
      refine ⟨8916084974281825164840581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5944056649521216776560387 8916084974281825164840581)
      ·
        refine ⟨1671765932677842218407609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8916084974281825164840581 1671765932677842218407609)
        ·
          refine ⟨1253824449508381663805707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1671765932677842218407609 1253824449508381663805707)
          ·
            refine ⟨1880736674262572495708561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1253824449508381663805707 1880736674262572495708561)
            ·
              refine ⟨1410552505696929371781421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1880736674262572495708561 1410552505696929371781421)
              ·
                refine ⟨528957189636348514418033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410552505696929371781421 528957189636348514418033)
                ·
                  refine ⟨396717892227261385813525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 528957189636348514418033 396717892227261385813525)
                  ·
                    rfl

theorem cell20_869181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_869181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869181 prefixEnd_869181 := by exact prefixLift 869181
  have htrace : WordTrace (prefixWord ++ tailWord_869181) baseStart_869181 baseEnd_869181 := by
    simpa [prefixWord, tailWord_869181, baseEnd_869181] using wordTrace_append hprefix tailTrace_869181
  have hstable : (prefixWord ++ tailWord_869181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869181).length < 2 ^ (prefixWord ++ tailWord_869181).sum := by decide
  have hdescent : baseEnd_869181 < baseStart_869181 := by decide
  rcases family_descends (prefixWord ++ tailWord_869181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869216 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 3]
def baseStart_869216 : Nat := 118140960795 + 869216 * 2 ^ 59
def prefixEnd_869216 : Nat := 4983230072969 + 3 ^ 40 * 869216 * 2
def baseEnd_869216 : Nat := 396733867180956819646715

theorem tailTrace_869216 : CollatzResearch.WordTrace tailWord_869216 prefixEnd_869216 396733867180956819646715 := by
  unfold tailWord_869216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15851456009493178559589751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21135274679324238079453001 15851456009493178559589751)
  ·
    refine ⟨23777184014239767839384627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15851456009493178559589751 23777184014239767839384627)
    ·
      refine ⟨35665776021359651759076941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23777184014239767839384627 35665776021359651759076941)
      ·
        refine ⟨13374666008009869409653853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35665776021359651759076941 13374666008009869409653853)
        ·
          refine ⟨5015499753003701028620195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13374666008009869409653853 5015499753003701028620195)
          ·
            refine ⟨7523249629505551542930293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015499753003701028620195 7523249629505551542930293)
            ·
              refine ⟨705304652766145457149715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7523249629505551542930293 705304652766145457149715)
              ·
                refine ⟨1057956979149218185724573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705304652766145457149715 1057956979149218185724573)
                ·
                  refine ⟨396733867180956819646715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1057956979149218185724573 396733867180956819646715)
                  ·
                    rfl

theorem cell20_869216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 3].length) (baseStart_869216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869216 prefixEnd_869216 := by exact prefixLift 869216
  have htrace : WordTrace (prefixWord ++ tailWord_869216) baseStart_869216 baseEnd_869216 := by
    simpa [prefixWord, tailWord_869216, baseEnd_869216] using wordTrace_append hprefix tailTrace_869216
  have hstable : (prefixWord ++ tailWord_869216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869216).length < 2 ^ (prefixWord ++ tailWord_869216).sum := by decide
  have hdescent : baseEnd_869216 < baseStart_869216 := by decide
  rcases family_descends (prefixWord ++ tailWord_869216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869237 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_869237 : Nat := 118140960795 + 869237 * 2 ^ 59
def prefixEnd_869237 : Nat := 4983230072969 + 3 ^ 40 * 869237 * 2
def baseEnd_869237 : Nat := 396743452153174079946629

theorem tailTrace_869237 : CollatzResearch.WordTrace tailWord_869237 prefixEnd_869237 396743452153174079946629 := by
  unfold tailWord_869237
  simp only [CollatzResearch.WordTrace]
  refine ⟨31703677951910277705693965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21135785301273518470462643 31703677951910277705693965)
  ·
    refine ⟨11888879231966354139635237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31703677951910277705693965 11888879231966354139635237)
    ·
      refine ⟨2229164855993691401181607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11888879231966354139635237 2229164855993691401181607)
      ·
        refine ⟨3343747283990537101772411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229164855993691401181607 3343747283990537101772411)
        ·
          refine ⟨5015620925985805652658617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343747283990537101772411 5015620925985805652658617)
          ·
            refine ⟨3761715694489354239493963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5015620925985805652658617 3761715694489354239493963)
            ·
              refine ⟨5642573541734031359240945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3761715694489354239493963 5642573541734031359240945)
              ·
                refine ⟨4231930156300523519430709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5642573541734031359240945 4231930156300523519430709)
                ·
                  refine ⟨396743452153174079946629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4231930156300523519430709 396743452153174079946629)
                  ·
                    rfl

theorem cell20_869237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_869237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869237 prefixEnd_869237 := by exact prefixLift 869237
  have htrace : WordTrace (prefixWord ++ tailWord_869237) baseStart_869237 baseEnd_869237 := by
    simpa [prefixWord, tailWord_869237, baseEnd_869237] using wordTrace_append hprefix tailTrace_869237
  have hstable : (prefixWord ++ tailWord_869237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869237).length < 2 ^ (prefixWord ++ tailWord_869237).sum := by decide
  have hdescent : baseEnd_869237 < baseStart_869237 := by decide
  rcases family_descends (prefixWord ++ tailWord_869237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869268 : List Nat := [2, 4, 2, 1, 1, 1, 4, 5]
def baseStart_869268 : Nat := 118140960795 + 869268 * 2 ^ 59
def prefixEnd_869268 : Nat := 4983230072969 + 3 ^ 40 * 869268 * 2
def baseEnd_869268 : Nat := 132252533799291916637723

theorem tailTrace_869268 : CollatzResearch.WordTrace tailWord_869268 prefixEnd_869268 132252533799291916637723 := by
  unfold tailWord_869268
  simp only [CollatzResearch.WordTrace]
  refine ⟨15852404307398985000036229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21136539076531980000048305 15852404307398985000036229)
  ·
    refine ⟨2972325807637309687506793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15852404307398985000036229 2972325807637309687506793)
    ·
      refine ⟨2229244355727982265630095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972325807637309687506793 2229244355727982265630095)
      ·
        refine ⟨3343866533591973398445143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229244355727982265630095 3343866533591973398445143)
        ·
          refine ⟨5015799800387960097667715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3343866533591973398445143 5015799800387960097667715)
          ·
            refine ⟨7523699700581940146501573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5015799800387960097667715 7523699700581940146501573)
            ·
              refine ⟨1410693693859113777469045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7523699700581940146501573 1410693693859113777469045)
              ·
                refine ⟨132252533799291916637723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410693693859113777469045 132252533799291916637723)
                ·
                  rfl

theorem cell20_869268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_869268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869268 prefixEnd_869268 := by exact prefixLift 869268
  have htrace : WordTrace (prefixWord ++ tailWord_869268) baseStart_869268 baseEnd_869268 := by
    simpa [prefixWord, tailWord_869268, baseEnd_869268] using wordTrace_append hprefix tailTrace_869268
  have hstable : (prefixWord ++ tailWord_869268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869268).length < 2 ^ (prefixWord ++ tailWord_869268).sum := by decide
  have hdescent : baseEnd_869268 < baseStart_869268 := by decide
  rcases family_descends (prefixWord ++ tailWord_869268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869302 : List Nat := [5, 1, 4, 1, 1, 8]
def baseStart_869302 : Nat := 118140960795 + 869302 * 2 ^ 59
def prefixEnd_869302 : Nat := 4983230072969 + 3 ^ 40 * 869302 * 2
def baseEnd_869302 : Nat := 14695300737937879362211

theorem tailTrace_869302 : CollatzResearch.WordTrace tailWord_869302 prefixEnd_869302 14695300737937879362211 := by
  unfold tailWord_869302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981628043542174612925635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21137365797783195871206773 1981628043542174612925635)
  ·
    refine ⟨2972442065313261919388453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981628043542174612925635 2972442065313261919388453)
    ·
      refine ⟨557332887246236609885335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2972442065313261919388453 557332887246236609885335)
      ·
        refine ⟨835999330869354914828003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557332887246236609885335 835999330869354914828003)
        ·
          refine ⟨1253998996304032372242005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 835999330869354914828003 1253998996304032372242005)
          ·
            refine ⟨14695300737937879362211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1253998996304032372242005 14695300737937879362211)
            ·
              rfl

theorem cell20_869302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 8].length) (baseStart_869302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869302 prefixEnd_869302 := by exact prefixLift 869302
  have htrace : WordTrace (prefixWord ++ tailWord_869302) baseStart_869302 baseEnd_869302 := by
    simpa [prefixWord, tailWord_869302, baseEnd_869302] using wordTrace_append hprefix tailTrace_869302
  have hstable : (prefixWord ++ tailWord_869302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869302).length < 2 ^ (prefixWord ++ tailWord_869302).sum := by decide
  have hdescent : baseEnd_869302 < baseStart_869302 := by decide
  rcases family_descends (prefixWord ++ tailWord_869302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869327 : List Nat := [1, 1, 2, 1, 1, 6, 3, 5]
def baseStart_869327 : Nat := 118140960795 + 869327 * 2 ^ 59
def prefixEnd_869327 : Nat := 4983230072969 + 3 ^ 40 * 869327 * 2
def baseEnd_869327 : Nat := 132261510201844588982087

theorem tailTrace_869327 : CollatzResearch.WordTrace tailWord_869327 prefixEnd_869327 132261510201844588982087 := by
  unfold tailWord_869327
  simp only [CollatzResearch.WordTrace]
  refine ⟨31706960521584223076470235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21137973681056148717646823 31706960521584223076470235)
  ·
    refine ⟨47560440782376334614705353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31706960521584223076470235 47560440782376334614705353)
    ·
      refine ⟨35670330586782250961029015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47560440782376334614705353 35670330586782250961029015)
      ·
        refine ⟨53505495880173376441543523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35670330586782250961029015 53505495880173376441543523)
        ·
          refine ⟨80258243820260064662315285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53505495880173376441543523 80258243820260064662315285)
          ·
            refine ⟨3762105179074690531046029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 80258243820260064662315285 3762105179074690531046029)
            ·
              refine ⟨1410789442153008949142261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3762105179074690531046029 1410789442153008949142261)
              ·
                refine ⟨132261510201844588982087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1410789442153008949142261 132261510201844588982087)
                ·
                  rfl

theorem cell20_869327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_869327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869327 prefixEnd_869327 := by exact prefixLift 869327
  have htrace : WordTrace (prefixWord ++ tailWord_869327) baseStart_869327 baseEnd_869327 := by
    simpa [prefixWord, tailWord_869327, baseEnd_869327] using wordTrace_append hprefix tailTrace_869327
  have hstable : (prefixWord ++ tailWord_869327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869327).length < 2 ^ (prefixWord ++ tailWord_869327).sum := by decide
  have hdescent : baseEnd_869327 < baseStart_869327 := by decide
  rcases family_descends (prefixWord ++ tailWord_869327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869330 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 3]
def baseStart_869330 : Nat := 118140960795 + 869330 * 2 ^ 59
def prefixEnd_869330 : Nat := 4983230072969 + 3 ^ 40 * 869330 * 2
def baseEnd_869330 : Nat := 396785899887279089846249

theorem tailTrace_869330 : CollatzResearch.WordTrace tailWord_869330 prefixEnd_869330 396785899887279089846249 := by
  unfold tailWord_869330
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926767485143338647207361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21138046627048903059219629 7926767485143338647207361)
  ·
    refine ⟨5945075613857503985405521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7926767485143338647207361 5945075613857503985405521)
    ·
      refine ⟨4458806710393127989054141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5945075613857503985405521 4458806710393127989054141)
      ·
        refine ⟨1672052516397422995895303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4458806710393127989054141 1672052516397422995895303)
        ·
          refine ⟨2508078774596134493842955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672052516397422995895303 2508078774596134493842955)
          ·
            refine ⟨3762118161894201740764433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508078774596134493842955 3762118161894201740764433)
            ·
              refine ⟨2821588621420651305573325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3762118161894201740764433 2821588621420651305573325)
              ·
                refine ⟨1058095733032744239589997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2821588621420651305573325 1058095733032744239589997)
                ·
                  refine ⟨396785899887279089846249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058095733032744239589997 396785899887279089846249)
                  ·
                    rfl

theorem cell20_869330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_869330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869330 prefixEnd_869330 := by exact prefixLift 869330
  have htrace : WordTrace (prefixWord ++ tailWord_869330) baseStart_869330 baseEnd_869330 := by
    simpa [prefixWord, tailWord_869330, baseEnd_869330] using wordTrace_append hprefix tailTrace_869330
  have hstable : (prefixWord ++ tailWord_869330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869330).length < 2 ^ (prefixWord ++ tailWord_869330).sum := by decide
  have hdescent : baseEnd_869330 < baseStart_869330 := by decide
  rcases family_descends (prefixWord ++ tailWord_869330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869354 : List Nat := [3, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_869354 : Nat := 118140960795 + 869354 * 2 ^ 59
def prefixEnd_869354 : Nat := 4983230072969 + 3 ^ 40 * 869354 * 2
def baseEnd_869354 : Nat := 396796854141241673046151

theorem tailTrace_869354 : CollatzResearch.WordTrace tailWord_869354 prefixEnd_869354 396796854141241673046151 := by
  unfold tailWord_869354
  simp only [CollatzResearch.WordTrace]
  refine ⟨7926986323121601671925779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21138630194990937791802077 7926986323121601671925779)
  ·
    refine ⟨11890479484682402507888669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7926986323121601671925779 11890479484682402507888669)
    ·
      refine ⟨4458929806755900940458251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11890479484682402507888669 4458929806755900940458251)
      ·
        refine ⟨6688394710133851410687377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4458929806755900940458251 6688394710133851410687377)
        ·
          refine ⟨5016296032600388558015533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6688394710133851410687377 5016296032600388558015533)
          ·
            refine ⟨1881111012225145709255825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5016296032600388558015533 1881111012225145709255825)
            ·
              refine ⟨1410833259168859281941869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881111012225145709255825 1410833259168859281941869)
              ·
                refine ⟨529062472188322230728201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1410833259168859281941869 529062472188322230728201)
                ·
                  refine ⟨396796854141241673046151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529062472188322230728201 396796854141241673046151)
                  ·
                    rfl

theorem cell20_869354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_869354 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869354 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869354 prefixEnd_869354 := by exact prefixLift 869354
  have htrace : WordTrace (prefixWord ++ tailWord_869354) baseStart_869354 baseEnd_869354 := by
    simpa [prefixWord, tailWord_869354, baseEnd_869354] using wordTrace_append hprefix tailTrace_869354
  have hstable : (prefixWord ++ tailWord_869354).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869354).length < 2 ^ (prefixWord ++ tailWord_869354).sum := by decide
  have hdescent : baseEnd_869354 < baseStart_869354 := by decide
  rcases family_descends (prefixWord ++ tailWord_869354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869399 : List Nat := [1, 1, 3, 5, 1, 3, 2, 4]
def baseStart_869399 : Nat := 118140960795 + 869399 * 2 ^ 59
def prefixEnd_869399 : Nat := 4983230072969 + 3 ^ 40 * 869399 * 2
def baseEnd_869399 : Nat := 132272464455807172181989

theorem tailTrace_869399 : CollatzResearch.WordTrace tailWord_869399 prefixEnd_869399 132272464455807172181989 := by
  unfold tailWord_869399
  simp only [CollatzResearch.WordTrace]
  refine ⟨31709586577323379373091251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21139724384882252915394167 31709586577323379373091251)
  ·
    refine ⟨47564379865985069059636877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31709586577323379373091251 47564379865985069059636877)
    ·
      refine ⟨17836642449744400897363829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47564379865985069059636877 17836642449744400897363829)
      ·
        refine ⟨1672185229663537584127859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17836642449744400897363829 1672185229663537584127859)
        ·
          refine ⟨2508277844495306376191789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672185229663537584127859 2508277844495306376191789)
          ·
            refine ⟨940604191685739891071921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2508277844495306376191789 940604191685739891071921)
            ·
              refine ⟨705453143764304918303941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940604191685739891071921 705453143764304918303941)
              ·
                refine ⟨132272464455807172181989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705453143764304918303941 132272464455807172181989)
                ·
                  rfl

theorem cell20_869399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_869399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869399 prefixEnd_869399 := by exact prefixLift 869399
  have htrace : WordTrace (prefixWord ++ tailWord_869399) baseStart_869399 baseEnd_869399 := by
    simpa [prefixWord, tailWord_869399, baseEnd_869399] using wordTrace_append hprefix tailTrace_869399
  have hstable : (prefixWord ++ tailWord_869399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869399).length < 2 ^ (prefixWord ++ tailWord_869399).sum := by decide
  have hdescent : baseEnd_869399 < baseStart_869399 := by decide
  rcases family_descends (prefixWord ++ tailWord_869399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869430 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_869430 : Nat := 118140960795 + 869430 * 2 ^ 59
def prefixEnd_869430 : Nat := 4983230072969 + 3 ^ 40 * 869430 * 2
def baseEnd_869430 : Nat := 396831542612123186512507

theorem tailTrace_869430 : CollatzResearch.WordTrace tailWord_869430 prefixEnd_869430 396831542612123186512507 := by
  unfold tailWord_869430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1981919827513191979216859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 21140478160140714444979829 1981919827513191979216859)
  ·
    refine ⟨2972879741269787968825289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1981919827513191979216859 2972879741269787968825289)
    ·
      refine ⟨2229659805952340976618967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2972879741269787968825289 2229659805952340976618967)
      ·
        refine ⟨3344489708928511464928451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229659805952340976618967 3344489708928511464928451)
        ·
          refine ⟨5016734563392767197392677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3344489708928511464928451 5016734563392767197392677)
          ·
            refine ⟨940637730636143849511127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5016734563392767197392677 940637730636143849511127)
            ·
              refine ⟨1410956595954215774266691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940637730636143849511127 1410956595954215774266691)
              ·
                refine ⟨2116434893931323661400037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410956595954215774266691 2116434893931323661400037)
                ·
                  refine ⟨396831542612123186512507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116434893931323661400037 396831542612123186512507)
                  ·
                    rfl

theorem cell20_869430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_869430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869430 prefixEnd_869430 := by exact prefixLift 869430
  have htrace : WordTrace (prefixWord ++ tailWord_869430) baseStart_869430 baseEnd_869430 := by
    simpa [prefixWord, tailWord_869430, baseEnd_869430] using wordTrace_append hprefix tailTrace_869430
  have hstable : (prefixWord ++ tailWord_869430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869430).length < 2 ^ (prefixWord ++ tailWord_869430).sum := by decide
  have hdescent : baseEnd_869430 < baseStart_869430 := by decide
  rcases family_descends (prefixWord ++ tailWord_869430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869434 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 4]
def baseStart_869434 : Nat := 118140960795 + 869434 * 2 ^ 59
def prefixEnd_869434 : Nat := 4983230072969 + 3 ^ 40 * 869434 * 2
def baseEnd_869434 : Nat := 396833368321116950379157

theorem tailTrace_869434 : CollatzResearch.WordTrace tailWord_869434 prefixEnd_869434 396833368321116950379157 := by
  unfold tailWord_869434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7927715783049145087653839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21140575421464386900410237 7927715783049145087653839)
  ·
    refine ⟨11891573674573717631480759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7927715783049145087653839 11891573674573717631480759)
    ·
      refine ⟨17837360511860576447221139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11891573674573717631480759 17837360511860576447221139)
      ·
        refine ⟨26756040767790864670831709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17837360511860576447221139 26756040767790864670831709)
        ·
          refine ⟨10033515287921574251561891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26756040767790864670831709 10033515287921574251561891)
          ·
            refine ⟨15050272931882361377342837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10033515287921574251561891 15050272931882361377342837)
            ·
              refine ⟨1410963087363971379125891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15050272931882361377342837 1410963087363971379125891)
              ·
                refine ⟨2116444631045957068688837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1410963087363971379125891 2116444631045957068688837)
                ·
                  refine ⟨396833368321116950379157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2116444631045957068688837 396833368321116950379157)
                  ·
                    rfl

theorem cell20_869434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_869434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869434 prefixEnd_869434 := by exact prefixLift 869434
  have htrace : WordTrace (prefixWord ++ tailWord_869434) baseStart_869434 baseEnd_869434 := by
    simpa [prefixWord, tailWord_869434, baseEnd_869434] using wordTrace_append hprefix tailTrace_869434
  have hstable : (prefixWord ++ tailWord_869434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869434).length < 2 ^ (prefixWord ++ tailWord_869434).sum := by decide
  have hdescent : baseEnd_869434 < baseStart_869434 := by decide
  rcases family_descends (prefixWord ++ tailWord_869434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869482 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 3]
def baseStart_869482 : Nat := 118140960795 + 869482 * 2 ^ 59
def prefixEnd_869482 : Nat := 4983230072969 + 3 ^ 40 * 869482 * 2
def baseEnd_869482 : Nat := 396855276829042116778961

theorem tailTrace_869482 : CollatzResearch.WordTrace tailWord_869482 prefixEnd_869482 396855276829042116778961 := by
  unfold tailWord_869482
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928153459005671137090675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21141742557348456365575133 7928153459005671137090675)
  ·
    refine ⟨11892230188508506705636013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7928153459005671137090675 11892230188508506705636013)
    ·
      refine ⟨4459586320690690014613505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11892230188508506705636013 4459586320690690014613505)
      ·
        refine ⟨3344689740518017510960129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4459586320690690014613505 3344689740518017510960129)
        ·
          refine ⟨2508517305388513133220097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344689740518017510960129 2508517305388513133220097)
          ·
            refine ⟨1881387979041384849915073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508517305388513133220097 1881387979041384849915073)
            ·
              refine ⟨1411040984281038637436305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881387979041384849915073 1411040984281038637436305)
              ·
                refine ⟨1058280738210778978077229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411040984281038637436305 1058280738210778978077229)
                ·
                  refine ⟨396855276829042116778961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058280738210778978077229 396855276829042116778961)
                  ·
                    rfl

theorem cell20_869482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_869482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869482 prefixEnd_869482 := by exact prefixLift 869482
  have htrace : WordTrace (prefixWord ++ tailWord_869482) baseStart_869482 baseEnd_869482 := by
    simpa [prefixWord, tailWord_869482, baseEnd_869482] using wordTrace_append hprefix tailTrace_869482
  have hstable : (prefixWord ++ tailWord_869482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869482).length < 2 ^ (prefixWord ++ tailWord_869482).sum := by decide
  have hdescent : baseEnd_869482 < baseStart_869482 := by decide
  rcases family_descends (prefixWord ++ tailWord_869482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869485 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 2]
def baseStart_869485 : Nat := 118140960795 + 869485 * 2 ^ 59
def prefixEnd_869485 : Nat := 4983230072969 + 3 ^ 40 * 869485 * 2
def baseEnd_869485 : Nat := 396856646110787439678949

theorem tailTrace_869485 : CollatzResearch.WordTrace tailWord_869485 prefixEnd_869485 396856646110787439678949 := by
  unfold tailWord_869485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31712723255011816060721909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21141815503341210707147939 31712723255011816060721909)
  ·
    refine ⟨2973067805157357755692679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31712723255011816060721909 2973067805157357755692679)
    ·
      refine ⟨4459601707736036633539019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973067805157357755692679 4459601707736036633539019)
      ·
        refine ⟨6689402561604054950308529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4459601707736036633539019 6689402561604054950308529)
        ·
          refine ⟨5017051921203041212731397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6689402561604054950308529 5017051921203041212731397)
          ·
            refine ⟨940697235225570227387137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5017051921203041212731397 940697235225570227387137)
            ·
              refine ⟨705522926419177670540353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940697235225570227387137 705522926419177670540353)
              ·
                refine ⟨529142194814383252905265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705522926419177670540353 529142194814383252905265)
                ·
                  refine ⟨396856646110787439678949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529142194814383252905265 396856646110787439678949)
                  ·
                    rfl

theorem cell20_869485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_869485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869485 prefixEnd_869485 := by exact prefixLift 869485
  have htrace : WordTrace (prefixWord ++ tailWord_869485) baseStart_869485 baseEnd_869485 := by
    simpa [prefixWord, tailWord_869485, baseEnd_869485] using wordTrace_append hprefix tailTrace_869485
  have hstable : (prefixWord ++ tailWord_869485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869485).length < 2 ^ (prefixWord ++ tailWord_869485).sum := by decide
  have hdescent : baseEnd_869485 < baseStart_869485 := by decide
  rcases family_descends (prefixWord ++ tailWord_869485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869527 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 2]
def baseStart_869527 : Nat := 118140960795 + 869527 * 2 ^ 59
def prefixEnd_869527 : Nat := 4983230072969 + 3 ^ 40 * 869527 * 2
def baseEnd_869527 : Nat := 396875816055221960278777

theorem tailTrace_869527 : CollatzResearch.WordTrace tailWord_869527 prefixEnd_869527 396875816055221960278777 := by
  unfold tailWord_869527
  simp only [CollatzResearch.WordTrace]
  refine ⟨31714255120859657233750835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21142836747239771489167223 31714255120859657233750835)
  ·
    refine ⟨47571382681289485850626253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31714255120859657233750835 47571382681289485850626253)
    ·
      refine ⟨17839268505483557193984845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47571382681289485850626253 17839268505483557193984845)
      ·
        refine ⟨6689725689556333947744317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17839268505483557193984845 6689725689556333947744317)
        ·
          refine ⟨2508647133583625230404119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6689725689556333947744317 2508647133583625230404119)
          ·
            refine ⟨3762970700375437845606179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2508647133583625230404119 3762970700375437845606179)
            ·
              refine ⟨5644456050563156768409269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3762970700375437845606179 5644456050563156768409269)
              ·
                refine ⟨529167754740295947038369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5644456050563156768409269 529167754740295947038369)
                ·
                  refine ⟨396875816055221960278777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529167754740295947038369 396875816055221960278777)
                  ·
                    rfl

theorem cell20_869527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 2].length) (baseStart_869527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869527 prefixEnd_869527 := by exact prefixLift 869527
  have htrace : WordTrace (prefixWord ++ tailWord_869527) baseStart_869527 baseEnd_869527 := by
    simpa [prefixWord, tailWord_869527, baseEnd_869527] using wordTrace_append hprefix tailTrace_869527
  have hstable : (prefixWord ++ tailWord_869527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869527).length < 2 ^ (prefixWord ++ tailWord_869527).sum := by decide
  have hdescent : baseEnd_869527 < baseStart_869527 := by decide
  rcases family_descends (prefixWord ++ tailWord_869527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869534 : List Nat := [4, 3, 1, 1, 2, 2, 7]
def baseStart_869534 : Nat := 118140960795 + 869534 * 2 ^ 59
def prefixEnd_869534 : Nat := 4983230072969 + 3 ^ 40 * 869534 * 2
def baseEnd_869534 : Nat := 44097667893995671893935

theorem tailTrace_869534 : CollatzResearch.WordTrace tailWord_869534 prefixEnd_869534 44097667893995671893935 := by
  unfold tailWord_869534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964313803979287178656957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21143006954556198286170437 3964313803979287178656957)
  ·
    refine ⟨1486617676492232691996359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3964313803979287178656957 1486617676492232691996359)
    ·
      refine ⟨2229926514738349037994539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1486617676492232691996359 2229926514738349037994539)
      ·
        refine ⟨3344889772107523556991809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2229926514738349037994539 3344889772107523556991809)
        ·
          refine ⟨2508667329080642667743857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3344889772107523556991809 2508667329080642667743857)
          ·
            refine ⟨1881500496810482000807893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508667329080642667743857 1881500496810482000807893)
            ·
              refine ⟨44097667893995671893935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1881500496810482000807893 44097667893995671893935)
              ·
                rfl

theorem cell20_869534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 7].length) (baseStart_869534 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869534 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869534 prefixEnd_869534 := by exact prefixLift 869534
  have htrace : WordTrace (prefixWord ++ tailWord_869534) baseStart_869534 baseEnd_869534 := by
    simpa [prefixWord, tailWord_869534, baseEnd_869534] using wordTrace_append hprefix tailTrace_869534
  have hstable : (prefixWord ++ tailWord_869534).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869534).length < 2 ^ (prefixWord ++ tailWord_869534).sum := by decide
  have hdescent : baseEnd_869534 < baseStart_869534 := by decide
  rcases family_descends (prefixWord ++ tailWord_869534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869541 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 3]
def baseStart_869541 : Nat := 118140960795 + 869541 * 2 ^ 59
def prefixEnd_869541 : Nat := 4983230072969 + 3 ^ 40 * 869541 * 2
def baseEnd_869541 : Nat := 396882206036700133812053

theorem tailTrace_869541 : CollatzResearch.WordTrace tailWord_869541 prefixEnd_869541 396882206036700133812053 := by
  unfold tailWord_869541
  simp only [CollatzResearch.WordTrace]
  refine ⟨31714765742808937624760477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21143177161872625083173651 31714765742808937624760477)
  ·
    refine ⟨11893037153553351609285179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31714765742808937624760477 11893037153553351609285179)
    ·
      refine ⟨17839555730330027413927769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11893037153553351609285179 17839555730330027413927769)
      ·
        refine ⟨13379666797747520560445827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17839555730330027413927769 13379666797747520560445827)
        ·
          refine ⟨20069500196621280840668741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13379666797747520560445827 20069500196621280840668741)
          ·
            refine ⟨3763031286866490157625389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20069500196621280840668741 3763031286866490157625389)
            ·
              refine ⟨1411136732574933809109521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3763031286866490157625389 1411136732574933809109521)
              ·
                refine ⟨1058352549431200356832141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411136732574933809109521 1058352549431200356832141)
                ·
                  refine ⟨396882206036700133812053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058352549431200356832141 396882206036700133812053)
                  ·
                    rfl

theorem cell20_869541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_869541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869541 prefixEnd_869541 := by exact prefixLift 869541
  have htrace : WordTrace (prefixWord ++ tailWord_869541) baseStart_869541 baseEnd_869541 := by
    simpa [prefixWord, tailWord_869541, baseEnd_869541] using wordTrace_append hprefix tailTrace_869541
  have hstable : (prefixWord ++ tailWord_869541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869541).length < 2 ^ (prefixWord ++ tailWord_869541).sum := by decide
  have hdescent : baseEnd_869541 < baseStart_869541 := by decide
  rcases family_descends (prefixWord ++ tailWord_869541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869572 : List Nat := [2, 3, 3, 1, 3, 1, 1, 6]
def baseStart_869572 : Nat := 118140960795 + 869572 * 2 ^ 59
def prefixEnd_869572 : Nat := 4983230072969 + 3 ^ 40 * 869572 * 2
def baseEnd_869572 : Nat := 132298785093800601259531

theorem tailTrace_869572 : CollatzResearch.WordTrace tailWord_869572 prefixEnd_869572 132298785093800601259531 := by
  unfold tailWord_869572
  simp only [CollatzResearch.WordTrace]
  refine ⟨15857948202848314959569485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21143930937131086612759313 15857948202848314959569485)
  ·
    refine ⟨5946730576068118109838557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15857948202848314959569485 5946730576068118109838557)
    ·
      refine ⟨2230023966025544291189459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5946730576068118109838557 2230023966025544291189459)
      ·
        refine ⟨3345035949038316436784189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230023966025544291189459 3345035949038316436784189)
        ·
          refine ⟨1254388480889368663794071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3345035949038316436784189 1254388480889368663794071)
          ·
            refine ⟨1881582721334052995691107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254388480889368663794071 1881582721334052995691107)
            ·
              refine ⟨2822374082001079493536661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1881582721334052995691107 2822374082001079493536661)
              ·
                refine ⟨132298785093800601259531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2822374082001079493536661 132298785093800601259531)
                ·
                  rfl

theorem cell20_869572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 6].length) (baseStart_869572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869572 prefixEnd_869572 := by exact prefixLift 869572
  have htrace : WordTrace (prefixWord ++ tailWord_869572) baseStart_869572 baseEnd_869572 := by
    simpa [prefixWord, tailWord_869572, baseEnd_869572] using wordTrace_append hprefix tailTrace_869572
  have hstable : (prefixWord ++ tailWord_869572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869572).length < 2 ^ (prefixWord ++ tailWord_869572).sum := by decide
  have hdescent : baseEnd_869572 < baseStart_869572 := by decide
  rcases family_descends (prefixWord ++ tailWord_869572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869574 : List Nat := [6, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_869574 : Nat := 118140960795 + 869574 * 2 ^ 59
def prefixEnd_869574 : Nat := 4983230072969 + 3 ^ 40 * 869574 * 2
def baseEnd_869574 : Nat := 396897268135898685711919

theorem tailTrace_869574 : CollatzResearch.WordTrace tailWord_869574 prefixEnd_869574 396897268135898685711919 := by
  unfold tailWord_869574
  simp only [CollatzResearch.WordTrace]
  refine ⟨991124042240293258147243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 21143979567792922840474517 991124042240293258147243)
  ·
    refine ⟨1486686063360439887220865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 991124042240293258147243 1486686063360439887220865)
    ·
      refine ⟨1115014547520329915415649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1486686063360439887220865 1115014547520329915415649)
      ·
        refine ⟨836260910640247436561737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1115014547520329915415649 836260910640247436561737)
        ·
          refine ⟨627195682980185577421303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836260910640247436561737 627195682980185577421303)
          ·
            refine ⟨940793524470278366131955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627195682980185577421303 940793524470278366131955)
            ·
              refine ⟨1411190286705417549197933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940793524470278366131955 1411190286705417549197933)
              ·
                refine ⟨529196357514531580949225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1411190286705417549197933 529196357514531580949225)
                ·
                  refine ⟨396897268135898685711919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529196357514531580949225 396897268135898685711919)
                  ·
                    rfl

theorem cell20_869574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_869574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869574 prefixEnd_869574 := by exact prefixLift 869574
  have htrace : WordTrace (prefixWord ++ tailWord_869574) baseStart_869574 baseEnd_869574 := by
    simpa [prefixWord, tailWord_869574, baseEnd_869574] using wordTrace_append hprefix tailTrace_869574
  have hstable : (prefixWord ++ tailWord_869574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869574).length < 2 ^ (prefixWord ++ tailWord_869574).sum := by decide
  have hdescent : baseEnd_869574 < baseStart_869574 := by decide
  rcases family_descends (prefixWord ++ tailWord_869574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869600 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 5]
def baseStart_869600 : Nat := 118140960795 + 869600 * 2 ^ 59
def prefixEnd_869600 : Nat := 4983230072969 + 3 ^ 40 * 869600 * 2
def baseEnd_869600 : Nat := 396909135244358150845145

theorem tailTrace_869600 : CollatzResearch.WordTrace tailWord_869600 prefixEnd_869600 396909135244358150845145 := by
  unfold tailWord_869600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15858458824797595350579127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21144611766396793800772169 15858458824797595350579127)
  ·
    refine ⟨23787688237196393025868691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15858458824797595350579127 23787688237196393025868691)
    ·
      refine ⟨35681532355794589538803037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23787688237196393025868691 35681532355794589538803037)
      ·
        refine ⟨13380574633422971077051139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35681532355794589538803037 13380574633422971077051139)
        ·
          refine ⟨20070861950134456615576709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13380574633422971077051139 20070861950134456615576709)
          ·
            refine ⟨3763286615650210615420633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20070861950134456615576709 3763286615650210615420633)
            ·
              refine ⟨2822464961737657961565475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763286615650210615420633 2822464961737657961565475)
              ·
                refine ⟨4233697442606486942348213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2822464961737657961565475 4233697442606486942348213)
                ·
                  refine ⟨396909135244358150845145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4233697442606486942348213 396909135244358150845145)
                  ·
                    rfl

theorem cell20_869600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_869600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869600 prefixEnd_869600 := by exact prefixLift 869600
  have htrace : WordTrace (prefixWord ++ tailWord_869600) baseStart_869600 baseEnd_869600 := by
    simpa [prefixWord, tailWord_869600, baseEnd_869600] using wordTrace_append hprefix tailTrace_869600
  have hstable : (prefixWord ++ tailWord_869600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869600).length < 2 ^ (prefixWord ++ tailWord_869600).sum := by decide
  have hdescent : baseEnd_869600 < baseStart_869600 := by decide
  rcases family_descends (prefixWord ++ tailWord_869600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869613 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 3]
def baseStart_869613 : Nat := 118140960795 + 869613 * 2 ^ 59
def prefixEnd_869613 : Nat := 4983230072969 + 3 ^ 40 * 869613 * 2
def baseEnd_869613 : Nat := 396915068798587883411759

theorem tailTrace_869613 : CollatzResearch.WordTrace tailWord_869613 prefixEnd_869613 396915068798587883411759 := by
  unfold tailWord_869613
  simp only [CollatzResearch.WordTrace]
  refine ⟨31717391798548093921381493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21144927865698729280920995 31717391798548093921381493)
  ·
    refine ⟨2973505481113883805129515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31717391798548093921381493 2973505481113883805129515)
    ·
      refine ⟨4460258221670825707694273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973505481113883805129515 4460258221670825707694273)
      ·
        refine ⟨3345193666253119280770705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4460258221670825707694273 3345193666253119280770705)
        ·
          refine ⟨2508895249689839460578029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3345193666253119280770705 2508895249689839460578029)
          ·
            refine ⟨940835718633689797716761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2508895249689839460578029 940835718633689797716761)
            ·
              refine ⟨705626788975267348287571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 940835718633689797716761 705626788975267348287571)
              ·
                refine ⟨1058440183462901022431357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705626788975267348287571 1058440183462901022431357)
                ·
                  refine ⟨396915068798587883411759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058440183462901022431357 396915068798587883411759)
                  ·
                    rfl

theorem cell20_869613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_869613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869613 prefixEnd_869613 := by exact prefixLift 869613
  have htrace : WordTrace (prefixWord ++ tailWord_869613) baseStart_869613 baseEnd_869613 := by
    simpa [prefixWord, tailWord_869613, baseEnd_869613] using wordTrace_append hprefix tailTrace_869613
  have hstable : (prefixWord ++ tailWord_869613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869613).length < 2 ^ (prefixWord ++ tailWord_869613).sum := by decide
  have hdescent : baseEnd_869613 < baseStart_869613 := by decide
  rcases family_descends (prefixWord ++ tailWord_869613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869652 : List Nat := [2, 4, 14]
def baseStart_869652 : Nat := 118140960795 + 869652 * 2 ^ 59
def prefixEnd_869652 : Nat := 4983230072969 + 3 ^ 40 * 869652 * 2
def baseEnd_869652 : Nat := 544489532868692841031

theorem tailTrace_869652 : CollatzResearch.WordTrace tailWord_869652 prefixEnd_869652 544489532868692841031 := by
  unfold tailWord_869652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15859407122703401791025605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21145876163604535721367473 15859407122703401791025605)
  ·
    refine ⟨2973638835506887835817301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15859407122703401791025605 2973638835506887835817301)
    ·
      refine ⟨544489532868692841031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 14 2973638835506887835817301 544489532868692841031)
      ·
        rfl

theorem cell20_869652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 14].length) (baseStart_869652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869652 prefixEnd_869652 := by exact prefixLift 869652
  have htrace : WordTrace (prefixWord ++ tailWord_869652) baseStart_869652 baseEnd_869652 := by
    simpa [prefixWord, tailWord_869652, baseEnd_869652] using wordTrace_append hprefix tailTrace_869652
  have hstable : (prefixWord ++ tailWord_869652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869652).length < 2 ^ (prefixWord ++ tailWord_869652).sum := by decide
  have hdescent : baseEnd_869652 < baseStart_869652 := by decide
  rcases family_descends (prefixWord ++ tailWord_869652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869655 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 3]
def baseStart_869655 : Nat := 118140960795 + 869655 * 2 ^ 59
def prefixEnd_869655 : Nat := 4983230072969 + 3 ^ 40 * 869655 * 2
def baseEnd_869655 : Nat := 396934238743022404011587

theorem tailTrace_869655 : CollatzResearch.WordTrace tailWord_869655 prefixEnd_869655 396934238743022404011587 := by
  unfold tailWord_869655
  simp only [CollatzResearch.WordTrace]
  refine ⟨31718923664395935094410419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21145949109597290062940279 31718923664395935094410419)
  ·
    refine ⟨47578385496593902641615629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31718923664395935094410419 47578385496593902641615629)
    ·
      refine ⟨17841894561222713490605861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47578385496593902641615629 17841894561222713490605861)
      ·
        refine ⟨3345355230229258779488599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17841894561222713490605861 3345355230229258779488599)
        ·
          refine ⟨5018032845343888169232899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3345355230229258779488599 5018032845343888169232899)
          ·
            refine ⟨7527049268015832253849349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5018032845343888169232899 7527049268015832253849349)
            ·
              refine ⟨1411321737752968547596753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7527049268015832253849349 1411321737752968547596753)
              ·
                refine ⟨1058491303314726410697565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1411321737752968547596753 1058491303314726410697565)
                ·
                  refine ⟨396934238743022404011587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058491303314726410697565 396934238743022404011587)
                  ·
                    rfl

theorem cell20_869655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 3].length) (baseStart_869655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869655 prefixEnd_869655 := by exact prefixLift 869655
  have htrace : WordTrace (prefixWord ++ tailWord_869655) baseStart_869655 baseEnd_869655 := by
    simpa [prefixWord, tailWord_869655, baseEnd_869655] using wordTrace_append hprefix tailTrace_869655
  have hstable : (prefixWord ++ tailWord_869655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869655).length < 2 ^ (prefixWord ++ tailWord_869655).sum := by decide
  have hdescent : baseEnd_869655 < baseStart_869655 := by decide
  rcases family_descends (prefixWord ++ tailWord_869655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869658 : List Nat := [3, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_869658 : Nat := 118140960795 + 869658 * 2 ^ 59
def prefixEnd_869658 : Nat := 4983230072969 + 3 ^ 40 * 869658 * 2
def baseEnd_869658 : Nat := 396935608024767726911575

theorem tailTrace_869658 : CollatzResearch.WordTrace tailWord_869658 prefixEnd_869658 396935608024767726911575 := by
  unfold tailWord_869658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7929758270846266651692407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21146022055590044404513085 7929758270846266651692407)
  ·
    refine ⟨11894637406269399977538611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7929758270846266651692407 11894637406269399977538611)
    ·
      refine ⟨17841956109404099966307917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894637406269399977538611 17841956109404099966307917)
      ·
        refine ⟨6690733541026537487365469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17841956109404099966307917 6690733541026537487365469)
        ·
          refine ⟨2509025077884951557762051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6690733541026537487365469 2509025077884951557762051)
          ·
            refine ⟨3763537616827427336643077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509025077884951557762051 3763537616827427336643077)
            ·
              refine ⟨705663303155142625620577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3763537616827427336643077 705663303155142625620577)
              ·
                refine ⟨529247477366356969215433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705663303155142625620577 529247477366356969215433)
                ·
                  refine ⟨396935608024767726911575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529247477366356969215433 396935608024767726911575)
                  ·
                    rfl

theorem cell20_869658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_869658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869658 prefixEnd_869658 := by exact prefixLift 869658
  have htrace : WordTrace (prefixWord ++ tailWord_869658) baseStart_869658 baseEnd_869658 := by
    simpa [prefixWord, tailWord_869658, baseEnd_869658] using wordTrace_append hprefix tailTrace_869658
  have hstable : (prefixWord ++ tailWord_869658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869658).length < 2 ^ (prefixWord ++ tailWord_869658).sum := by decide
  have hdescent : baseEnd_869658 < baseStart_869658 := by decide
  rcases family_descends (prefixWord ++ tailWord_869658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869669 : List Nat := [1, 3, 1, 2, 4, 1, 3, 5]
def baseStart_869669 : Nat := 118140960795 + 869669 * 2 ^ 59
def prefixEnd_869669 : Nat := 4983230072969 + 3 ^ 40 * 869669 * 2
def baseEnd_869669 : Nat := 132313542908166859181621

theorem tailTrace_869669 : CollatzResearch.WordTrace tailWord_869669 prefixEnd_869669 132313542908166859181621 := by
  unfold tailWord_869669
  simp only [CollatzResearch.WordTrace]
  refine ⟨31719434286345215485420061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21146289524230143656946707 31719434286345215485420061)
  ·
    refine ⟨11894787857379455807032523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31719434286345215485420061 11894787857379455807032523)
    ·
      refine ⟨17842181786069183710548785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11894787857379455807032523 17842181786069183710548785)
      ·
        refine ⟨13381636339551887782911589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17842181786069183710548785 13381636339551887782911589)
        ·
          refine ⟨2509056813665978959295923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13381636339551887782911589 2509056813665978959295923)
          ·
            refine ⟨3763585220498968438943885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509056813665978959295923 3763585220498968438943885)
            ·
              refine ⟨1411344457687113164603957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3763585220498968438943885 1411344457687113164603957)
              ·
                refine ⟨132313542908166859181621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1411344457687113164603957 132313542908166859181621)
                ·
                  rfl

theorem cell20_869669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_869669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869669 prefixEnd_869669 := by exact prefixLift 869669
  have htrace : WordTrace (prefixWord ++ tailWord_869669) baseStart_869669 baseEnd_869669 := by
    simpa [prefixWord, tailWord_869669, baseEnd_869669] using wordTrace_append hprefix tailTrace_869669
  have hstable : (prefixWord ++ tailWord_869669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869669).length < 2 ^ (prefixWord ++ tailWord_869669).sum := by decide
  have hdescent : baseEnd_869669 < baseStart_869669 := by decide
  rcases family_descends (prefixWord ++ tailWord_869669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869683 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 6]
def baseStart_869683 : Nat := 118140960795 + 869683 * 2 ^ 59
def prefixEnd_869683 : Nat := 4983230072969 + 3 ^ 40 * 869683 * 2
def baseEnd_869683 : Nat := 396947018705978751078139

theorem tailTrace_869683 : CollatzResearch.WordTrace tailWord_869683 prefixEnd_869683 396947018705978751078139 := by
  unfold tailWord_869683
  simp only [CollatzResearch.WordTrace]
  refine ⟨31719944908294495876429703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21146629938862997250953135 31719944908294495876429703)
  ·
    refine ⟨47579917362441743814644555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31719944908294495876429703 47579917362441743814644555)
    ·
      refine ⟨71369876043662615721966833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47579917362441743814644555 71369876043662615721966833)
      ·
        refine ⟨53527407032746961791475125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71369876043662615721966833 53527407032746961791475125)
        ·
          refine ⟨5018194409320027667950793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53527407032746961791475125 5018194409320027667950793)
          ·
            refine ⟨3763645806990020750963095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5018194409320027667950793 3763645806990020750963095)
            ·
              refine ⟨5645468710485031126444643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3763645806990020750963095 5645468710485031126444643)
              ·
                refine ⟨8468203065727546689666965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5645468710485031126444643 8468203065727546689666965)
                ·
                  refine ⟨396947018705978751078139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8468203065727546689666965 396947018705978751078139)
                  ·
                    rfl

theorem cell20_869683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_869683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869683 prefixEnd_869683 := by exact prefixLift 869683
  have htrace : WordTrace (prefixWord ++ tailWord_869683) baseStart_869683 baseEnd_869683 := by
    simpa [prefixWord, tailWord_869683, baseEnd_869683] using wordTrace_append hprefix tailTrace_869683
  have hstable : (prefixWord ++ tailWord_869683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869683).length < 2 ^ (prefixWord ++ tailWord_869683).sum := by decide
  have hdescent : baseEnd_869683 < baseStart_869683 := by decide
  rcases family_descends (prefixWord ++ tailWord_869683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869717 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 2]
def baseStart_869717 : Nat := 118140960795 + 869717 * 2 ^ 59
def prefixEnd_869717 : Nat := 4983230072969 + 3 ^ 40 * 869717 * 2
def baseEnd_869717 : Nat := 396962537232425743944667

theorem tailTrace_869717 : CollatzResearch.WordTrace tailWord_869717 prefixEnd_869717 396962537232425743944667 := by
  unfold tailWord_869717
  simp only [CollatzResearch.WordTrace]
  refine ⟨31721184990171319683167405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21147456660114213122111603 31721184990171319683167405)
  ·
    refine ⟨11895444371314244881187777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31721184990171319683167405 11895444371314244881187777)
    ·
      refine ⟨8921583278485683660890833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11895444371314244881187777 8921583278485683660890833)
      ·
        refine ⟨6691187458864262745668125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8921583278485683660890833 6691187458864262745668125)
        ·
          refine ⟨2509195297074098529625547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6691187458864262745668125 2509195297074098529625547)
          ·
            refine ⟨3763792945611147794438321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509195297074098529625547 3763792945611147794438321)
            ·
              refine ⟨2822844709208360845828741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3763792945611147794438321 2822844709208360845828741)
              ·
                refine ⟨529283382976567658592889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2822844709208360845828741 529283382976567658592889)
                ·
                  refine ⟨396962537232425743944667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529283382976567658592889 396962537232425743944667)
                  ·
                    rfl

theorem cell20_869717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_869717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869717 prefixEnd_869717 := by exact prefixLift 869717
  have htrace : WordTrace (prefixWord ++ tailWord_869717) baseStart_869717 baseEnd_869717 := by
    simpa [prefixWord, tailWord_869717, baseEnd_869717] using wordTrace_append hprefix tailTrace_869717
  have hstable : (prefixWord ++ tailWord_869717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869717).length < 2 ^ (prefixWord ++ tailWord_869717).sum := by decide
  have hdescent : baseEnd_869717 < baseStart_869717 := by decide
  rcases family_descends (prefixWord ++ tailWord_869717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869721 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 4]
def baseStart_869721 : Nat := 118140960795 + 869721 * 2 ^ 59
def prefixEnd_869721 : Nat := 4983230072969 + 3 ^ 40 * 869721 * 2
def baseEnd_869721 : Nat := 396964362941419507811317

theorem tailTrace_869721 : CollatzResearch.WordTrace tailWord_869721 prefixEnd_869721 396964362941419507811317 := by
  unfold tailWord_869721
  simp only [CollatzResearch.WordTrace]
  refine ⟨31721330882156828366313017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21147553921437885577542011 31721330882156828366313017)
  ·
    refine ⟨23790998161617621274734763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31721330882156828366313017 23790998161617621274734763)
    ·
      refine ⟨35686497242426431912102145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23790998161617621274734763 35686497242426431912102145)
      ·
        refine ⟨26764872931819823934076609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35686497242426431912102145 26764872931819823934076609)
        ·
          refine ⟨20073654698864867950557457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26764872931819823934076609 20073654698864867950557457)
          ·
            refine ⟨15055241024148650962918093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20073654698864867950557457 15055241024148650962918093)
            ·
              refine ⟨5645715384055744111094285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15055241024148650962918093 5645715384055744111094285)
              ·
                refine ⟨2117143269020904041660357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5645715384055744111094285 2117143269020904041660357)
                ·
                  refine ⟨396964362941419507811317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117143269020904041660357 396964362941419507811317)
                  ·
                    rfl

theorem cell20_869721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_869721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869721 prefixEnd_869721 := by exact prefixLift 869721
  have htrace : WordTrace (prefixWord ++ tailWord_869721) baseStart_869721 baseEnd_869721 := by
    simpa [prefixWord, tailWord_869721, baseEnd_869721] using wordTrace_append hprefix tailTrace_869721
  have hstable : (prefixWord ++ tailWord_869721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869721).length < 2 ^ (prefixWord ++ tailWord_869721).sum := by decide
  have hdescent : baseEnd_869721 < baseStart_869721 := by decide
  rcases family_descends (prefixWord ++ tailWord_869721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869745 : List Nat := [1, 2, 2, 2, 1, 2, 6, 4]
def baseStart_869745 : Nat := 118140960795 + 869745 * 2 ^ 59
def prefixEnd_869745 : Nat := 4983230072969 + 3 ^ 40 * 869745 * 2
def baseEnd_869745 : Nat := 132325105731794030337073

theorem tailTrace_869745 : CollatzResearch.WordTrace tailWord_869745 prefixEnd_869745 132325105731794030337073 := by
  unfold tailWord_869745
  simp only [CollatzResearch.WordTrace]
  refine ⟨31722206234069880465186689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21148137489379920310124459 31722206234069880465186689)
  ·
    refine ⟨23791654675552410348890017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31722206234069880465186689 23791654675552410348890017)
    ·
      refine ⟨17843741006664307761667513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23791654675552410348890017 17843741006664307761667513)
      ·
        refine ⟨13382805754998230821250635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17843741006664307761667513 13382805754998230821250635)
        ·
          refine ⟨20074208632497346231875953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13382805754998230821250635 20074208632497346231875953)
          ·
            refine ⟨15055656474373009673906965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20074208632497346231875953 15055656474373009673906965)
            ·
              refine ⟨705733897236234828464389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15055656474373009673906965 705733897236234828464389)
              ·
                refine ⟨132325105731794030337073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 705733897236234828464389 132325105731794030337073)
                ·
                  rfl

theorem cell20_869745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 4].length) (baseStart_869745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869745 prefixEnd_869745 := by exact prefixLift 869745
  have htrace : WordTrace (prefixWord ++ tailWord_869745) baseStart_869745 baseEnd_869745 := by
    simpa [prefixWord, tailWord_869745, baseEnd_869745] using wordTrace_append hprefix tailTrace_869745
  have hstable : (prefixWord ++ tailWord_869745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869745).length < 2 ^ (prefixWord ++ tailWord_869745).sum := by decide
  have hdescent : baseEnd_869745 < baseStart_869745 := by decide
  rcases family_descends (prefixWord ++ tailWord_869745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869758 : List Nat := [4, 2, 3, 2, 2, 1, 6]
def baseStart_869758 : Nat := 118140960795 + 869758 * 2 ^ 59
def prefixEnd_869758 : Nat := 4983230072969 + 3 ^ 40 * 869758 * 2
def baseEnd_869758 : Nat := 44109027861067980397537

theorem tailTrace_869758 : CollatzResearch.WordTrace tailWord_869758 prefixEnd_869758 44109027861067980397537 := by
  unfold tailWord_869758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965335047877847960676241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21148453588681855790273285 3965335047877847960676241)
  ·
    refine ⟨2974001285908385970507181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3965335047877847960676241 2974001285908385970507181)
    ·
      refine ⟨1115250482215644738940193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2974001285908385970507181 1115250482215644738940193)
      ·
        refine ⟨836437861661733554205145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1115250482215644738940193 836437861661733554205145)
        ·
          refine ⟨627328396246300165653859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836437861661733554205145 627328396246300165653859)
          ·
            refine ⟨940992594369450248480789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 627328396246300165653859 940992594369450248480789)
            ·
              refine ⟨44109027861067980397537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 940992594369450248480789 44109027861067980397537)
              ·
                rfl

theorem cell20_869758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 6].length) (baseStart_869758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869758 prefixEnd_869758 := by exact prefixLift 869758
  have htrace : WordTrace (prefixWord ++ tailWord_869758) baseStart_869758 baseEnd_869758 := by
    simpa [prefixWord, tailWord_869758, baseEnd_869758] using wordTrace_append hprefix tailTrace_869758
  have hstable : (prefixWord ++ tailWord_869758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869758).length < 2 ^ (prefixWord ++ tailWord_869758).sum := by decide
  have hdescent : baseEnd_869758 < baseStart_869758 := by decide
  rcases family_descends (prefixWord ++ tailWord_869758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869762 : List Nat := [3, 4, 2, 1, 1, 1, 8]
def baseStart_869762 : Nat := 118140960795 + 869762 * 2 ^ 59
def prefixEnd_869762 : Nat := 4983230072969 + 3 ^ 40 * 869762 * 2
def baseEnd_869762 : Nat := 44109230717622843049387

theorem tailTrace_869762 : CollatzResearch.WordTrace tailWord_869762 prefixEnd_869762 44109230717622843049387 := by
  unfold tailWord_869762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930706568752073092138885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21148550850005528245703693 7930706568752073092138885)
  ·
    refine ⟨1487007481641013704776041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7930706568752073092138885 1487007481641013704776041)
    ·
      refine ⟨1115255611230760278582031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1487007481641013704776041 1115255611230760278582031)
      ·
        refine ⟨1672883416846140417873047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115255611230760278582031 1672883416846140417873047)
        ·
          refine ⟨2509325125269210626809571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672883416846140417873047 2509325125269210626809571)
          ·
            refine ⟨3763987687903815940214357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2509325125269210626809571 3763987687903815940214357)
            ·
              refine ⟨44109230717622843049387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3763987687903815940214357 44109230717622843049387)
              ·
                rfl

theorem cell20_869762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 8].length) (baseStart_869762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869762 prefixEnd_869762 := by exact prefixLift 869762
  have htrace : WordTrace (prefixWord ++ tailWord_869762) baseStart_869762 baseEnd_869762 := by
    simpa [prefixWord, tailWord_869762, baseEnd_869762] using wordTrace_append hprefix tailTrace_869762
  have hstable : (prefixWord ++ tailWord_869762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869762).length < 2 ^ (prefixWord ++ tailWord_869762).sum := by decide
  have hdescent : baseEnd_869762 < baseStart_869762 := by decide
  rcases family_descends (prefixWord ++ tailWord_869762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869804 : List Nat := [2, 2, 1, 1, 1, 1, 6, 6]
def baseStart_869804 : Nat := 118140960795 + 869804 * 2 ^ 59
def prefixEnd_869804 : Nat := 4983230072969 + 3 ^ 40 * 869804 * 2
def baseEnd_869804 : Nat := 132334082134346702681437

theorem tailTrace_869804 : CollatzResearch.WordTrace tailWord_869804 prefixEnd_869804 132334082134346702681437 := by
  unfold tailWord_869804
  simp only [CollatzResearch.WordTrace]
  refine ⟨15862179070428066770792233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21149572093904089027722977 15862179070428066770792233)
  ·
    refine ⟨11896634302821050078094175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15862179070428066770792233 11896634302821050078094175)
    ·
      refine ⟨17844951454231575117141263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11896634302821050078094175 17844951454231575117141263)
      ·
        refine ⟨26767427181347362675711895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17844951454231575117141263 26767427181347362675711895)
        ·
          refine ⟨40151140772021044013567843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26767427181347362675711895 40151140772021044013567843)
          ·
            refine ⟨60226711158031566020351765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40151140772021044013567843 60226711158031566020351765)
            ·
              refine ⟨2823127085532729657203989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 60226711158031566020351765 2823127085532729657203989)
              ·
                refine ⟨132334082134346702681437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2823127085532729657203989 132334082134346702681437)
                ·
                  rfl

theorem cell20_869804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_869804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869804 prefixEnd_869804 := by exact prefixLift 869804
  have htrace : WordTrace (prefixWord ++ tailWord_869804) baseStart_869804 baseEnd_869804 := by
    simpa [prefixWord, tailWord_869804, baseEnd_869804] using wordTrace_append hprefix tailTrace_869804
  have hstable : (prefixWord ++ tailWord_869804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869804).length < 2 ^ (prefixWord ++ tailWord_869804).sum := by decide
  have hdescent : baseEnd_869804 < baseStart_869804 := by decide
  rcases family_descends (prefixWord ++ tailWord_869804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869811 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 7]
def baseStart_869811 : Nat := 118140960795 + 869811 * 2 ^ 59
def prefixEnd_869811 : Nat := 4983230072969 + 3 ^ 40 * 869811 * 2
def baseEnd_869811 : Nat := 397005441393779194810949

theorem tailTrace_869811 : CollatzResearch.WordTrace tailWord_869811 prefixEnd_869811 397005441393779194810949 := by
  unfold tailWord_869811
  simp only [CollatzResearch.WordTrace]
  refine ⟨31724613451830773737089287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21149742301220515824726191 31724613451830773737089287)
  ·
    refine ⟨47586920177746160605633931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31724613451830773737089287 47586920177746160605633931)
    ·
      refine ⟨71380380266619240908450897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47586920177746160605633931 71380380266619240908450897)
      ·
        refine ⟨53535285199964430681338173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71380380266619240908450897 53535285199964430681338173)
        ·
          refine ⟨20075731949986661505501815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53535285199964430681338173 20075731949986661505501815)
          ·
            refine ⟨30113597924979992258252723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20075731949986661505501815 30113597924979992258252723)
            ·
              refine ⟨45170396887469988387379085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30113597924979992258252723 45170396887469988387379085)
              ·
                refine ⟨16938898832801245645267157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45170396887469988387379085 16938898832801245645267157)
                ·
                  refine ⟨397005441393779194810949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16938898832801245645267157 397005441393779194810949)
                  ·
                    rfl

theorem cell20_869811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 7].length) (baseStart_869811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869811 prefixEnd_869811 := by exact prefixLift 869811
  have htrace : WordTrace (prefixWord ++ tailWord_869811) baseStart_869811 baseEnd_869811 := by
    simpa [prefixWord, tailWord_869811, baseEnd_869811] using wordTrace_append hprefix tailTrace_869811
  have hstable : (prefixWord ++ tailWord_869811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869811).length < 2 ^ (prefixWord ++ tailWord_869811).sum := by decide
  have hdescent : baseEnd_869811 < baseStart_869811 := by decide
  rcases family_descends (prefixWord ++ tailWord_869811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869880 : List Nat := [2, 1, 2, 1, 1, 6, 7]
def baseStart_869880 : Nat := 118140960795 + 869880 * 2 ^ 59
def prefixEnd_869880 : Nat := 4983230072969 + 3 ^ 40 * 869880 * 2
def baseEnd_869880 : Nat := 44115214985991291278963

theorem tailTrace_869880 : CollatzResearch.WordTrace tailWord_869880 prefixEnd_869880 44115214985991291278963 := by
  unfold tailWord_869880
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863565044290399260675547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21151420059053865680900729 15863565044290399260675547)
  ·
    refine ⟨23795347566435598891013321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15863565044290399260675547 23795347566435598891013321)
    ·
      refine ⟨17846510674826699168259991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23795347566435598891013321 17846510674826699168259991)
      ·
        refine ⟨26769766012240048752389987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17846510674826699168259991 26769766012240048752389987)
        ·
          refine ⟨40154649018360073128584981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26769766012240048752389987 40154649018360073128584981)
          ·
            refine ⟨1882249172735628427902421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 40154649018360073128584981 1882249172735628427902421)
            ·
              refine ⟨44115214985991291278963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1882249172735628427902421 44115214985991291278963)
              ·
                rfl

theorem cell20_869880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 7].length) (baseStart_869880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869880 prefixEnd_869880 := by exact prefixLift 869880
  have htrace : WordTrace (prefixWord ++ tailWord_869880) baseStart_869880 baseEnd_869880 := by
    simpa [prefixWord, tailWord_869880, baseEnd_869880] using wordTrace_append hprefix tailTrace_869880
  have hstable : (prefixWord ++ tailWord_869880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869880).length < 2 ^ (prefixWord ++ tailWord_869880).sum := by decide
  have hdescent : baseEnd_869880 < baseStart_869880 := by decide
  rcases family_descends (prefixWord ++ tailWord_869880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869886 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 4]
def baseStart_869886 : Nat := 118140960795 + 869886 * 2 ^ 59
def prefixEnd_869886 : Nat := 4983230072969 + 3 ^ 40 * 869886 * 2
def baseEnd_869886 : Nat := 397039673437412267310643

theorem tailTrace_869886 : CollatzResearch.WordTrace tailWord_869886 prefixEnd_869886 397039673437412267310643 := by
  unfold tailWord_869886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965918615819882693258689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 21151565951039374364046341 3965918615819882693258689)
  ·
    refine ⟨2974438961864912019944017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3965918615819882693258689 2974438961864912019944017)
    ·
      refine ⟨2230829221398684014958013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2974438961864912019944017 2230829221398684014958013)
      ·
        refine ⟨836560958024506505609255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2230829221398684014958013 836560958024506505609255)
        ·
          refine ⟨1254841437036759758413883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836560958024506505609255 1254841437036759758413883)
          ·
            refine ⟨1882262155555139637620825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254841437036759758413883 1882262155555139637620825)
            ·
              refine ⟨1411696616666354728215619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882262155555139637620825 1411696616666354728215619)
              ·
                refine ⟨2117544924999532092323429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411696616666354728215619 2117544924999532092323429)
                ·
                  refine ⟨397039673437412267310643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117544924999532092323429 397039673437412267310643)
                  ·
                    rfl

theorem cell20_869886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_869886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869886 prefixEnd_869886 := by exact prefixLift 869886
  have htrace : WordTrace (prefixWord ++ tailWord_869886) baseStart_869886 baseEnd_869886 := by
    simpa [prefixWord, tailWord_869886, baseEnd_869886] using wordTrace_append hprefix tailTrace_869886
  have hstable : (prefixWord ++ tailWord_869886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869886).length < 2 ^ (prefixWord ++ tailWord_869886).sum := by decide
  have hdescent : baseEnd_869886 < baseStart_869886 := by decide
  rcases family_descends (prefixWord ++ tailWord_869886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869900 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 3]
def baseStart_869900 : Nat := 118140960795 + 869900 * 2 ^ 59
def prefixEnd_869900 : Nat := 4983230072969 + 3 ^ 40 * 869900 * 2
def baseEnd_869900 : Nat := 397046063418890440843919

theorem tailTrace_869900 : CollatzResearch.WordTrace tailWord_869900 prefixEnd_869900 397046063418890440843919 := by
  unfold tailWord_869900
  simp only [CollatzResearch.WordTrace]
  refine ⟨15863929774254170968539577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21151906365672227958052769 15863929774254170968539577)
  ·
    refine ⟨11897947330690628226404683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15863929774254170968539577 11897947330690628226404683)
    ·
      refine ⟨17846920996035942339607025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11897947330690628226404683 17846920996035942339607025)
      ·
        refine ⟨13385190747026956754705269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17846920996035942339607025 13385190747026956754705269)
        ·
          refine ⟨1254861632533777195753619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13385190747026956754705269 1254861632533777195753619)
          ·
            refine ⟨1882292448800665793630429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254861632533777195753619 1882292448800665793630429)
            ·
              refine ⟨705859668300249672611411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1882292448800665793630429 705859668300249672611411)
              ·
                refine ⟨1058789502450374508917117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 705859668300249672611411 1058789502450374508917117)
                ·
                  refine ⟨397046063418890440843919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058789502450374508917117 397046063418890440843919)
                  ·
                    rfl

theorem cell20_869900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3].length) (baseStart_869900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869900 prefixEnd_869900 := by exact prefixLift 869900
  have htrace : WordTrace (prefixWord ++ tailWord_869900) baseStart_869900 baseEnd_869900 := by
    simpa [prefixWord, tailWord_869900, baseEnd_869900] using wordTrace_append hprefix tailTrace_869900
  have hstable : (prefixWord ++ tailWord_869900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869900).length < 2 ^ (prefixWord ++ tailWord_869900).sum := by decide
  have hdescent : baseEnd_869900 < baseStart_869900 := by decide
  rcases family_descends (prefixWord ++ tailWord_869900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869959 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 3]
def baseStart_869959 : Nat := 118140960795 + 869959 * 2 ^ 59
def prefixEnd_869959 : Nat := 4983230072969 + 3 ^ 40 * 869959 * 2
def baseEnd_869959 : Nat := 397072992626548457877011

theorem tailTrace_869959 : CollatzResearch.WordTrace tailWord_869959 prefixEnd_869959 397072992626548457877011 := by
  unfold tailWord_869959
  simp only [CollatzResearch.WordTrace]
  refine ⟨31730011455294595013476931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21153340970196396675651287 31730011455294595013476931)
  ·
    refine ⟨47595017182941892520215397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31730011455294595013476931 47595017182941892520215397)
    ·
      refine ⟨8924065721801604847540387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47595017182941892520215397 8924065721801604847540387)
      ·
        refine ⟨13386098582702407271310581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8924065721801604847540387 13386098582702407271310581)
        ·
          refine ⟨1254946742128350681685367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13386098582702407271310581 1254946742128350681685367)
          ·
            refine ⟨1882420113192526022528051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254946742128350681685367 1882420113192526022528051)
            ·
              refine ⟨2823630169788789033792077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882420113192526022528051 2823630169788789033792077)
              ·
                refine ⟨1058861313670795887672029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2823630169788789033792077 1058861313670795887672029)
                ·
                  refine ⟨397072992626548457877011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1058861313670795887672029 397072992626548457877011)
                  ·
                    rfl

theorem cell20_869959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 3].length) (baseStart_869959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869959 prefixEnd_869959 := by exact prefixLift 869959
  have htrace : WordTrace (prefixWord ++ tailWord_869959) baseStart_869959 baseEnd_869959 := by
    simpa [prefixWord, tailWord_869959, baseEnd_869959] using wordTrace_append hprefix tailTrace_869959
  have hstable : (prefixWord ++ tailWord_869959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869959).length < 2 ^ (prefixWord ++ tailWord_869959).sum := by decide
  have hdescent : baseEnd_869959 < baseStart_869959 := by decide
  rcases family_descends (prefixWord ++ tailWord_869959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_869994 : List Nat := [3, 1, 3, 2, 1, 10]
def baseStart_869994 : Nat := 118140960795 + 869994 * 2 ^ 59
def prefixEnd_869994 : Nat := 4983230072969 + 3 ^ 40 * 869994 * 2
def baseEnd_869994 : Nat := 14706998799268292285563

theorem tailTrace_869994 : CollatzResearch.WordTrace tailWord_869994 prefixEnd_869994 14706998799268292285563 := by
  unfold tailWord_869994
  simp only [CollatzResearch.WordTrace]
  refine ⟨7932822002541948997750259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21154192006778530660667357 7932822002541948997750259)
  ·
    refine ⟨11899233003812923496625389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7932822002541948997750259 11899233003812923496625389)
    ·
      refine ⟨4462212376429846311234521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11899233003812923496625389 4462212376429846311234521)
      ·
        refine ⟨3346659282322384733425891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462212376429846311234521 3346659282322384733425891)
        ·
          refine ⟨5019988923483577100138837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3346659282322384733425891 5019988923483577100138837)
          ·
            refine ⟨14706998799268292285563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5019988923483577100138837 14706998799268292285563)
            ·
              rfl

theorem cell20_869994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 10].length) (baseStart_869994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_869994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_869994 prefixEnd_869994 := by exact prefixLift 869994
  have htrace : WordTrace (prefixWord ++ tailWord_869994) baseStart_869994 baseEnd_869994 := by
    simpa [prefixWord, tailWord_869994, baseEnd_869994] using wordTrace_append hprefix tailTrace_869994
  have hstable : (prefixWord ++ tailWord_869994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_869994).length < 2 ^ (prefixWord ++ tailWord_869994).sum := by decide
  have hdescent : baseEnd_869994 < baseStart_869994 := by decide
  rcases family_descends (prefixWord ++ tailWord_869994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870000 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 2]
def baseStart_870000 : Nat := 118140960795 + 870000 * 2 ^ 59
def prefixEnd_870000 : Nat := 4983230072969 + 3 ^ 40 * 870000 * 2
def baseEnd_870000 : Nat := 397091706143734537510177

theorem tailTrace_870000 : CollatzResearch.WordTrace tailWord_870000 prefixEnd_870000 397091706143734537510177 := by
  unfold tailWord_870000
  simp only [CollatzResearch.WordTrace]
  refine ⟨15865753424073029507859727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 21154337898764039343812969 15865753424073029507859727)
  ·
    refine ⟨23798630136109544261789591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15865753424073029507859727 23798630136109544261789591)
    ·
      refine ⟨35697945204164316392684387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23798630136109544261789591 35697945204164316392684387)
      ·
        refine ⟨53546917806246474589026581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35697945204164316392684387 53546917806246474589026581)
        ·
          refine ⟨2510011772167803496360621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 53546917806246474589026581 2510011772167803496360621)
          ·
            refine ⟨941254414562926311135233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2510011772167803496360621 941254414562926311135233)
            ·
              refine ⟨705940810922194733351425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941254414562926311135233 705940810922194733351425)
              ·
                refine ⟨529455608191646050013569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 705940810922194733351425 529455608191646050013569)
                ·
                  refine ⟨397091706143734537510177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529455608191646050013569 397091706143734537510177)
                  ·
                    rfl

theorem cell20_870000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 2].length) (baseStart_870000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870000 prefixEnd_870000 := by exact prefixLift 870000
  have htrace : WordTrace (prefixWord ++ tailWord_870000) baseStart_870000 baseEnd_870000 := by
    simpa [prefixWord, tailWord_870000, baseEnd_870000] using wordTrace_append hprefix tailTrace_870000
  have hstable : (prefixWord ++ tailWord_870000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870000).length < 2 ^ (prefixWord ++ tailWord_870000).sum := by decide
  have hdescent : baseEnd_870000 < baseStart_870000 := by decide
  rcases family_descends (prefixWord ++ tailWord_870000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870001 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 5]
def baseStart_870001 : Nat := 118140960795 + 870001 * 2 ^ 59
def prefixEnd_870001 : Nat := 4983230072969 + 3 ^ 40 * 870001 * 2
def baseEnd_870001 : Nat := 397092162570982978476839

theorem tailTrace_870001 : CollatzResearch.WordTrace tailWord_870001 prefixEnd_870001 397092162570982978476839 := by
  unfold tailWord_870001
  simp only [CollatzResearch.WordTrace]
  refine ⟨31731543321142436186505857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21154362214094957457670571 31731543321142436186505857)
  ·
    refine ⟨23798657490856827139879393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31731543321142436186505857 23798657490856827139879393)
    ·
      refine ⟨17848993118142620354909545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23798657490856827139879393 17848993118142620354909545)
      ·
        refine ⟨13386744838606965266182159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17848993118142620354909545 13386744838606965266182159)
        ·
          refine ⟨20080117257910447899273239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13386744838606965266182159 20080117257910447899273239)
          ·
            refine ⟨30120175886865671848909859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20080117257910447899273239 30120175886865671848909859)
            ·
              refine ⟨45180263830298507773364789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30120175886865671848909859 45180263830298507773364789)
              ·
                refine ⟨4235649734090485103752949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45180263830298507773364789 4235649734090485103752949)
                ·
                  refine ⟨397092162570982978476839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4235649734090485103752949 397092162570982978476839)
                  ·
                    rfl

theorem cell20_870001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_870001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870001 prefixEnd_870001 := by exact prefixLift 870001
  have htrace : WordTrace (prefixWord ++ tailWord_870001) baseStart_870001 baseEnd_870001 := by
    simpa [prefixWord, tailWord_870001, baseEnd_870001] using wordTrace_append hprefix tailTrace_870001
  have hstable : (prefixWord ++ tailWord_870001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870001).length < 2 ^ (prefixWord ++ tailWord_870001).sum := by decide
  have hdescent : baseEnd_870001 < baseStart_870001 := by decide
  rcases family_descends (prefixWord ++ tailWord_870001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870063 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 4]
def baseStart_870063 : Nat := 118140960795 + 870063 * 2 ^ 59
def prefixEnd_870063 : Nat := 4983230072969 + 3 ^ 40 * 870063 * 2
def baseEnd_870063 : Nat := 397120461060386318409919

theorem tailTrace_870063 : CollatzResearch.WordTrace tailWord_870063 prefixEnd_870063 397120461060386318409919 := by
  unfold tailWord_870063
  simp only [CollatzResearch.WordTrace]
  refine ⟨31733804646917820775262843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21155869764611880516841895 31733804646917820775262843)
  ·
    refine ⟨47600706970376731162894265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31733804646917820775262843 47600706970376731162894265)
    ·
      refine ⟨35700530227782548372170699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47600706970376731162894265 35700530227782548372170699)
      ·
        refine ⟨53550795341673822558256049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35700530227782548372170699 53550795341673822558256049)
        ·
          refine ⟨40163096506255366918692037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53550795341673822558256049 40163096506255366918692037)
          ·
            refine ⟨7530580594922881297254757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40163096506255366918692037 7530580594922881297254757)
            ·
              refine ⟨1411983861548040243235267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7530580594922881297254757 1411983861548040243235267)
              ·
                refine ⟨2117975792322060364852901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1411983861548040243235267 2117975792322060364852901)
                ·
                  refine ⟨397120461060386318409919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2117975792322060364852901 397120461060386318409919)
                  ·
                    rfl

theorem cell20_870063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 4].length) (baseStart_870063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870063 prefixEnd_870063 := by exact prefixLift 870063
  have htrace : WordTrace (prefixWord ++ tailWord_870063) baseStart_870063 baseEnd_870063 := by
    simpa [prefixWord, tailWord_870063, baseEnd_870063] using wordTrace_append hprefix tailTrace_870063
  have hstable : (prefixWord ++ tailWord_870063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870063).length < 2 ^ (prefixWord ++ tailWord_870063).sum := by decide
  have hdescent : baseEnd_870063 < baseStart_870063 := by decide
  rcases family_descends (prefixWord ++ tailWord_870063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870093 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 2]
def baseStart_870093 : Nat := 118140960795 + 870093 * 2 ^ 59
def prefixEnd_870093 : Nat := 4983230072969 + 3 ^ 40 * 870093 * 2
def baseEnd_870093 : Nat := 397134153877839547409797

theorem tailTrace_870093 : CollatzResearch.WordTrace tailWord_870093 prefixEnd_870093 397134153877839547409797 := by
  unfold tailWord_870093
  simp only [CollatzResearch.WordTrace]
  refine ⟨31734898836809135898854933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21156599224539423932569955 31734898836809135898854933)
  ·
    refine ⟨1487573382975428245258825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31734898836809135898854933 1487573382975428245258825)
    ·
      refine ⟨1115680037231571183944119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1487573382975428245258825 1115680037231571183944119)
      ·
        refine ⟨1673520055847356775916179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1115680037231571183944119 1673520055847356775916179)
        ·
          refine ⟨2510280083771035163874269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1673520055847356775916179 2510280083771035163874269)
          ·
            refine ⟨941355031414138186452851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2510280083771035163874269 941355031414138186452851)
            ·
              refine ⟨1412032547121207279679277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941355031414138186452851 1412032547121207279679277)
              ·
                refine ⟨529512205170452729879729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412032547121207279679277 529512205170452729879729)
                ·
                  refine ⟨397134153877839547409797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529512205170452729879729 397134153877839547409797)
                  ·
                    rfl

theorem cell20_870093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_870093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870093 prefixEnd_870093 := by exact prefixLift 870093
  have htrace : WordTrace (prefixWord ++ tailWord_870093) baseStart_870093 baseEnd_870093 := by
    simpa [prefixWord, tailWord_870093, baseEnd_870093] using wordTrace_append hprefix tailTrace_870093
  have hstable : (prefixWord ++ tailWord_870093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870093).length < 2 ^ (prefixWord ++ tailWord_870093).sum := by decide
  have hdescent : baseEnd_870093 < baseStart_870093 := by decide
  rcases family_descends (prefixWord ++ tailWord_870093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870097 : List Nat := [1, 2, 2, 1, 2, 6, 1, 3, 2]
def baseStart_870097 : Nat := 118140960795 + 870097 * 2 ^ 59
def prefixEnd_870097 : Nat := 4983230072969 + 3 ^ 40 * 870097 * 2
def baseEnd_870097 : Nat := 397135979586833311276447

theorem tailTrace_870097 : CollatzResearch.WordTrace tailWord_870097 prefixEnd_870097 397135979586833311276447 := by
  unfold tailWord_870097
  simp only [CollatzResearch.WordTrace]
  refine ⟨31735044728794644582000545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21156696485863096388000363 31735044728794644582000545)
  ·
    refine ⟨23801283546595983436500409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31735044728794644582000545 23801283546595983436500409)
    ·
      refine ⟨17850962659946987577375307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23801283546595983436500409 17850962659946987577375307)
      ·
        refine ⟨26776443989920481366062961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17850962659946987577375307 26776443989920481366062961)
        ·
          refine ⟨20082332992440361024547221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26776443989920481366062961 20082332992440361024547221)
          ·
            refine ⟨941359359020641923025651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20082332992440361024547221 941359359020641923025651)
            ·
              refine ⟨1412039038530962884538477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941359359020641923025651 1412039038530962884538477)
              ·
                refine ⟨529514639449111081701929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1412039038530962884538477 529514639449111081701929)
                ·
                  refine ⟨397135979586833311276447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 529514639449111081701929 397135979586833311276447)
                  ·
                    rfl

theorem cell20_870097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_870097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870097 prefixEnd_870097 := by exact prefixLift 870097
  have htrace : WordTrace (prefixWord ++ tailWord_870097) baseStart_870097 baseEnd_870097 := by
    simpa [prefixWord, tailWord_870097, baseEnd_870097] using wordTrace_append hprefix tailTrace_870097
  have hstable : (prefixWord ++ tailWord_870097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870097).length < 2 ^ (prefixWord ++ tailWord_870097).sum := by decide
  have hdescent : baseEnd_870097 < baseStart_870097 := by decide
  rcases family_descends (prefixWord ++ tailWord_870097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870125 : List Nat := [1, 5, 1, 2, 1, 3, 2, 5]
def baseStart_870125 : Nat := 118140960795 + 870125 * 2 ^ 59
def prefixEnd_870125 : Nat := 4983230072969 + 3 ^ 40 * 870125 * 2
def baseEnd_870125 : Nat := 132382919849929886114333

theorem tailTrace_870125 : CollatzResearch.WordTrace tailWord_870125 prefixEnd_870125 132382919849929886114333 := by
  unfold tailWord_870125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31736065972693205364019829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21157377315128803576013219 31736065972693205364019829)
  ·
    refine ⟨2975256184939988002876859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31736065972693205364019829 2975256184939988002876859)
    ·
      refine ⟨4462884277409982004315289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975256184939988002876859 4462884277409982004315289)
      ·
        refine ⟨3347163208057486503236467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4462884277409982004315289 3347163208057486503236467)
        ·
          refine ⟨5020744812086229754854701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3347163208057486503236467 5020744812086229754854701)
          ·
            refine ⟨1882779304532336158070513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5020744812086229754854701 1882779304532336158070513)
            ·
              refine ⟨1412084478399252118552885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1882779304532336158070513 1412084478399252118552885)
              ·
                refine ⟨132382919849929886114333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1412084478399252118552885 132382919849929886114333)
                ·
                  rfl

theorem cell20_870125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 5].length) (baseStart_870125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870125 prefixEnd_870125 := by exact prefixLift 870125
  have htrace : WordTrace (prefixWord ++ tailWord_870125) baseStart_870125 baseEnd_870125 := by
    simpa [prefixWord, tailWord_870125, baseEnd_870125] using wordTrace_append hprefix tailTrace_870125
  have hstable : (prefixWord ++ tailWord_870125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870125).length < 2 ^ (prefixWord ++ tailWord_870125).sum := by decide
  have hdescent : baseEnd_870125 < baseStart_870125 := by decide
  rcases family_descends (prefixWord ++ tailWord_870125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870170 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 3]
def baseStart_870170 : Nat := 118140960795 + 870170 * 2 ^ 59
def prefixEnd_870170 : Nat := 4983230072969 + 3 ^ 40 * 870170 * 2
def baseEnd_870170 : Nat := 397169298775969501842815

theorem tailTrace_870170 : CollatzResearch.WordTrace tailWord_870170 prefixEnd_870170 397169298775969501842815 := by
  unfold tailWord_870170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7934426814382544512351991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21158471505020118699605309 7934426814382544512351991)
  ·
    refine ⟨11901640221573816768527987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7934426814382544512351991 11901640221573816768527987)
    ·
      refine ⟨17852460332360725152791981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11901640221573816768527987 17852460332360725152791981)
      ·
        refine ⟨6694672624635271932296993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17852460332360725152791981 6694672624635271932296993)
        ·
          refine ⟨5021004468476453949222745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6694672624635271932296993 5021004468476453949222745)
          ·
            refine ⟨3765753351357340461917059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5021004468476453949222745 3765753351357340461917059)
            ·
              refine ⟨5648630027036010692875589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3765753351357340461917059 5648630027036010692875589)
              ·
                refine ⟨1059118130069252004914173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5648630027036010692875589 1059118130069252004914173)
                ·
                  refine ⟨397169298775969501842815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059118130069252004914173 397169298775969501842815)
                  ·
                    rfl

theorem cell20_870170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_870170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870170 prefixEnd_870170 := by exact prefixLift 870170
  have htrace : WordTrace (prefixWord ++ tailWord_870170) baseStart_870170 baseEnd_870170 := by
    simpa [prefixWord, tailWord_870170, baseEnd_870170] using wordTrace_append hprefix tailTrace_870170
  have hstable : (prefixWord ++ tailWord_870170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870170).length < 2 ^ (prefixWord ++ tailWord_870170).sum := by decide
  have hdescent : baseEnd_870170 < baseStart_870170 := by decide
  rcases family_descends (prefixWord ++ tailWord_870170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870225 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 3]
def baseStart_870225 : Nat := 118140960795 + 870225 * 2 ^ 59
def prefixEnd_870225 : Nat := 4983230072969 + 3 ^ 40 * 870225 * 2
def baseEnd_870225 : Nat := 397194402274633755009257

theorem tailTrace_870225 : CollatzResearch.WordTrace tailWord_870225 prefixEnd_870225 397194402274633755009257 := by
  unfold tailWord_870225
  simp only [CollatzResearch.WordTrace]
  refine ⟨31739713272330922442660129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21159808848220614961773419 31739713272330922442660129)
  ·
    refine ⟨23804784954248191831995097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31739713272330922442660129 23804784954248191831995097)
    ·
      refine ⟨17853588715686143873996323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23804784954248191831995097 17853588715686143873996323)
      ·
        refine ⟨26780383073529215810994485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17853588715686143873996323 26780383073529215810994485)
        ·
          refine ⟨2510660913143363982280733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26780383073529215810994485 2510660913143363982280733)
          ·
            refine ⟨941497842428761493355275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2510660913143363982280733 941497842428761493355275)
            ·
              refine ⟨1412246763643142240032913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 941497842428761493355275 1412246763643142240032913)
              ·
                refine ⟨1059185072732356680024685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1412246763643142240032913 1059185072732356680024685)
                ·
                  refine ⟨397194402274633755009257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059185072732356680024685 397194402274633755009257)
                  ·
                    rfl

theorem cell20_870225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 3].length) (baseStart_870225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870225 prefixEnd_870225 := by exact prefixLift 870225
  have htrace : WordTrace (prefixWord ++ tailWord_870225) baseStart_870225 baseEnd_870225 := by
    simpa [prefixWord, tailWord_870225, baseEnd_870225] using wordTrace_append hprefix tailTrace_870225
  have hstable : (prefixWord ++ tailWord_870225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870225).length < 2 ^ (prefixWord ++ tailWord_870225).sum := by decide
  have hdescent : baseEnd_870225 < baseStart_870225 := by decide
  rcases family_descends (prefixWord ++ tailWord_870225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870242 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 3]
def baseStart_870242 : Nat := 118140960795 + 870242 * 2 ^ 59
def prefixEnd_870242 : Nat := 4983230072969 + 3 ^ 40 * 870242 * 2
def baseEnd_870242 : Nat := 397202161537857251442521

theorem tailTrace_870242 : CollatzResearch.WordTrace tailWord_870242 prefixEnd_870242 397202161537857251442521 := by
  unfold tailWord_870242
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935083328317333586507245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21160222208846222897352653 7935083328317333586507245)
  ·
    refine ⟨2975656248119000094940217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7935083328317333586507245 2975656248119000094940217)
    ·
      refine ⟨2231742186089250071205163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2975656248119000094940217 2231742186089250071205163)
      ·
        refine ⟨3347613279133875106807745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2231742186089250071205163 3347613279133875106807745)
        ·
          refine ⟨2510709959350406330105809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347613279133875106807745 2510709959350406330105809)
          ·
            refine ⟨1883032469512804747579357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2510709959350406330105809 1883032469512804747579357)
            ·
              refine ⟨706137176067301780342259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1883032469512804747579357 706137176067301780342259)
              ·
                refine ⟨1059205764100952670513389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706137176067301780342259 1059205764100952670513389)
                ·
                  refine ⟨397202161537857251442521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059205764100952670513389 397202161537857251442521)
                  ·
                    rfl

theorem cell20_870242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_870242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870242 prefixEnd_870242 := by exact prefixLift 870242
  have htrace : WordTrace (prefixWord ++ tailWord_870242) baseStart_870242 baseEnd_870242 := by
    simpa [prefixWord, tailWord_870242, baseEnd_870242] using wordTrace_append hprefix tailTrace_870242
  have hstable : (prefixWord ++ tailWord_870242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870242).length < 2 ^ (prefixWord ++ tailWord_870242).sum := by decide
  have hdescent : baseEnd_870242 < baseStart_870242 := by decide
  rcases family_descends (prefixWord ++ tailWord_870242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870253 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 4]
def baseStart_870253 : Nat := 118140960795 + 870253 * 2 ^ 59
def prefixEnd_870253 : Nat := 4983230072969 + 3 ^ 40 * 870253 * 2
def baseEnd_870253 : Nat := 397207182237590102075809

theorem tailTrace_870253 : CollatzResearch.WordTrace tailWord_870253 prefixEnd_870253 397207182237590102075809 := by
  unfold tailWord_870253
  simp only [CollatzResearch.WordTrace]
  refine ⟨31740734516229483224679413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21160489677486322149786275 31740734516229483224679413)
  ·
    refine ⟨2975693860896514052313695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31740734516229483224679413 2975693860896514052313695)
    ·
      refine ⟨4463540791344771078470543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975693860896514052313695 4463540791344771078470543)
      ·
        refine ⟨6695311187017156617705815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4463540791344771078470543 6695311187017156617705815)
        ·
          refine ⟨10042966780525734926558723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6695311187017156617705815 10042966780525734926558723)
          ·
            refine ⟨15064450170788602389838085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10042966780525734926558723 15064450170788602389838085)
            ·
              refine ⟨2824584407022862948094641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15064450170788602389838085 2824584407022862948094641)
              ·
                refine ⟨2118438305267147211070981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824584407022862948094641 2118438305267147211070981)
                ·
                  refine ⟨397207182237590102075809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118438305267147211070981 397207182237590102075809)
                  ·
                    rfl

theorem cell20_870253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_870253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870253 prefixEnd_870253 := by exact prefixLift 870253
  have htrace : WordTrace (prefixWord ++ tailWord_870253) baseStart_870253 baseEnd_870253 := by
    simpa [prefixWord, tailWord_870253, baseEnd_870253] using wordTrace_append hprefix tailTrace_870253
  have hstable : (prefixWord ++ tailWord_870253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870253).length < 2 ^ (prefixWord ++ tailWord_870253).sum := by decide
  have hdescent : baseEnd_870253 < baseStart_870253 := by decide
  rcases family_descends (prefixWord ++ tailWord_870253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870298 : List Nat := [3, 1, 1, 4, 2, 1, 1, 7]
def baseStart_870298 : Nat := 118140960795 + 870298 * 2 ^ 59
def prefixEnd_870298 : Nat := 4983230072969 + 3 ^ 40 * 870298 * 2
def baseEnd_870298 : Nat := 132409240487923315191875

theorem tailTrace_870298 : CollatzResearch.WordTrace tailWord_870298 prefixEnd_870298 132409240487923315191875 := by
  unfold tailWord_870298
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935593950266613977516887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 21161583867377637273378365 7935593950266613977516887)
  ·
    refine ⟨11903390925399920966275331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7935593950266613977516887 11903390925399920966275331)
    ·
      refine ⟨17855086388099881449412997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11903390925399920966275331 17855086388099881449412997)
      ·
        refine ⟨3347828697768727771764937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17855086388099881449412997 3347828697768727771764937)
        ·
          refine ⟨2510871523326545828823703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3347828697768727771764937 2510871523326545828823703)
          ·
            refine ⟨3766307284989818743235555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2510871523326545828823703 3766307284989818743235555)
            ·
              refine ⟨5649460927484728114853333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3766307284989818743235555 5649460927484728114853333)
              ·
                refine ⟨132409240487923315191875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5649460927484728114853333 132409240487923315191875)
                ·
                  rfl

theorem cell20_870298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 7].length) (baseStart_870298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870298 prefixEnd_870298 := by exact prefixLift 870298
  have htrace : WordTrace (prefixWord ++ tailWord_870298) baseStart_870298 baseEnd_870298 := by
    simpa [prefixWord, tailWord_870298, baseEnd_870298] using wordTrace_append hprefix tailTrace_870298
  have hstable : (prefixWord ++ tailWord_870298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870298).length < 2 ^ (prefixWord ++ tailWord_870298).sum := by decide
  have hdescent : baseEnd_870298 < baseStart_870298 := by decide
  rcases family_descends (prefixWord ++ tailWord_870298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870301 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 3]
def baseStart_870301 : Nat := 118140960795 + 870301 * 2 ^ 59
def prefixEnd_870301 : Nat := 4983230072969 + 3 ^ 40 * 870301 * 2
def baseEnd_870301 : Nat := 397229090745515268475613

theorem tailTrace_870301 : CollatzResearch.WordTrace tailWord_870301 prefixEnd_870301 397229090745515268475613 := by
  unfold tailWord_870301
  simp only [CollatzResearch.WordTrace]
  refine ⟨31742485220055587422426757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21161656813370391614951171 31742485220055587422426757)
  ·
    refine ⟨5951715978760422641705017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31742485220055587422426757 5951715978760422641705017)
    ·
      refine ⟨4463786984070316981278763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5951715978760422641705017 4463786984070316981278763)
      ·
        refine ⟨6695680476105475471918145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4463786984070316981278763 6695680476105475471918145)
        ·
          refine ⟨5021760357079106603938609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6695680476105475471918145 5021760357079106603938609)
          ·
            refine ⟨3766320267809329952953957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5021760357079106603938609 3766320267809329952953957)
            ·
              refine ⟨706185050214249366178867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3766320267809329952953957 706185050214249366178867)
              ·
                refine ⟨1059277575321374049268301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 706185050214249366178867 1059277575321374049268301)
                ·
                  refine ⟨397229090745515268475613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059277575321374049268301 397229090745515268475613)
                  ·
                    rfl

theorem cell20_870301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 3].length) (baseStart_870301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870301 prefixEnd_870301 := by exact prefixLift 870301
  have htrace : WordTrace (prefixWord ++ tailWord_870301) baseStart_870301 baseEnd_870301 := by
    simpa [prefixWord, tailWord_870301, baseEnd_870301] using wordTrace_append hprefix tailTrace_870301
  have hstable : (prefixWord ++ tailWord_870301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870301).length < 2 ^ (prefixWord ++ tailWord_870301).sum := by decide
  have hdescent : baseEnd_870301 < baseStart_870301 := by decide
  rcases family_descends (prefixWord ++ tailWord_870301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870319 : List Nat := [1, 1, 2, 1, 2, 2, 3, 8]
def baseStart_870319 : Nat := 118140960795 + 870319 * 2 ^ 59
def prefixEnd_870319 : Nat := 4983230072969 + 3 ^ 40 * 870319 * 2
def baseEnd_870319 : Nat := 132412435478662401958513

theorem tailTrace_870319 : CollatzResearch.WordTrace tailWord_870319 prefixEnd_870319 132412435478662401958513 := by
  unfold tailWord_870319
  simp only [CollatzResearch.WordTrace]
  refine ⟨31743141733990376496582011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21162094489326917664388007 31743141733990376496582011)
  ·
    refine ⟨47614712600985564744873017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31743141733990376496582011 47614712600985564744873017)
    ·
      refine ⟨35711034450739173558654763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47614712600985564744873017 35711034450739173558654763)
      ·
        refine ⟨53566551676108760337982145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35711034450739173558654763 53566551676108760337982145)
        ·
          refine ⟨40174913757081570253486609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53566551676108760337982145 40174913757081570253486609)
          ·
            refine ⟨30131185317811177690114957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40174913757081570253486609 30131185317811177690114957)
            ·
              refine ⟨11299194494179191633793109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30131185317811177690114957 11299194494179191633793109)
              ·
                refine ⟨132412435478662401958513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11299194494179191633793109 132412435478662401958513)
                ·
                  rfl

theorem cell20_870319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 8].length) (baseStart_870319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870319 prefixEnd_870319 := by exact prefixLift 870319
  have htrace : WordTrace (prefixWord ++ tailWord_870319) baseStart_870319 baseEnd_870319 := by
    simpa [prefixWord, tailWord_870319, baseEnd_870319] using wordTrace_append hprefix tailTrace_870319
  have hstable : (prefixWord ++ tailWord_870319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870319).length < 2 ^ (prefixWord ++ tailWord_870319).sum := by decide
  have hdescent : baseEnd_870319 < baseStart_870319 := by decide
  rcases family_descends (prefixWord ++ tailWord_870319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870367 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 4]
def baseStart_870367 : Nat := 118140960795 + 870367 * 2 ^ 59
def prefixEnd_870367 : Nat := 4983230072969 + 3 ^ 40 * 870367 * 2
def baseEnd_870367 : Nat := 397259214943912372275343

theorem tailTrace_870367 : CollatzResearch.WordTrace tailWord_870367 prefixEnd_870367 397259214943912372275343 := by
  unfold tailWord_870367
  simp only [CollatzResearch.WordTrace]
  refine ⟨31744892437816480694329355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21163261625210987129552903 31744892437816480694329355)
  ·
    refine ⟨47617338656724721041494033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31744892437816480694329355 47617338656724721041494033)
    ·
      refine ⟨35713003992543540781120525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47617338656724721041494033 35713003992543540781120525)
      ·
        refine ⟨13392376497203827792920197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35713003992543540781120525 13392376497203827792920197)
        ·
          refine ⟨2511070593225717711172537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13392376497203827792920197 2511070593225717711172537)
          ·
            refine ⟨1883302944919288283379403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2511070593225717711172537 1883302944919288283379403)
            ·
              refine ⟨2824954417378932425069105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1883302944919288283379403 2824954417378932425069105)
              ·
                refine ⟨2118715813034199318801829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2824954417378932425069105 2118715813034199318801829)
                ·
                  refine ⟨397259214943912372275343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118715813034199318801829 397259214943912372275343)
                  ·
                    rfl

theorem cell20_870367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_870367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870367 prefixEnd_870367 := by exact prefixLift 870367
  have htrace : WordTrace (prefixWord ++ tailWord_870367) baseStart_870367 baseEnd_870367 := by
    simpa [prefixWord, tailWord_870367, baseEnd_870367] using wordTrace_append hprefix tailTrace_870367
  have hstable : (prefixWord ++ tailWord_870367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870367).length < 2 ^ (prefixWord ++ tailWord_870367).sum := by decide
  have hdescent : baseEnd_870367 < baseStart_870367 := by decide
  rcases family_descends (prefixWord ++ tailWord_870367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870405 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 4]
def baseStart_870405 : Nat := 118140960795 + 870405 * 2 ^ 59
def prefixEnd_870405 : Nat := 4983230072969 + 3 ^ 40 * 870405 * 2
def baseEnd_870405 : Nat := 397276559179353129008521

theorem tailTrace_870405 : CollatzResearch.WordTrace tailWord_870405 prefixEnd_870405 397276559179353129008521 := by
  unfold tailWord_870405
  simp only [CollatzResearch.WordTrace]
  refine ⟨31746278411678813184212669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21164185607785875456141779 31746278411678813184212669)
  ·
    refine ⟨11904854404379554944079751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31746278411678813184212669 11904854404379554944079751)
    ·
      refine ⟨17857281606569332416119627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11904854404379554944079751 17857281606569332416119627)
      ·
        refine ⟨26785922409853998624179441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17857281606569332416119627 26785922409853998624179441)
        ·
          refine ⟨20089441807390498968134581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26785922409853998624179441 20089441807390498968134581)
          ·
            refine ⟨1883385169442859278262617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 20089441807390498968134581 1883385169442859278262617)
            ·
              refine ⟨1412538877082144458696963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1883385169442859278262617 1412538877082144458696963)
              ·
                refine ⟨2118808315623216688045445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1412538877082144458696963 2118808315623216688045445)
                ·
                  refine ⟨397276559179353129008521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2118808315623216688045445 397276559179353129008521)
                  ·
                    rfl

theorem cell20_870405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_870405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870405 prefixEnd_870405 := by exact prefixLift 870405
  have htrace : WordTrace (prefixWord ++ tailWord_870405) baseStart_870405 baseEnd_870405 := by
    simpa [prefixWord, tailWord_870405, baseEnd_870405] using wordTrace_append hprefix tailTrace_870405
  have hstable : (prefixWord ++ tailWord_870405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870405).length < 2 ^ (prefixWord ++ tailWord_870405).sum := by decide
  have hdescent : baseEnd_870405 < baseStart_870405 := by decide
  rcases family_descends (prefixWord ++ tailWord_870405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_870419 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 3]
def baseStart_870419 : Nat := 118140960795 + 870419 * 2 ^ 59
def prefixEnd_870419 : Nat := 4983230072969 + 3 ^ 40 * 870419 * 2
def baseEnd_870419 : Nat := 397282949160831302541797

theorem tailTrace_870419 : CollatzResearch.WordTrace tailWord_870419 prefixEnd_870419 397282949160831302541797 := by
  unfold tailWord_870419
  simp only [CollatzResearch.WordTrace]
  refine ⟨31746789033628093575222311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 21164526022418729050148207 31746789033628093575222311)
  ·
    refine ⟨47620183550442140362833467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31746789033628093575222311 47620183550442140362833467)
    ·
      refine ⟨71430275325663210544250201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47620183550442140362833467 71430275325663210544250201)
      ·
        refine ⟨53572706494247407908187651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71430275325663210544250201 53572706494247407908187651)
        ·
          refine ⟨80359059741371111862281477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53572706494247407908187651 80359059741371111862281477)
          ·
            refine ⟨15067323701507083474177777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80359059741371111862281477 15067323701507083474177777)
            ·
              refine ⟨11300492776130312605633333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15067323701507083474177777 11300492776130312605633333)
              ·
                refine ⟨1059421197762216806778125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11300492776130312605633333 1059421197762216806778125)
                ·
                  refine ⟨397282949160831302541797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1059421197762216806778125 397282949160831302541797)
                  ·
                    rfl

theorem cell20_870419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 3].length) (baseStart_870419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_870419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_870419 prefixEnd_870419 := by exact prefixLift 870419
  have htrace : WordTrace (prefixWord ++ tailWord_870419) baseStart_870419 baseEnd_870419 := by
    simpa [prefixWord, tailWord_870419, baseEnd_870419] using wordTrace_append hprefix tailTrace_870419
  have hstable : (prefixWord ++ tailWord_870419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_870419).length < 2 ^ (prefixWord ++ tailWord_870419).sum := by decide
  have hdescent : baseEnd_870419 < baseStart_870419 := by decide
  rcases family_descends (prefixWord ++ tailWord_870419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
