import V185TrunkScan23Chunk0681

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4032726 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_4032726 : Nat := 118140960795 + 4032726 * 2 ^ 59
def prefixEnd_4032726 : Nat := 4983230072969 + 3 ^ 40 * 4032726 * 2
def baseEnd_4032726 : Nat := 2070726785883494174678837

theorem tailTrace_4032726 : CollatzResearch.WordTrace tailWord_4032726 prefixEnd_4032726 2070726785883494174678837 := by
  unfold tailWord_4032726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9192850049258119475808377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98057067192086607741956021 9192850049258119475808377)
  ·
    refine ⟨6894637536943589606856283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9192850049258119475808377 6894637536943589606856283)
    ·
      refine ⟨10341956305415384410284425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894637536943589606856283 10341956305415384410284425)
      ·
        refine ⟨7756467229061538307713319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10341956305415384410284425 7756467229061538307713319)
        ·
          refine ⟨11634700843592307461569979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756467229061538307713319 11634700843592307461569979)
          ·
            refine ⟨17452051265388461192354969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11634700843592307461569979 17452051265388461192354969)
            ·
              refine ⟨13089038449041345894266227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17452051265388461192354969 13089038449041345894266227)
              ·
                refine ⟨19633557673562018841399341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13089038449041345894266227 19633557673562018841399341)
                ·
                  refine ⟨7362584127585757065524753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19633557673562018841399341 7362584127585757065524753)
                  ·
                    refine ⟨5521938095689317799143565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7362584127585757065524753 5521938095689317799143565)
                    ·
                      refine ⟨2070726785883494174678837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521938095689317799143565 2070726785883494174678837)
                      ·
                        rfl

theorem cell23_4032726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_4032726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032726 prefixEnd_4032726 := by exact prefixLift 4032726
  have htrace : WordTrace (prefixWord ++ tailWord_4032726) baseStart_4032726 baseEnd_4032726 := by
    simpa [prefixWord, tailWord_4032726, baseEnd_4032726] using wordTrace_append hprefix tailTrace_4032726
  have hstable : (prefixWord ++ tailWord_4032726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032726).length < 2 ^ (prefixWord ++ tailWord_4032726).sum := by decide
  have hdescent : baseEnd_4032726 < baseStart_4032726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032735 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5]
def baseStart_4032735 : Nat := 118140960795 + 4032735 * 2 ^ 59
def prefixEnd_4032735 : Nat := 4983230072969 + 3 ^ 40 * 4032735 * 2
def baseEnd_4032735 : Nat := 2070731407209384639466295

theorem tailTrace_4032735 : CollatzResearch.WordTrace tailWord_4032735 prefixEnd_4032735 2070731407209384639466295 := by
  unfold tailWord_4032735
  simp only [CollatzResearch.WordTrace]
  refine ⟨147085929045097306150011659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98057286030064870766674439 147085929045097306150011659)
  ·
    refine ⟨220628893567645959225017489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147085929045097306150011659 220628893567645959225017489)
    ·
      refine ⟨165471670175734469418763117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220628893567645959225017489 165471670175734469418763117)
      ·
        refine ⟨62051876315900426032036169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165471670175734469418763117 62051876315900426032036169)
        ·
          refine ⟨46538907236925319524027127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62051876315900426032036169 46538907236925319524027127)
          ·
            refine ⟨69808360855387979286040691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46538907236925319524027127 69808360855387979286040691)
            ·
              refine ⟨104712541283081968929061037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69808360855387979286040691 104712541283081968929061037)
              ·
                refine ⟨39267202981155738348397889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104712541283081968929061037 39267202981155738348397889)
                ·
                  refine ⟨29450402235866803761298417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39267202981155738348397889 29450402235866803761298417)
                  ·
                    refine ⟨22087801676900102820973813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29450402235866803761298417 22087801676900102820973813)
                    ·
                      refine ⟨2070731407209384639466295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22087801676900102820973813 2070731407209384639466295)
                      ·
                        rfl

theorem cell23_4032735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_4032735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032735 prefixEnd_4032735 := by exact prefixLift 4032735
  have htrace : WordTrace (prefixWord ++ tailWord_4032735) baseStart_4032735 baseEnd_4032735 := by
    simpa [prefixWord, tailWord_4032735, baseEnd_4032735] using wordTrace_append hprefix tailTrace_4032735
  have hstable : (prefixWord ++ tailWord_4032735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032735).length < 2 ^ (prefixWord ++ tailWord_4032735).sum := by decide
  have hdescent : baseEnd_4032735 < baseStart_4032735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032743 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4032743 : Nat := 118140960795 + 4032743 * 2 ^ 59
def prefixEnd_4032743 : Nat := 4983230072969 + 3 ^ 40 * 4032743 * 2
def baseEnd_4032743 : Nat := 2070735515054620608166259

theorem tailTrace_4032743 : CollatzResearch.WordTrace tailWord_4032743 prefixEnd_4032743 2070735515054620608166259 := by
  unfold tailWord_4032743
  simp only [CollatzResearch.WordTrace]
  refine ⟨147086220829068323516302883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98057480552712215677535255 147086220829068323516302883)
  ·
    refine ⟨220629331243602485274454325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147086220829068323516302883 220629331243602485274454325)
    ·
      refine ⟨20683999804087732994480093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220629331243602485274454325 20683999804087732994480093)
      ·
        refine ⟨7756499926532899872930035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20683999804087732994480093 7756499926532899872930035)
        ·
          refine ⟨11634749889799349809395053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756499926532899872930035 11634749889799349809395053)
          ·
            refine ⟨4363031208674756178523145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11634749889799349809395053 4363031208674756178523145)
            ·
              refine ⟨3272273406506067133892359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363031208674756178523145 3272273406506067133892359)
              ·
                refine ⟨4908410109759100700838539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272273406506067133892359 4908410109759100700838539)
                ·
                  refine ⟨7362615164638651051257809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908410109759100700838539 7362615164638651051257809)
                  ·
                    refine ⟨5521961373478988288443357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7362615164638651051257809 5521961373478988288443357)
                    ·
                      refine ⟨2070735515054620608166259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5521961373478988288443357 2070735515054620608166259)
                      ·
                        rfl

theorem cell23_4032743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4032743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032743 prefixEnd_4032743 := by exact prefixLift 4032743
  have htrace : WordTrace (prefixWord ++ tailWord_4032743) baseStart_4032743 baseEnd_4032743 := by
    simpa [prefixWord, tailWord_4032743, baseEnd_4032743] using wordTrace_append hprefix tailTrace_4032743
  have hstable : (prefixWord ++ tailWord_4032743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032743).length < 2 ^ (prefixWord ++ tailWord_4032743).sum := by decide
  have hdescent : baseEnd_4032743 < baseStart_4032743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032745 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 4]
def baseStart_4032745 : Nat := 118140960795 + 4032745 * 2 ^ 59
def prefixEnd_4032745 : Nat := 4983230072969 + 3 ^ 40 * 4032745 * 2
def baseEnd_4032745 : Nat := 2070736542015929600341249

theorem tailTrace_4032745 : CollatzResearch.WordTrace tailWord_4032745 prefixEnd_4032745 2070736542015929600341249 := by
  unfold tailWord_4032745
  simp only [CollatzResearch.WordTrace]
  refine ⟨147086293775061077857875689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98057529183374051905250459 147086293775061077857875689)
  ·
    refine ⟨110314720331295808393406767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147086293775061077857875689 110314720331295808393406767)
    ·
      refine ⟨165472080496943712590110151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110314720331295808393406767 165472080496943712590110151)
      ·
        refine ⟨248208120745415568885165227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165472080496943712590110151 248208120745415568885165227)
        ·
          refine ⟨372312181118123353327747841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248208120745415568885165227 372312181118123353327747841)
          ·
            refine ⟨279234135838592514995810881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372312181118123353327747841 279234135838592514995810881)
            ·
              refine ⟨209425601878944386246858161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279234135838592514995810881 209425601878944386246858161)
              ·
                refine ⟨157069201409208289685143621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209425601878944386246858161 157069201409208289685143621)
                ·
                  refine ⟨29450475264226554315964429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157069201409208289685143621 29450475264226554315964429)
                  ·
                    refine ⟨11043928224084957868486661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29450475264226554315964429 11043928224084957868486661)
                    ·
                      refine ⟨2070736542015929600341249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11043928224084957868486661 2070736542015929600341249)
                      ·
                        rfl

theorem cell23_4032745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_4032745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032745 prefixEnd_4032745 := by exact prefixLift 4032745
  have htrace : WordTrace (prefixWord ++ tailWord_4032745) baseStart_4032745 baseEnd_4032745 := by
    simpa [prefixWord, tailWord_4032745, baseEnd_4032745] using wordTrace_append hprefix tailTrace_4032745
  have hstable : (prefixWord ++ tailWord_4032745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032745).length < 2 ^ (prefixWord ++ tailWord_4032745).sum := by decide
  have hdescent : baseEnd_4032745 < baseStart_4032745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032755 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 4, 6]
def baseStart_4032755 : Nat := 118140960795 + 4032755 * 2 ^ 59
def prefixEnd_4032755 : Nat := 4983230072969 + 3 ^ 40 * 4032755 * 2
def baseEnd_4032755 : Nat := 690247225607491520405401

theorem tailTrace_4032755 : CollatzResearch.WordTrace tailWord_4032755 prefixEnd_4032755 690247225607491520405401 := by
  unfold tailWord_4032755
  simp only [CollatzResearch.WordTrace]
  refine ⟨147086658505024849565739719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98057772336683233043826479 147086658505024849565739719)
  ·
    refine ⟨220629987757537274348609579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147086658505024849565739719 220629987757537274348609579)
    ·
      refine ⟨330944981636305911522914369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220629987757537274348609579 330944981636305911522914369)
      ·
        refine ⟨248208736227229433642185777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330944981636305911522914369 248208736227229433642185777)
        ·
          refine ⟨186156552170422075231639333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248208736227229433642185777 186156552170422075231639333)
          ·
            refine ⟨34904353531954139105932375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186156552170422075231639333 34904353531954139105932375)
            ·
              refine ⟨52356530297931208658898563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34904353531954139105932375 52356530297931208658898563)
              ·
                refine ⟨78534795446896812988347845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52356530297931208658898563 78534795446896812988347845)
                ·
                  refine ⟨14725274146293152435315221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78534795446896812988347845 14725274146293152435315221)
                  ·
                    refine ⟨690247225607491520405401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14725274146293152435315221 690247225607491520405401)
                    ·
                      rfl

theorem cell23_4032755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 4, 6].length) (baseStart_4032755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032755 prefixEnd_4032755 := by exact prefixLift 4032755
  have htrace : WordTrace (prefixWord ++ tailWord_4032755) baseStart_4032755 baseEnd_4032755 := by
    simpa [prefixWord, tailWord_4032755, baseEnd_4032755] using wordTrace_append hprefix tailTrace_4032755
  have hstable : (prefixWord ++ tailWord_4032755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032755).length < 2 ^ (prefixWord ++ tailWord_4032755).sum := by decide
  have hdescent : baseEnd_4032755 < baseStart_4032755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032782 : List Nat := [4, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4032782 : Nat := 118140960795 + 4032782 * 2 ^ 59
def prefixEnd_4032782 : Nat := 4983230072969 + 3 ^ 40 * 4032782 * 2
def baseEnd_4032782 : Nat := 2070755540800145955578579

theorem tailTrace_4032782 : CollatzResearch.WordTrace tailWord_4032782 prefixEnd_4032782 2070755540800145955578579 := by
  unfold tailWord_4032782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18385955409490879147121575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98058428850618022117981733 18385955409490879147121575)
  ·
    refine ⟨27578933114236318720682363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18385955409490879147121575 27578933114236318720682363)
    ·
      refine ⟨41368399671354478081023545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27578933114236318720682363 41368399671354478081023545)
      ·
        refine ⟨31026299753515858560767659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41368399671354478081023545 31026299753515858560767659)
        ·
          refine ⟨46539449630273787841151489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31026299753515858560767659 46539449630273787841151489)
          ·
            refine ⟨34904587222705340880863617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46539449630273787841151489 34904587222705340880863617)
            ·
              refine ⟨26178440417029005660647713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34904587222705340880863617 26178440417029005660647713)
              ·
                refine ⟨19633830312771754245485785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26178440417029005660647713 19633830312771754245485785)
                ·
                  refine ⟨14725372734578815684114339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19633830312771754245485785 14725372734578815684114339)
                  ·
                    refine ⟨22088059101868223526171509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14725372734578815684114339 22088059101868223526171509)
                    ·
                      refine ⟨2070755540800145955578579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22088059101868223526171509 2070755540800145955578579)
                      ·
                        rfl

theorem cell23_4032782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4032782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032782 prefixEnd_4032782 := by exact prefixLift 4032782
  have htrace : WordTrace (prefixWord ++ tailWord_4032782) baseStart_4032782 baseEnd_4032782 := by
    simpa [prefixWord, tailWord_4032782, baseEnd_4032782] using wordTrace_append hprefix tailTrace_4032782
  have hstable : (prefixWord ++ tailWord_4032782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032782).length < 2 ^ (prefixWord ++ tailWord_4032782).sum := by decide
  have hdescent : baseEnd_4032782 < baseStart_4032782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032812 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 3]
def baseStart_4032812 : Nat := 118140960795 + 4032812 * 2 ^ 59
def prefixEnd_4032812 : Nat := 4983230072969 + 3 ^ 40 * 4032812 * 2
def baseEnd_4032812 : Nat := 2070770945219780838203441

theorem tailTrace_4032812 : CollatzResearch.WordTrace tailWord_4032812 prefixEnd_4032812 2070770945219780838203441 := by
  unfold tailWord_4032812
  simp only [CollatzResearch.WordTrace]
  refine ⟨73544368732909174150282345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98059158310545565533709793 73544368732909174150282345)
  ·
    refine ⟨55158276549681880612711759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73544368732909174150282345 55158276549681880612711759)
    ·
      refine ⟨82737414824522820919067639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55158276549681880612711759 82737414824522820919067639)
      ·
        refine ⟨124106122236784231378601459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82737414824522820919067639 124106122236784231378601459)
        ·
          refine ⟨186159183355176347067902189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124106122236784231378601459 186159183355176347067902189)
          ·
            refine ⟨69809693758191130150463321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186159183355176347067902189 69809693758191130150463321)
            ·
              refine ⟨52357270318643347612847491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69809693758191130150463321 52357270318643347612847491)
              ·
                refine ⟨78535905477965021419271237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52357270318643347612847491 78535905477965021419271237)
                ·
                  refine ⟨14725482277118441516113357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78535905477965021419271237 14725482277118441516113357)
                  ·
                    refine ⟨5522055853919415568542509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14725482277118441516113357 5522055853919415568542509)
                    ·
                      refine ⟨2070770945219780838203441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522055853919415568542509 2070770945219780838203441)
                      ·
                        rfl

theorem cell23_4032812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_4032812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032812 prefixEnd_4032812 := by exact prefixLift 4032812
  have htrace : WordTrace (prefixWord ++ tailWord_4032812) baseStart_4032812 baseEnd_4032812 := by
    simpa [prefixWord, tailWord_4032812, baseEnd_4032812] using wordTrace_append hprefix tailTrace_4032812
  have hstable : (prefixWord ++ tailWord_4032812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032812).length < 2 ^ (prefixWord ++ tailWord_4032812).sum := by decide
  have hdescent : baseEnd_4032812 < baseStart_4032812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032830 : List Nat := [4, 2, 1, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_4032830 : Nat := 118140960795 + 4032830 * 2 ^ 59
def prefixEnd_4032830 : Nat := 4983230072969 + 3 ^ 40 * 4032830 * 2
def baseEnd_4032830 : Nat := 2070780187871561767778359

theorem tailTrace_4032830 : CollatzResearch.WordTrace tailWord_4032830 prefixEnd_4032830 2070780187871561767778359 := by
  unfold tailWord_4032830
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386174247469142171839993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98059595986502091583146629 18386174247469142171839993)
  ·
    refine ⟨13789630685601856628879995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18386174247469142171839993 13789630685601856628879995)
    ·
      refine ⟨20684446028402784943319993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13789630685601856628879995 20684446028402784943319993)
      ·
        refine ⟨15513334521302088707489995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20684446028402784943319993 15513334521302088707489995)
        ·
          refine ⟨23270001781953133061234993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15513334521302088707489995 23270001781953133061234993)
          ·
            refine ⟨17452501336464849795926245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23270001781953133061234993 17452501336464849795926245)
            ·
              refine ⟨3272344000587159336736171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17452501336464849795926245 3272344000587159336736171)
              ·
                refine ⟨4908516000880739005104257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272344000587159336736171 4908516000880739005104257)
                ·
                  refine ⟨3681387000660554253828193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908516000880739005104257 3681387000660554253828193)
                  ·
                    refine ⟨2761040250495415690371145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3681387000660554253828193 2761040250495415690371145)
                    ·
                      refine ⟨2070780187871561767778359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761040250495415690371145 2070780187871561767778359)
                      ·
                        rfl

theorem cell23_4032830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_4032830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032830 prefixEnd_4032830 := by exact prefixLift 4032830
  have htrace : WordTrace (prefixWord ++ tailWord_4032830) baseStart_4032830 baseEnd_4032830 := by
    simpa [prefixWord, tailWord_4032830, baseEnd_4032830] using wordTrace_append hprefix tailTrace_4032830
  have hstable : (prefixWord ++ tailWord_4032830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032830).length < 2 ^ (prefixWord ++ tailWord_4032830).sum := by decide
  have hdescent : baseEnd_4032830 < baseStart_4032830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032849 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 2, 5]
def baseStart_4032849 : Nat := 118140960795 + 4032849 * 2 ^ 59
def prefixEnd_4032849 : Nat := 4983230072969 + 3 ^ 40 * 4032849 * 2
def baseEnd_4032849 : Nat := 690263314667999064480257

theorem tailTrace_4032849 : CollatzResearch.WordTrace tailWord_4032849 prefixEnd_4032849 690263314667999064480257 := by
  unfold tailWord_4032849
  simp only [CollatzResearch.WordTrace]
  refine ⟨147090086966684303619661601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98060057977789535746441067 147090086966684303619661601)
  ·
    refine ⟨110317565225013227714746201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147090086966684303619661601 110317565225013227714746201)
    ·
      refine ⟨82738173918759920786059651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110317565225013227714746201 82738173918759920786059651)
      ·
        refine ⟨124107260878139881179089477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82738173918759920786059651 124107260878139881179089477)
        ·
          refine ⟨23270111414651227721079277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124107260878139881179089477 23270111414651227721079277)
          ·
            refine ⟨8726291780494210395404729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23270111414651227721079277 8726291780494210395404729)
            ·
              refine ⟨6544718835370657796553547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726291780494210395404729 6544718835370657796553547)
              ·
                refine ⟨9817078253055986694830321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544718835370657796553547 9817078253055986694830321)
                ·
                  refine ⟨7362808689791990021122741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9817078253055986694830321 7362808689791990021122741)
                  ·
                    refine ⟨690263314667999064480257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7362808689791990021122741 690263314667999064480257)
                    ·
                      rfl

theorem cell23_4032849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_4032849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032849 prefixEnd_4032849 := by exact prefixLift 4032849
  have htrace : WordTrace (prefixWord ++ tailWord_4032849) baseStart_4032849 baseEnd_4032849 := by
    simpa [prefixWord, tailWord_4032849, baseEnd_4032849] using wordTrace_append hprefix tailTrace_4032849
  have hstable : (prefixWord ++ tailWord_4032849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032849).length < 2 ^ (prefixWord ++ tailWord_4032849).sum := by decide
  have hdescent : baseEnd_4032849 < baseStart_4032849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032869 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4032869 : Nat := 118140960795 + 4032869 * 2 ^ 59
def prefixEnd_4032869 : Nat := 4983230072969 + 3 ^ 40 * 4032869 * 2
def baseEnd_4032869 : Nat := 2070800213617087115190679

theorem tailTrace_4032869 : CollatzResearch.WordTrace tailWord_4032869 prefixEnd_4032869 2070800213617087115190679 := by
  unfold tailWord_4032869
  simp only [CollatzResearch.WordTrace]
  refine ⟨147090816426611847035389661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98060544284407898023593107 147090816426611847035389661)
  ·
    refine ⟨55159056159979442638271123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147090816426611847035389661 55159056159979442638271123)
    ·
      refine ⟨82738584239969163957406685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55159056159979442638271123 82738584239969163957406685)
      ·
        refine ⟨31026969089988436484027507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82738584239969163957406685 31026969089988436484027507)
        ·
          refine ⟨46540453634982654726041261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31026969089988436484027507 46540453634982654726041261)
          ·
            refine ⟨17452670113118495522265473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46540453634982654726041261 17452670113118495522265473)
            ·
              refine ⟨13089502584838871641699105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17452670113118495522265473 13089502584838871641699105)
              ·
                refine ⟨9817126938629153731274329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13089502584838871641699105 9817126938629153731274329)
                ·
                  refine ⟨7362845203971865298455747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9817126938629153731274329 7362845203971865298455747)
                  ·
                    refine ⟨11044267805957797947683621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362845203971865298455747 11044267805957797947683621)
                    ·
                      refine ⟨2070800213617087115190679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11044267805957797947683621 2070800213617087115190679)
                      ·
                        rfl

theorem cell23_4032869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4032869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032869 prefixEnd_4032869 := by exact prefixLift 4032869
  have htrace : WordTrace (prefixWord ++ tailWord_4032869) baseStart_4032869 baseEnd_4032869 := by
    simpa [prefixWord, tailWord_4032869, baseEnd_4032869] using wordTrace_append hprefix tailTrace_4032869
  have hstable : (prefixWord ++ tailWord_4032869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032869).length < 2 ^ (prefixWord ++ tailWord_4032869).sum := by decide
  have hdescent : baseEnd_4032869 < baseStart_4032869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032926 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_4032926 : Nat := 118140960795 + 4032926 * 2 ^ 59
def prefixEnd_4032926 : Nat := 4983230072969 + 3 ^ 40 * 4032926 * 2
def baseEnd_4032926 : Nat := 230092164668265932464213

theorem tailTrace_4032926 : CollatzResearch.WordTrace tailWord_4032926 prefixEnd_4032926 230092164668265932464213 := by
  unfold tailWord_4032926
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386611923425668221276829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98061930258270230513476421 18386611923425668221276829)
  ·
    refine ⟨6894979471284625582978811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18386611923425668221276829 6894979471284625582978811)
    ·
      refine ⟨10342469206926938374468217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894979471284625582978811 10342469206926938374468217)
      ·
        refine ⟨7756851905195203780851163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10342469206926938374468217 7756851905195203780851163)
        ·
          refine ⟨11635277857792805671276745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756851905195203780851163 11635277857792805671276745)
          ·
            refine ⟨8726458393344604253457559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635277857792805671276745 8726458393344604253457559)
            ·
              refine ⟨13089687590016906380186339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726458393344604253457559 13089687590016906380186339)
              ·
                refine ⟨19634531385025359570279509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13089687590016906380186339 19634531385025359570279509)
                ·
                  refine ⟨230092164668265932464213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19634531385025359570279509 230092164668265932464213)
                  ·
                    rfl

theorem cell23_4032926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_4032926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032926 prefixEnd_4032926 := by exact prefixLift 4032926
  have htrace : WordTrace (prefixWord ++ tailWord_4032926) baseStart_4032926 baseEnd_4032926 := by
    simpa [prefixWord, tailWord_4032926, baseEnd_4032926] using wordTrace_append hprefix tailTrace_4032926
  have hstable : (prefixWord ++ tailWord_4032926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032926).length < 2 ^ (prefixWord ++ tailWord_4032926).sum := by decide
  have hdescent : baseEnd_4032926 < baseStart_4032926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032956 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 1, 5]
def baseStart_4032956 : Nat := 118140960795 + 4032956 * 2 ^ 59
def prefixEnd_4032956 : Nat := 4983230072969 + 3 ^ 40 * 4032956 * 2
def baseEnd_4032956 : Nat := 690281628811342758267593

theorem tailTrace_4032956 : CollatzResearch.WordTrace tailWord_4032956 prefixEnd_4032956 690281628811342758267593 := by
  unfold tailWord_4032956
  simp only [CollatzResearch.WordTrace]
  refine ⟨73546994788648330446903361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98062659718197773929204481 73546994788648330446903361)
  ·
    refine ⟨55160246091486247835177521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73546994788648330446903361 55160246091486247835177521)
    ·
      refine ⟨41370184568614685876383141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55160246091486247835177521 41370184568614685876383141)
      ·
        refine ⟨7756909606615253601821839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41370184568614685876383141 7756909606615253601821839)
        ·
          refine ⟨11635364409922880402732759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7756909606615253601821839 11635364409922880402732759)
          ·
            refine ⟨17453046614884320604099139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635364409922880402732759 17453046614884320604099139)
            ·
              refine ⟨26179569922326480906148709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453046614884320604099139 26179569922326480906148709)
              ·
                refine ⟨4908669360436215169902883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26179569922326480906148709 4908669360436215169902883)
                ·
                  refine ⟨7363004040654322754854325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908669360436215169902883 7363004040654322754854325)
                  ·
                    refine ⟨690281628811342758267593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7363004040654322754854325 690281628811342758267593)
                    ·
                      rfl

theorem cell23_4032956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_4032956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032956 prefixEnd_4032956 := by exact prefixLift 4032956
  have htrace : WordTrace (prefixWord ++ tailWord_4032956) baseStart_4032956 baseEnd_4032956 := by
    simpa [prefixWord, tailWord_4032956, baseEnd_4032956] using wordTrace_append hprefix tailTrace_4032956
  have hstable : (prefixWord ++ tailWord_4032956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032956).length < 2 ^ (prefixWord ++ tailWord_4032956).sum := by decide
  have hdescent : baseEnd_4032956 < baseStart_4032956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032969 : List Nat := [1, 2, 1, 1, 2, 1, 5, 2, 4, 4]
def baseStart_4032969 : Nat := 118140960795 + 4032969 * 2 ^ 59
def prefixEnd_4032969 : Nat := 4983230072969 + 3 ^ 40 * 4032969 * 2
def baseEnd_4032969 : Nat := 690283853894178907980073

theorem tailTrace_4032969 : CollatzResearch.WordTrace tailWord_4032969 prefixEnd_4032969 690283853894178907980073 := by
  unfold tailWord_4032969
  simp only [CollatzResearch.WordTrace]
  refine ⟨147094463726249564114029961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98062975817499709409353307 147094463726249564114029961)
  ·
    refine ⟨110320847794687173085522471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147094463726249564114029961 110320847794687173085522471)
    ·
      refine ⟨165481271692030759628283707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110320847794687173085522471 165481271692030759628283707)
      ·
        refine ⟨248221907538046139442425561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165481271692030759628283707 248221907538046139442425561)
        ·
          refine ⟨186166430653534604581819171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248221907538046139442425561 186166430653534604581819171)
          ·
            refine ⟨279249645980301906872728757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186166430653534604581819171 279249645980301906872728757)
            ·
              refine ⟨26179654310653303769318321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279249645980301906872728757 26179654310653303769318321)
              ·
                refine ⟨19634740732989977826988741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26179654310653303769318321 19634740732989977826988741)
                ·
                  refine ⟨3681513887435620842560389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19634740732989977826988741 3681513887435620842560389)
                  ·
                    refine ⟨690283853894178907980073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681513887435620842560389 690283853894178907980073)
                    ·
                      rfl

theorem cell23_4032969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 4, 4].length) (baseStart_4032969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032969 prefixEnd_4032969 := by exact prefixLift 4032969
  have htrace : WordTrace (prefixWord ++ tailWord_4032969) baseStart_4032969 baseEnd_4032969 := by
    simpa [prefixWord, tailWord_4032969, baseEnd_4032969] using wordTrace_append hprefix tailTrace_4032969
  have hstable : (prefixWord ++ tailWord_4032969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032969).length < 2 ^ (prefixWord ++ tailWord_4032969).sum := by decide
  have hdescent : baseEnd_4032969 < baseStart_4032969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032986 : List Nat := [3, 1, 1, 2, 3, 1, 2, 4, 2, 4]
def baseStart_4032986 : Nat := 118140960795 + 4032986 * 2 ^ 59
def prefixEnd_4032986 : Nat := 4983230072969 + 3 ^ 40 * 4032986 * 2
def baseEnd_4032986 : Nat := 690286763617887719142547

theorem tailTrace_4032986 : CollatzResearch.WordTrace tailWord_4032986 prefixEnd_4032986 690286763617887719142547 := by
  unfold tailWord_4032986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36773770941796994004349703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98063389178125317344932541 36773770941796994004349703)
  ·
    refine ⟨55160656412695491006524555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36773770941796994004349703 55160656412695491006524555)
    ·
      refine ⟨82740984619043236509786833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55160656412695491006524555 82740984619043236509786833)
      ·
        refine ⟨62055738464282427382340125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82740984619043236509786833 62055738464282427382340125)
        ·
          refine ⟨23270901924105910268377547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62055738464282427382340125 23270901924105910268377547)
          ·
            refine ⟨34906352886158865402566321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270901924105910268377547 34906352886158865402566321)
            ·
              refine ⟨26179764664619149051924741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34906352886158865402566321 26179764664619149051924741)
              ·
                refine ⟨4908705874616090447235889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26179764664619149051924741 4908705874616090447235889)
                ·
                  refine ⟨3681529405962067835426917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908705874616090447235889 3681529405962067835426917)
                  ·
                    refine ⟨690286763617887719142547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681529405962067835426917 690286763617887719142547)
                    ·
                      rfl

theorem cell23_4032986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_4032986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032986 prefixEnd_4032986 := by exact prefixLift 4032986
  have htrace : WordTrace (prefixWord ++ tailWord_4032986) baseStart_4032986 baseEnd_4032986 := by
    simpa [prefixWord, tailWord_4032986, baseEnd_4032986] using wordTrace_append hprefix tailTrace_4032986
  have hstable : (prefixWord ++ tailWord_4032986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032986).length < 2 ^ (prefixWord ++ tailWord_4032986).sum := by decide
  have hdescent : baseEnd_4032986 < baseStart_4032986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032989 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4032989 : Nat := 118140960795 + 4032989 * 2 ^ 59
def prefixEnd_4032989 : Nat := 4983230072969 + 3 ^ 40 * 4032989 * 2
def baseEnd_4032989 : Nat := 2070861831295626645690127

theorem tailTrace_4032989 : CollatzResearch.WordTrace tailWord_4032989 prefixEnd_4032989 2070861831295626645690127 := by
  unfold tailWord_4032989
  simp only [CollatzResearch.WordTrace]
  refine ⟨147095193186177107529758021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98063462124118071686505347 147095193186177107529758021)
  ·
    refine ⟨27580348722408207661829629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147095193186177107529758021 27580348722408207661829629)
    ·
      refine ⟨10342630770903077873186111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27580348722408207661829629 10342630770903077873186111)
      ·
        refine ⟨15513946156354616809779167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10342630770903077873186111 15513946156354616809779167)
        ·
          refine ⟨23270919234531925214668751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15513946156354616809779167 23270919234531925214668751)
          ·
            refine ⟨34906378851797887822003127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270919234531925214668751 34906378851797887822003127)
            ·
              refine ⟨52359568277696831733004691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34906378851797887822003127 52359568277696831733004691)
              ·
                refine ⟨78539352416545247599507037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52359568277696831733004691 78539352416545247599507037)
                ·
                  refine ⟨29452257156204467849815139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78539352416545247599507037 29452257156204467849815139)
                  ·
                    refine ⟨44178385734306701774722709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29452257156204467849815139 44178385734306701774722709)
                    ·
                      refine ⟨2070861831295626645690127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44178385734306701774722709 2070861831295626645690127)
                      ·
                        rfl

theorem cell23_4032989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4032989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032989 prefixEnd_4032989 := by exact prefixLift 4032989
  have htrace : WordTrace (prefixWord ++ tailWord_4032989) baseStart_4032989 baseEnd_4032989 := by
    simpa [prefixWord, tailWord_4032989, baseEnd_4032989] using wordTrace_append hprefix tailTrace_4032989
  have hstable : (prefixWord ++ tailWord_4032989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032989).length < 2 ^ (prefixWord ++ tailWord_4032989).sum := by decide
  have hdescent : baseEnd_4032989 < baseStart_4032989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4032999 : List Nat := [1, 1, 5, 2, 1, 1, 4, 8]
def baseStart_4032999 : Nat := 118140960795 + 4032999 * 2 ^ 59
def prefixEnd_4032999 : Nat := 4983230072969 + 3 ^ 40 * 4032999 * 2
def baseEnd_4032999 : Nat := 76698776522302652095003

theorem tailTrace_4032999 : CollatzResearch.WordTrace tailWord_4032999 prefixEnd_4032999 76698776522302652095003 := by
  unfold tailWord_4032999
  simp only [CollatzResearch.WordTrace]
  refine ⟨147095557916140879237622051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98063705277427252825081367 147095557916140879237622051)
  ·
    refine ⟨220643336874211318856433077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147095557916140879237622051 220643336874211318856433077)
    ·
      refine ⟨20685312831957311142790601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220643336874211318856433077 20685312831957311142790601)
      ·
        refine ⟨15513984623967983357092951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20685312831957311142790601 15513984623967983357092951)
        ·
          refine ⟨23270976935951975035639427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15513984623967983357092951 23270976935951975035639427)
          ·
            refine ⟨34906465403927962553459141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23270976935951975035639427 34906465403927962553459141)
            ·
              refine ⟨6544962263236492978773589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34906465403927962553459141 6544962263236492978773589)
              ·
                refine ⟨76698776522302652095003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6544962263236492978773589 76698776522302652095003)
                ·
                  rfl

theorem cell23_4032999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 8].length) (baseStart_4032999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4032999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4032999 prefixEnd_4032999 := by exact prefixLift 4032999
  have htrace : WordTrace (prefixWord ++ tailWord_4032999) baseStart_4032999 baseEnd_4032999 := by
    simpa [prefixWord, tailWord_4032999, baseEnd_4032999] using wordTrace_append hprefix tailTrace_4032999
  have hstable : (prefixWord ++ tailWord_4032999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4032999).length < 2 ^ (prefixWord ++ tailWord_4032999).sum := by decide
  have hdescent : baseEnd_4032999 < baseStart_4032999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4032999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033010 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4033010 : Nat := 118140960795 + 4033010 * 2 ^ 59
def prefixEnd_4033010 : Nat := 4983230072969 + 3 ^ 40 * 4033010 * 2
def baseEnd_4033010 : Nat := 2070872614389371063527531

theorem tailTrace_4033010 : CollatzResearch.WordTrace tailWord_4033010 prefixEnd_4033010 2070872614389371063527531 := by
  unfold tailWord_4033010
  simp only [CollatzResearch.WordTrace]
  refine ⟨36773989779775257029068121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98063972746067352077514989 36773989779775257029068121)
  ·
    refine ⟨27580492334831442771801091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36773989779775257029068121 27580492334831442771801091)
    ·
      refine ⟨41370738502247164157701637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27580492334831442771801091 41370738502247164157701637)
      ·
        refine ⟨7757013469171343279569057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41370738502247164157701637 7757013469171343279569057)
        ·
          refine ⟨5817760101878507459676793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7757013469171343279569057 5817760101878507459676793)
          ·
            refine ⟨4363320076408880594757595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817760101878507459676793 4363320076408880594757595)
            ·
              refine ⟨6544980114613320892136393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363320076408880594757595 6544980114613320892136393)
              ·
                refine ⟨4908735085959990669102295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544980114613320892136393 4908735085959990669102295)
                ·
                  refine ⟨7363102628939986003653443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908735085959990669102295 7363102628939986003653443)
                  ·
                    refine ⟨11044653943409979005480165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363102628939986003653443 11044653943409979005480165)
                    ·
                      refine ⟨2070872614389371063527531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11044653943409979005480165 2070872614389371063527531)
                      ·
                        rfl

theorem cell23_4033010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4033010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033010 prefixEnd_4033010 := by exact prefixLift 4033010
  have htrace : WordTrace (prefixWord ++ tailWord_4033010) baseStart_4033010 baseEnd_4033010 := by
    simpa [prefixWord, tailWord_4033010, baseEnd_4033010] using wordTrace_append hprefix tailTrace_4033010
  have hstable : (prefixWord ++ tailWord_4033010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033010).length < 2 ^ (prefixWord ++ tailWord_4033010).sum := by decide
  have hdescent : baseEnd_4033010 < baseStart_4033010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033037 : List Nat := [1, 7, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4033037 : Nat := 118140960795 + 4033037 * 2 ^ 59
def prefixEnd_4033037 : Nat := 4983230072969 + 3 ^ 40 * 4033037 * 2
def baseEnd_4033037 : Nat := 690295492789014152629969

theorem tailTrace_4033037 : CollatzResearch.WordTrace tailWord_4033037 prefixEnd_4033037 690295492789014152629969 := by
  unfold tailWord_4033037
  simp only [CollatzResearch.WordTrace]
  refine ⟨147096943890003211727505365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98064629260002141151670243 147096943890003211727505365)
  ·
    refine ⟨3447584622421950274863407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 147096943890003211727505365 3447584622421950274863407)
    ·
      refine ⟨5171376933632925412295111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447584622421950274863407 5171376933632925412295111)
      ·
        refine ⟨7757065400449388118442667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171376933632925412295111 7757065400449388118442667)
        ·
          refine ⟨11635598100674082177664001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757065400449388118442667 11635598100674082177664001)
          ·
            refine ⟨8726698575505561633248001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635598100674082177664001 8726698575505561633248001)
            ·
              refine ⟨6545023931629171224936001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726698575505561633248001 6545023931629171224936001)
              ·
                refine ⟨4908767948721878418702001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545023931629171224936001 4908767948721878418702001)
                ·
                  refine ⟨3681575961541408814026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908767948721878418702001 3681575961541408814026501)
                  ·
                    refine ⟨690295492789014152629969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681575961541408814026501 690295492789014152629969)
                    ·
                      rfl

theorem cell23_4033037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4033037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033037 prefixEnd_4033037 := by exact prefixLift 4033037
  have htrace : WordTrace (prefixWord ++ tailWord_4033037) baseStart_4033037 baseEnd_4033037 := by
    simpa [prefixWord, tailWord_4033037, baseEnd_4033037] using wordTrace_append hprefix tailTrace_4033037
  have hstable : (prefixWord ++ tailWord_4033037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033037).length < 2 ^ (prefixWord ++ tailWord_4033037).sum := by decide
  have hdescent : baseEnd_4033037 < baseStart_4033037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033043 : List Nat := [1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 3]
def baseStart_4033043 : Nat := 118140960795 + 4033043 * 2 ^ 59
def prefixEnd_4033043 : Nat := 4983230072969 + 3 ^ 40 * 4033043 * 2
def baseEnd_4033043 : Nat := 2070889559250969434414879

theorem tailTrace_4033043 : CollatzResearch.WordTrace tailWord_4033043 prefixEnd_4033043 2070889559250969434414879 := by
  unfold tailWord_4033043
  simp only [CollatzResearch.WordTrace]
  refine ⟨147097162727981474752223783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98064775151987649834815855 147097162727981474752223783)
  ·
    refine ⟨220645744091972212128335675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147097162727981474752223783 220645744091972212128335675)
    ·
      refine ⟨330968616137958318192503513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220645744091972212128335675 330968616137958318192503513)
      ·
        refine ⟨248226462103468738644377635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330968616137958318192503513 248226462103468738644377635)
        ·
          refine ⟨372339693155203107966566453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248226462103468738644377635 372339693155203107966566453)
          ·
            refine ⟨34906846233300291371865605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 372339693155203107966566453 34906846233300291371865605)
            ·
              refine ⟨6545033668743804632224801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34906846233300291371865605 6545033668743804632224801)
              ·
                refine ⟨4908775251557853474168601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545033668743804632224801 4908775251557853474168601)
                ·
                  refine ⟨3681581438668390105626451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908775251557853474168601 3681581438668390105626451)
                  ·
                    refine ⟨5522372158002585158439677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681581438668390105626451 5522372158002585158439677)
                    ·
                      refine ⟨2070889559250969434414879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522372158002585158439677 2070889559250969434414879)
                      ·
                        rfl

theorem cell23_4033043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 3].length) (baseStart_4033043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033043 prefixEnd_4033043 := by exact prefixLift 4033043
  have htrace : WordTrace (prefixWord ++ tailWord_4033043) baseStart_4033043 baseEnd_4033043 := by
    simpa [prefixWord, tailWord_4033043, baseEnd_4033043] using wordTrace_append hprefix tailTrace_4033043
  have hstable : (prefixWord ++ tailWord_4033043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033043).length < 2 ^ (prefixWord ++ tailWord_4033043).sum := by decide
  have hdescent : baseEnd_4033043 < baseStart_4033043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033044 : List Nat := [2, 4, 3, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_4033044 : Nat := 118140960795 + 4033044 * 2 ^ 59
def prefixEnd_4033044 : Nat := 4983230072969 + 3 ^ 40 * 4033044 * 2
def baseEnd_4033044 : Nat := 2070890072731623930502375

theorem tailTrace_4033044 : CollatzResearch.WordTrace tailWord_4033044 prefixEnd_4033044 2070890072731623930502375 := by
  unfold tailWord_4033044
  simp only [CollatzResearch.WordTrace]
  refine ⟨73548599600488925961505093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98064799467318567948673457 73548599600488925961505093)
  ·
    refine ⟨13790362425091673617782205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73548599600488925961505093 13790362425091673617782205)
    ·
      refine ⟨5171385909409377606668327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13790362425091673617782205 5171385909409377606668327)
      ·
        refine ⟨7757078864114066410002491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171385909409377606668327 7757078864114066410002491)
        ·
          refine ⟨11635618296171099615003737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757078864114066410002491 11635618296171099615003737)
          ·
            refine ⟨8726713722128324711252803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635618296171099615003737 8726713722128324711252803)
            ·
              refine ⟨13090070583192487066879205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8726713722128324711252803 13090070583192487066879205)
              ·
                refine ⟨2454388234348591325039851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13090070583192487066879205 2454388234348591325039851)
                ·
                  refine ⟨3681582351522886987559777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454388234348591325039851 3681582351522886987559777)
                  ·
                    refine ⟨2761186763642165240669833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3681582351522886987559777 2761186763642165240669833)
                    ·
                      refine ⟨2070890072731623930502375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761186763642165240669833 2070890072731623930502375)
                      ·
                        rfl

theorem cell23_4033044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_4033044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033044 prefixEnd_4033044 := by exact prefixLift 4033044
  have htrace : WordTrace (prefixWord ++ tailWord_4033044) baseStart_4033044 baseEnd_4033044 := by
    simpa [prefixWord, tailWord_4033044, baseEnd_4033044] using wordTrace_append hprefix tailTrace_4033044
  have hstable : (prefixWord ++ tailWord_4033044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033044).length < 2 ^ (prefixWord ++ tailWord_4033044).sum := by decide
  have hdescent : baseEnd_4033044 < baseStart_4033044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033053 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 3, 3, 2]
def baseStart_4033053 : Nat := 118140960795 + 4033053 * 2 ^ 59
def prefixEnd_4033053 : Nat := 4983230072969 + 3 ^ 40 * 4033053 * 2
def baseEnd_4033053 : Nat := 2070894694057514395289833

theorem tailTrace_4033053 : CollatzResearch.WordTrace tailWord_4033053 prefixEnd_4033053 2070894694057514395289833 := by
  unfold tailWord_4033053
  simp only [CollatzResearch.WordTrace]
  refine ⟨147097527457945246460087813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98065018305296830973391875 147097527457945246460087813)
  ·
    refine ⟨27580786398364733711266465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147097527457945246460087813 27580786398364733711266465)
    ·
      refine ⟨20685589798773550283449849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27580786398364733711266465 20685589798773550283449849)
      ·
        refine ⟨15514192349080162712587387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20685589798773550283449849 15514192349080162712587387)
        ·
          refine ⟨23271288523620244068881081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15514192349080162712587387 23271288523620244068881081)
          ·
            refine ⟨17453466392715183051660811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23271288523620244068881081 17453466392715183051660811)
            ·
              refine ⟨26180199589072774577491217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453466392715183051660811 26180199589072774577491217)
              ·
                refine ⟨19635149691804580933118413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26180199589072774577491217 19635149691804580933118413)
                ·
                  refine ⟨7363181134426717849919405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19635149691804580933118413 7363181134426717849919405)
                  ·
                    refine ⟨2761192925410019193719777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7363181134426717849919405 2761192925410019193719777)
                    ·
                      refine ⟨2070894694057514395289833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761192925410019193719777 2070894694057514395289833)
                      ·
                        rfl

theorem cell23_4033053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_4033053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033053 prefixEnd_4033053 := by exact prefixLift 4033053
  have htrace : WordTrace (prefixWord ++ tailWord_4033053) baseStart_4033053 baseEnd_4033053 := by
    simpa [prefixWord, tailWord_4033053, baseEnd_4033053] using wordTrace_append hprefix tailTrace_4033053
  have hstable : (prefixWord ++ tailWord_4033053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033053).length < 2 ^ (prefixWord ++ tailWord_4033053).sum := by decide
  have hdescent : baseEnd_4033053 < baseStart_4033053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033059 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 1, 8]
def baseStart_4033059 : Nat := 118140960795 + 4033059 * 2 ^ 59
def prefixEnd_4033059 : Nat := 4983230072969 + 3 ^ 40 * 4033059 * 2
def baseEnd_4033059 : Nat := 690299258313813790604935

theorem tailTrace_4033059 : CollatzResearch.WordTrace tailWord_4033059 prefixEnd_4033059 690299258313813790604935 := by
  unfold tailWord_4033059
  simp only [CollatzResearch.WordTrace]
  refine ⟨147097746295923509484806231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98065164197282339656537487 147097746295923509484806231)
  ·
    refine ⟨220646619443885264227209347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147097746295923509484806231 220646619443885264227209347)
    ·
      refine ⟨330969929165827896340814021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220646619443885264227209347 330969929165827896340814021)
      ·
        refine ⟨62056861718592730563902629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330969929165827896340814021 62056861718592730563902629)
        ·
          refine ⟨11635661572236136980731743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62056861718592730563902629 11635661572236136980731743)
          ·
            refine ⟨17453492358354205471097615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11635661572236136980731743 17453492358354205471097615)
            ·
              refine ⟨26180238537531308206646423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17453492358354205471097615 26180238537531308206646423)
              ·
                refine ⟨39270357806296962309969635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26180238537531308206646423 39270357806296962309969635)
                ·
                  refine ⟨58905536709445443464954453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39270357806296962309969635 58905536709445443464954453)
                  ·
                    refine ⟨690299258313813790604935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58905536709445443464954453 690299258313813790604935)
                    ·
                      rfl

theorem cell23_4033059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 8].length) (baseStart_4033059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033059 prefixEnd_4033059 := by exact prefixLift 4033059
  have htrace : WordTrace (prefixWord ++ tailWord_4033059) baseStart_4033059 baseEnd_4033059 := by
    simpa [prefixWord, tailWord_4033059, baseEnd_4033059] using wordTrace_append hprefix tailTrace_4033059
  have hstable : (prefixWord ++ tailWord_4033059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033059).length < 2 ^ (prefixWord ++ tailWord_4033059).sum := by decide
  have hdescent : baseEnd_4033059 < baseStart_4033059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033060 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4033060 : Nat := 118140960795 + 4033060 * 2 ^ 59
def prefixEnd_4033060 : Nat := 4983230072969 + 3 ^ 40 * 4033060 * 2
def baseEnd_4033060 : Nat := 2070898288422095867902301

theorem tailTrace_4033060 : CollatzResearch.WordTrace tailWord_4033060 prefixEnd_4033060 2070898288422095867902301 := by
  unfold tailWord_4033060
  simp only [CollatzResearch.WordTrace]
  refine ⟨73548891384459943327796317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98065188512613257770395089 73548891384459943327796317)
  ·
    refine ⟨27580834269172478747923619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73548891384459943327796317 27580834269172478747923619)
    ·
      refine ⟨41371251403758718121885429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27580834269172478747923619 41371251403758718121885429)
      ·
        refine ⟨3878554819102379823926759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41371251403758718121885429 3878554819102379823926759)
        ·
          refine ⟨5817832228653569735890139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878554819102379823926759 5817832228653569735890139)
          ·
            refine ⟨8726748342980354603835209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817832228653569735890139 8726748342980354603835209)
            ·
              refine ⟨6545061257235265952876407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8726748342980354603835209 6545061257235265952876407)
              ·
                refine ⟨9817591885852898929314611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545061257235265952876407 9817591885852898929314611)
                ·
                  refine ⟨14726387828779348393971917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817591885852898929314611 14726387828779348393971917)
                  ·
                    refine ⟨5522395435792255647739469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14726387828779348393971917 5522395435792255647739469)
                    ·
                      refine ⟨2070898288422095867902301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522395435792255647739469 2070898288422095867902301)
                      ·
                        rfl

theorem cell23_4033060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4033060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033060 prefixEnd_4033060 := by exact prefixLift 4033060
  have htrace : WordTrace (prefixWord ++ tailWord_4033060) baseStart_4033060 baseEnd_4033060 := by
    simpa [prefixWord, tailWord_4033060, baseEnd_4033060] using wordTrace_append hprefix tailTrace_4033060
  have hstable : (prefixWord ++ tailWord_4033060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033060).length < 2 ^ (prefixWord ++ tailWord_4033060).sum := by decide
  have hdescent : baseEnd_4033060 < baseStart_4033060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033079 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_4033079 : Nat := 118140960795 + 4033079 * 2 ^ 59
def prefixEnd_4033079 : Nat := 4983230072969 + 3 ^ 40 * 4033079 * 2
def baseEnd_4033079 : Nat := 2070908044554531293564713

theorem tailTrace_4033079 : CollatzResearch.WordTrace tailWord_4033079 prefixEnd_4033079 2070908044554531293564713 := by
  unfold tailWord_4033079
  simp only [CollatzResearch.WordTrace]
  refine ⟨147098475755851052900534291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98065650503900701933689527 147098475755851052900534291)
  ·
    refine ⟨220647713633776579350801437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147098475755851052900534291 220647713633776579350801437)
    ·
      refine ⟨82742892612666217256550539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220647713633776579350801437 82742892612666217256550539)
      ·
        refine ⟨124114338918999325884825809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82742892612666217256550539 124114338918999325884825809)
        ·
          refine ⟨93085754189249494413619357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124114338918999325884825809 93085754189249494413619357)
          ·
            refine ⟨34907157820968560405107259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93085754189249494413619357 34907157820968560405107259)
            ·
              refine ⟨52360736731452840607660889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34907157820968560405107259 52360736731452840607660889)
              ·
                refine ⟨39270552548589630455745667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52360736731452840607660889 39270552548589630455745667)
                ·
                  refine ⟨58905828822884445683618501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39270552548589630455745667 58905828822884445683618501)
                  ·
                    refine ⟨11044842904290833565678469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58905828822884445683618501 11044842904290833565678469)
                    ·
                      refine ⟨2070908044554531293564713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11044842904290833565678469 2070908044554531293564713)
                      ·
                        rfl

theorem cell23_4033079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_4033079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033079 prefixEnd_4033079 := by exact prefixLift 4033079
  have htrace : WordTrace (prefixWord ++ tailWord_4033079) baseStart_4033079 baseEnd_4033079 := by
    simpa [prefixWord, tailWord_4033079, baseEnd_4033079] using wordTrace_append hprefix tailTrace_4033079
  have hstable : (prefixWord ++ tailWord_4033079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033079).length < 2 ^ (prefixWord ++ tailWord_4033079).sum := by decide
  have hdescent : baseEnd_4033079 < baseStart_4033079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033094 : List Nat := [6, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_4033094 : Nat := 118140960795 + 4033094 * 2 ^ 59
def prefixEnd_4033094 : Nat := 4983230072969 + 3 ^ 40 * 4033094 * 2
def baseEnd_4033094 : Nat := 2070915746764348734877145

theorem tailTrace_4033094 : CollatzResearch.WordTrace tailWord_4033094 prefixEnd_4033094 2070915746764348734877145 := by
  unfold tailWord_4033094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596844464087397201947823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98066015233864473641553557 4596844464087397201947823)
  ·
    refine ⟨6895266696131095802921735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4596844464087397201947823 6895266696131095802921735)
    ·
      refine ⟨10342900044196643704382603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895266696131095802921735 10342900044196643704382603)
      ·
        refine ⟨15514350066294965556573905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10342900044196643704382603 15514350066294965556573905)
        ·
          refine ⟨11635762549721224167430429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15514350066294965556573905 11635762549721224167430429)
          ·
            refine ⟨4363410956145459062786411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11635762549721224167430429 4363410956145459062786411)
            ·
              refine ⟨6545116434218188594179617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363410956145459062786411 6545116434218188594179617)
              ·
                refine ⟨4908837325663641445634713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545116434218188594179617 4908837325663641445634713)
                ·
                  refine ⟨3681627994247731084226035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4908837325663641445634713 3681627994247731084226035)
                  ·
                    refine ⟨5522441991371596626339053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681627994247731084226035 5522441991371596626339053)
                    ·
                      refine ⟨2070915746764348734877145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522441991371596626339053 2070915746764348734877145)
                      ·
                        rfl

theorem cell23_4033094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_4033094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033094 prefixEnd_4033094 := by exact prefixLift 4033094
  have htrace : WordTrace (prefixWord ++ tailWord_4033094) baseStart_4033094 baseEnd_4033094 := by
    simpa [prefixWord, tailWord_4033094, baseEnd_4033094] using wordTrace_append hprefix tailTrace_4033094
  have hstable : (prefixWord ++ tailWord_4033094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033094).length < 2 ^ (prefixWord ++ tailWord_4033094).sum := by decide
  have hdescent : baseEnd_4033094 < baseStart_4033094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033106 : List Nat := [3, 2, 2, 1, 2, 1, 4, 1, 7]
def baseStart_4033106 : Nat := 118140960795 + 4033106 * 2 ^ 59
def prefixEnd_4033106 : Nat := 4983230072969 + 3 ^ 40 * 4033106 * 2
def baseEnd_4033106 : Nat := 230102434281355854214121

theorem tailTrace_4033106 : CollatzResearch.WordTrace tailWord_4033106 prefixEnd_4033106 230102434281355854214121 := by
  unfold tailWord_4033106
  simp only [CollatzResearch.WordTrace]
  refine ⟨36774865131688309127941793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98066307017835491007844781 36774865131688309127941793)
  ·
    refine ⟨27581148848766231845956345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36774865131688309127941793 27581148848766231845956345)
    ·
      refine ⟨20685861636574673884467259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27581148848766231845956345 20685861636574673884467259)
      ·
        refine ⟨31028792454862010826700889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20685861636574673884467259 31028792454862010826700889)
        ·
          refine ⟨23271594341146508120025667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31028792454862010826700889 23271594341146508120025667)
          ·
            refine ⟨34907391511719762180038501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23271594341146508120025667 34907391511719762180038501)
            ·
              refine ⟨6545135908447455408757219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34907391511719762180038501 6545135908447455408757219)
              ·
                refine ⟨9817703862671183113135829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545135908447455408757219 9817703862671183113135829)
                ·
                  refine ⟨230102434281355854214121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9817703862671183113135829 230102434281355854214121)
                  ·
                    rfl

theorem cell23_4033106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_4033106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033106 prefixEnd_4033106 := by exact prefixLift 4033106
  have htrace : WordTrace (prefixWord ++ tailWord_4033106) baseStart_4033106 baseEnd_4033106 := by
    simpa [prefixWord, tailWord_4033106, baseEnd_4033106] using wordTrace_append hprefix tailTrace_4033106
  have hstable : (prefixWord ++ tailWord_4033106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033106).length < 2 ^ (prefixWord ++ tailWord_4033106).sum := by decide
  have hdescent : baseEnd_4033106 < baseStart_4033106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033129 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 5]
def baseStart_4033129 : Nat := 118140960795 + 4033129 * 2 ^ 59
def prefixEnd_4033129 : Nat := 4983230072969 + 3 ^ 40 * 4033129 * 2
def baseEnd_4033129 : Nat := 2070933718587256097939483

theorem tailTrace_4033129 : CollatzResearch.WordTrace tailWord_4033129 prefixEnd_4033129 2070933718587256097939483 := by
  unfold tailWord_4033129
  simp only [CollatzResearch.WordTrace]
  refine ⟨147100299405669911439854441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98066866270446607626569627 147100299405669911439854441)
  ·
    refine ⟨110325224554252433579890831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147100299405669911439854441 110325224554252433579890831)
    ·
      refine ⟨165487836831378650369836247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110325224554252433579890831 165487836831378650369836247)
      ·
        refine ⟨248231755247067975554754371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165487836831378650369836247 248231755247067975554754371)
        ·
          refine ⟨372347632870601963332131557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248231755247067975554754371 372347632870601963332131557)
          ·
            refine ⟨69815181163237868124774667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372347632870601963332131557 69815181163237868124774667)
            ·
              refine ⟨104722771744856802187162001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69815181163237868124774667 104722771744856802187162001)
              ·
                refine ⟨78542078808642601640371501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104722771744856802187162001 78542078808642601640371501)
                ·
                  refine ⟨29453279553240975615139313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78542078808642601640371501 29453279553240975615139313)
                  ·
                    refine ⟨22089959664930731711354485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29453279553240975615139313 22089959664930731711354485)
                    ·
                      refine ⟨2070933718587256097939483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22089959664930731711354485 2070933718587256097939483)
                      ·
                        rfl

theorem cell23_4033129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_4033129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033129 prefixEnd_4033129 := by exact prefixLift 4033129
  have htrace : WordTrace (prefixWord ++ tailWord_4033129) baseStart_4033129 baseEnd_4033129 := by
    simpa [prefixWord, tailWord_4033129, baseEnd_4033129] using wordTrace_append hprefix tailTrace_4033129
  have hstable : (prefixWord ++ tailWord_4033129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033129).length < 2 ^ (prefixWord ++ tailWord_4033129).sum := by decide
  have hdescent : baseEnd_4033129 < baseStart_4033129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033169 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 6]
def baseStart_4033169 : Nat := 118140960795 + 4033169 * 2 ^ 59
def prefixEnd_4033169 : Nat := 4983230072969 + 3 ^ 40 * 4033169 * 2
def baseEnd_4033169 : Nat := 2070954257813435941439299

theorem tailTrace_4033169 : CollatzResearch.WordTrace tailWord_4033169 prefixEnd_4033169 2070954257813435941439299 := by
  unfold tailWord_4033169
  simp only [CollatzResearch.WordTrace]
  refine ⟨147101758325524998271310561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98067838883683332180873707 147101758325524998271310561)
  ·
    refine ⟨110326318744143748703482921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147101758325524998271310561 110326318744143748703482921)
    ·
      refine ⟨82744739058107811527612191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110326318744143748703482921 82744739058107811527612191)
      ·
        refine ⟨124117108587161717291418287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82744739058107811527612191 124117108587161717291418287)
        ·
          refine ⟨186175662880742575937127431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124117108587161717291418287 186175662880742575937127431)
          ·
            refine ⟨279263494321113863905691147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186175662880742575937127431 279263494321113863905691147)
            ·
              refine ⟨418895241481670795858536721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279263494321113863905691147 418895241481670795858536721)
              ·
                refine ⟨314171431111253096893902541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418895241481670795858536721 314171431111253096893902541)
                ·
                  refine ⟨117814286666719911335213453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 314171431111253096893902541 117814286666719911335213453)
                  ·
                    refine ⟨44180357500019966750705045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117814286666719911335213453 44180357500019966750705045)
                    ·
                      refine ⟨2070954257813435941439299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44180357500019966750705045 2070954257813435941439299)
                      ·
                        rfl

theorem cell23_4033169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_4033169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033169 prefixEnd_4033169 := by exact prefixLift 4033169
  have htrace : WordTrace (prefixWord ++ tailWord_4033169) baseStart_4033169 baseEnd_4033169 := by
    simpa [prefixWord, tailWord_4033169, baseEnd_4033169] using wordTrace_append hprefix tailTrace_4033169
  have hstable : (prefixWord ++ tailWord_4033169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033169).length < 2 ^ (prefixWord ++ tailWord_4033169).sum := by decide
  have hdescent : baseEnd_4033169 < baseStart_4033169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033213 : List Nat := [1, 4, 1, 2, 1, 4, 2, 2, 6]
def baseStart_4033213 : Nat := 118140960795 + 4033213 * 2 ^ 59
def prefixEnd_4033213 : Nat := 4983230072969 + 3 ^ 40 * 4033213 * 2
def baseEnd_4033213 : Nat := 230108538995803752143233

theorem tailTrace_4033213 : CollatzResearch.WordTrace tailWord_4033213 prefixEnd_4033213 230108538995803752143233 := by
  unfold tailWord_4033213
  simp only [CollatzResearch.WordTrace]
  refine ⟨147103363137365593785912293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98068908758243729190608195 147103363137365593785912293)
  ·
    refine ⟨27581880588256048834858555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147103363137365593785912293 27581880588256048834858555)
    ·
      refine ⟨41372820882384073252287833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27581880588256048834858555 41372820882384073252287833)
      ·
        refine ⟨31029615661788054939215875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41372820882384073252287833 31029615661788054939215875)
        ·
          refine ⟨46544423492682082408823813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31029615661788054939215875 46544423492682082408823813)
          ·
            refine ⟨8727079404877890451654465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46544423492682082408823813 8727079404877890451654465)
            ·
              refine ⟨6545309553658417838740849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8727079404877890451654465 6545309553658417838740849)
              ·
                refine ⟨4908982165243813379055637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6545309553658417838740849 4908982165243813379055637)
                ·
                  refine ⟨230108538995803752143233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4908982165243813379055637 230108538995803752143233)
                  ·
                    rfl

theorem cell23_4033213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_4033213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033213 prefixEnd_4033213 := by exact prefixLift 4033213
  have htrace : WordTrace (prefixWord ++ tailWord_4033213) baseStart_4033213 baseEnd_4033213 := by
    simpa [prefixWord, tailWord_4033213, baseEnd_4033213] using wordTrace_append hprefix tailTrace_4033213
  have hstable : (prefixWord ++ tailWord_4033213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033213).length < 2 ^ (prefixWord ++ tailWord_4033213).sum := by decide
  have hdescent : baseEnd_4033213 < baseStart_4033213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033233 : List Nat := [1, 2, 2, 1, 2, 3, 2, 2, 1, 5, 2]
def baseStart_4033233 : Nat := 118140960795 + 4033233 * 2 ^ 59
def prefixEnd_4033233 : Nat := 4983230072969 + 3 ^ 40 * 4033233 * 2
def baseEnd_4033233 : Nat := 2070987120575323691039005

theorem tailTrace_4033233 : CollatzResearch.WordTrace tailWord_4033233 prefixEnd_4033233 2070987120575323691039005 := by
  unfold tailWord_4033233
  simp only [CollatzResearch.WordTrace]
  refine ⟨147104092597293137201640353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98069395064862091467760235 147104092597293137201640353)
  ·
    refine ⟨110328069447969852901230265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147104092597293137201640353 110328069447969852901230265)
    ·
      refine ⟨82746052085977389675922699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110328069447969852901230265 82746052085977389675922699)
      ·
        refine ⟨124119078128966084513884049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82746052085977389675922699 124119078128966084513884049)
        ·
          refine ⟨93089308596724563385413037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124119078128966084513884049 93089308596724563385413037)
          ·
            refine ⟨34908490723771711269529889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93089308596724563385413037 34908490723771711269529889)
            ·
              refine ⟨26181368042828783452147417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34908490723771711269529889 26181368042828783452147417)
              ·
                refine ⟨19636026032121587589110563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26181368042828783452147417 19636026032121587589110563)
                ·
                  refine ⟨29454039048182381383665845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19636026032121587589110563 29454039048182381383665845)
                  ·
                    refine ⟨2761316160767098254718673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29454039048182381383665845 2761316160767098254718673)
                    ·
                      refine ⟨2070987120575323691039005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761316160767098254718673 2070987120575323691039005)
                      ·
                        rfl

theorem cell23_4033233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 1, 5, 2].length) (baseStart_4033233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033233 prefixEnd_4033233 := by exact prefixLift 4033233
  have htrace : WordTrace (prefixWord ++ tailWord_4033233) baseStart_4033233 baseEnd_4033233 := by
    simpa [prefixWord, tailWord_4033233, baseEnd_4033233] using wordTrace_append hprefix tailTrace_4033233
  have hstable : (prefixWord ++ tailWord_4033233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033233).length < 2 ^ (prefixWord ++ tailWord_4033233).sum := by decide
  have hdescent : baseEnd_4033233 < baseStart_4033233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033240 : List Nat := [2, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_4033240 : Nat := 118140960795 + 4033240 * 2 ^ 59
def prefixEnd_4033240 : Nat := 4983230072969 + 3 ^ 40 * 4033240 * 2
def baseEnd_4033240 : Nat := 2070990714939905163651473

theorem tailTrace_4033240 : CollatzResearch.WordTrace tailWord_4033240 prefixEnd_4033240 2070990714939905163651473 := by
  unfold tailWord_4033240
  simp only [CollatzResearch.WordTrace]
  refine ⟨73552173954133888698572587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98069565272178518264763449 73552173954133888698572587)
  ·
    refine ⟨110328260931200833047858881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73552173954133888698572587 110328260931200833047858881)
    ·
      refine ⟨82746195698400624785894161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110328260931200833047858881 82746195698400624785894161)
      ·
        refine ⟨62059646773800468589420621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82746195698400624785894161 62059646773800468589420621)
        ·
          refine ⟨23272367540175175721032733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62059646773800468589420621 23272367540175175721032733)
          ·
            refine ⟨8727137827565690895387275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23272367540175175721032733 8727137827565690895387275)
            ·
              refine ⟨13090706741348536343080913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8727137827565690895387275 13090706741348536343080913)
              ·
                refine ⟨9818030056011402257310685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13090706741348536343080913 9818030056011402257310685)
                ·
                  refine ⟨3681761271004275846491507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9818030056011402257310685 3681761271004275846491507)
                  ·
                    refine ⟨5522641906506413769737261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681761271004275846491507 5522641906506413769737261)
                    ·
                      refine ⟨2070990714939905163651473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522641906506413769737261 2070990714939905163651473)
                      ·
                        rfl

theorem cell23_4033240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_4033240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033240 prefixEnd_4033240 := by exact prefixLift 4033240
  have htrace : WordTrace (prefixWord ++ tailWord_4033240) baseStart_4033240 baseEnd_4033240 := by
    simpa [prefixWord, tailWord_4033240, baseEnd_4033240] using wordTrace_append hprefix tailTrace_4033240
  have hstable : (prefixWord ++ tailWord_4033240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033240).length < 2 ^ (prefixWord ++ tailWord_4033240).sum := by decide
  have hdescent : baseEnd_4033240 < baseStart_4033240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033303 : List Nat := [1, 1, 3, 4, 3, 1, 1, 9]
def baseStart_4033303 : Nat := 118140960795 + 4033303 * 2 ^ 59
def prefixEnd_4033303 : Nat := 4983230072969 + 3 ^ 40 * 4033303 * 2
def baseEnd_4033303 : Nat := 76704557934116237672729

theorem tailTrace_4033303 : CollatzResearch.WordTrace tailWord_4033303 prefixEnd_4033303 76704557934116237672729 := by
  unfold tailWord_4033303
  simp only [CollatzResearch.WordTrace]
  refine ⟨147106645707039539156688563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98071097138026359437792375 147106645707039539156688563)
  ·
    refine ⟨220659968560559308735032845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147106645707039539156688563 220659968560559308735032845)
    ·
      refine ⟨82747488210209740775637317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220659968560559308735032845 82747488210209740775637317)
      ·
        refine ⟨15515154039414326395431997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82747488210209740775637317 15515154039414326395431997)
        ·
          refine ⟨5818182764780372398286999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15515154039414326395431997 5818182764780372398286999)
          ·
            refine ⟨8727274147170558597430499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818182764780372398286999 8727274147170558597430499)
            ·
              refine ⟨13090911220755837896145749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8727274147170558597430499 13090911220755837896145749)
              ·
                refine ⟨76704557934116237672729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13090911220755837896145749 76704557934116237672729)
                ·
                  rfl

theorem cell23_4033303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 9].length) (baseStart_4033303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033303 prefixEnd_4033303 := by exact prefixLift 4033303
  have htrace : WordTrace (prefixWord ++ tailWord_4033303) baseStart_4033303 baseEnd_4033303 := by
    simpa [prefixWord, tailWord_4033303, baseEnd_4033303] using wordTrace_append hprefix tailTrace_4033303
  have hstable : (prefixWord ++ tailWord_4033303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033303).length < 2 ^ (prefixWord ++ tailWord_4033303).sum := by decide
  have hdescent : baseEnd_4033303 < baseStart_4033303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033313 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4033313 : Nat := 118140960795 + 4033313 * 2 ^ 59
def prefixEnd_4033313 : Nat := 4983230072969 + 3 ^ 40 * 4033313 * 2
def baseEnd_4033313 : Nat := 2071028199027683378038637

theorem tailTrace_4033313 : CollatzResearch.WordTrace tailWord_4033313 prefixEnd_4033313 2071028199027683378038637 := by
  unfold tailWord_4033313
  simp only [CollatzResearch.WordTrace]
  refine ⟨147107010437003310864552593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98071340291335540576368395 147107010437003310864552593)
  ·
    refine ⟨110330257827752483148414445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147107010437003310864552593 110330257827752483148414445)
    ·
      refine ⟨41373846685407181180655417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110330257827752483148414445 41373846685407181180655417)
      ·
        refine ⟨31030385014055385885491563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41373846685407181180655417 31030385014055385885491563)
        ·
          refine ⟨46545577521083078828237345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31030385014055385885491563 46545577521083078828237345)
          ·
            refine ⟨34909183140812309121178009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46545577521083078828237345 34909183140812309121178009)
            ·
              refine ⟨26181887355609231840883507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34909183140812309121178009 26181887355609231840883507)
              ·
                refine ⟨39272831033413847761325261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26181887355609231840883507 39272831033413847761325261)
                ·
                  refine ⟨14727311637530192910496973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39272831033413847761325261 14727311637530192910496973)
                  ·
                    refine ⟨5522741864073822341436365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14727311637530192910496973 5522741864073822341436365)
                    ·
                      refine ⟨2071028199027683378038637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522741864073822341436365 2071028199027683378038637)
                      ·
                        rfl

theorem cell23_4033313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4033313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033313 prefixEnd_4033313 := by exact prefixLift 4033313
  have htrace : WordTrace (prefixWord ++ tailWord_4033313) baseStart_4033313 baseEnd_4033313 := by
    simpa [prefixWord, tailWord_4033313, baseEnd_4033313] using wordTrace_append hprefix tailTrace_4033313
  have hstable : (prefixWord ++ tailWord_4033313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033313).length < 2 ^ (prefixWord ++ tailWord_4033313).sum := by decide
  have hdescent : baseEnd_4033313 < baseStart_4033313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033330 : List Nat := [3, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_4033330 : Nat := 118140960795 + 4033330 * 2 ^ 59
def prefixEnd_4033330 : Nat := 4983230072969 + 3 ^ 40 * 4033330 * 2
def baseEnd_4033330 : Nat := 2071036928198809811526059

theorem tailTrace_4033330 : CollatzResearch.WordTrace tailWord_4033330 prefixEnd_4033330 2071036928198809811526059 := by
  unfold tailWord_4033330
  simp only [CollatzResearch.WordTrace]
  refine ⟨36776907619485430691980361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98071753651961148511947629 36776907619485430691980361)
  ·
    refine ⟨27582680714614073018985271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36776907619485430691980361 27582680714614073018985271)
    ·
      refine ⟨41374021071921109528477907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27582680714614073018985271 41374021071921109528477907)
      ·
        refine ⟨62061031607881664292716861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41374021071921109528477907 62061031607881664292716861)
        ·
          refine ⟨23272886852955624109768823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62061031607881664292716861 23272886852955624109768823)
          ·
            refine ⟨34909330279433436164653235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23272886852955624109768823 34909330279433436164653235)
            ·
              refine ⟨52363995419150154246979853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34909330279433436164653235 52363995419150154246979853)
              ·
                refine ⟨19636498282181307842617445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52363995419150154246979853 19636498282181307842617445)
                ·
                  refine ⟨3681843427908995220490771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19636498282181307842617445 3681843427908995220490771)
                  ·
                    refine ⟨5522765141863492830736157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3681843427908995220490771 5522765141863492830736157)
                    ·
                      refine ⟨2071036928198809811526059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522765141863492830736157 2071036928198809811526059)
                      ·
                        rfl

theorem cell23_4033330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_4033330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033330 prefixEnd_4033330 := by exact prefixLift 4033330
  have htrace : WordTrace (prefixWord ++ tailWord_4033330) baseStart_4033330 baseEnd_4033330 := by
    simpa [prefixWord, tailWord_4033330, baseEnd_4033330] using wordTrace_append hprefix tailTrace_4033330
  have hstable : (prefixWord ++ tailWord_4033330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033330).length < 2 ^ (prefixWord ++ tailWord_4033330).sum := by decide
  have hdescent : baseEnd_4033330 < baseStart_4033330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033331 : List Nat := [1, 1, 1, 2, 6, 2, 3, 2, 1, 2, 2]
def baseStart_4033331 : Nat := 118140960795 + 4033331 * 2 ^ 59
def prefixEnd_4033331 : Nat := 4983230072969 + 3 ^ 40 * 4033331 * 2
def baseEnd_4033331 : Nat := 2071037441679464307613555

theorem tailTrace_4033331 : CollatzResearch.WordTrace tailWord_4033331 prefixEnd_4033331 2071037441679464307613555 := by
  unfold tailWord_4033331
  simp only [CollatzResearch.WordTrace]
  refine ⟨147107666950938099938707847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98071777967292066625805231 147107666950938099938707847)
  ·
    refine ⟨220661500426407149908061771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147107666950938099938707847 220661500426407149908061771)
    ·
      refine ⟨330992250639610724862092657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220661500426407149908061771 330992250639610724862092657)
      ·
        refine ⟨248244187979708043646569493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330992250639610724862092657 248244187979708043646569493)
        ·
          refine ⟨11636446311548814545932945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248244187979708043646569493 11636446311548814545932945)
          ·
            refine ⟨8727334733661610909449709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11636446311548814545932945 8727334733661610909449709)
            ·
              refine ⟨3272750525123104091043641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8727334733661610909449709 3272750525123104091043641)
              ·
                refine ⟨2454562893842328068282731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272750525123104091043641 2454562893842328068282731)
                ·
                  refine ⟨3681844340763492102424097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454562893842328068282731 3681844340763492102424097)
                  ·
                    refine ⟨2761383255572619076818073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3681844340763492102424097 2761383255572619076818073)
                    ·
                      refine ⟨2071037441679464307613555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761383255572619076818073 2071037441679464307613555)
                      ·
                        rfl

theorem cell23_4033331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 2, 1, 2, 2].length) (baseStart_4033331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033331 prefixEnd_4033331 := by exact prefixLift 4033331
  have htrace : WordTrace (prefixWord ++ tailWord_4033331) baseStart_4033331 baseEnd_4033331 := by
    simpa [prefixWord, tailWord_4033331, baseEnd_4033331] using wordTrace_append hprefix tailTrace_4033331
  have hstable : (prefixWord ++ tailWord_4033331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033331).length < 2 ^ (prefixWord ++ tailWord_4033331).sum := by decide
  have hdescent : baseEnd_4033331 < baseStart_4033331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033340 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_4033340 : Nat := 118140960795 + 4033340 * 2 ^ 59
def prefixEnd_4033340 : Nat := 4983230072969 + 3 ^ 40 * 4033340 * 2
def baseEnd_4033340 : Nat := 2071042063005354772401013

theorem tailTrace_4033340 : CollatzResearch.WordTrace tailWord_4033340 prefixEnd_4033340 2071042063005354772401013 := by
  unfold tailWord_4033340
  simp only [CollatzResearch.WordTrace]
  refine ⟨73553997603952747237892737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98071996805270329650523649 73553997603952747237892737)
  ·
    refine ⟨55165498202964560428419553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73553997603952747237892737 55165498202964560428419553)
    ·
      refine ⟨41374123652223420321314665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55165498202964560428419553 41374123652223420321314665)
      ·
        refine ⟨31030592739167565240985999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41374123652223420321314665 31030592739167565240985999)
        ·
          refine ⟨46545889108751347861478999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31030592739167565240985999 46545889108751347861478999)
          ·
            refine ⟨69818833663127021792218499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46545889108751347861478999 69818833663127021792218499)
            ·
              refine ⟨104728250494690532688327749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69818833663127021792218499 104728250494690532688327749)
              ·
                refine ⟨19636546967754474879061453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104728250494690532688327749 19636546967754474879061453)
                ·
                  refine ⟨7363705112907928079648045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19636546967754474879061453 7363705112907928079648045)
                  ·
                    refine ⟨2761389417340473029868017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7363705112907928079648045 2761389417340473029868017)
                    ·
                      refine ⟨2071042063005354772401013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761389417340473029868017 2071042063005354772401013)
                      ·
                        rfl

theorem cell23_4033340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_4033340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033340 prefixEnd_4033340 := by exact prefixLift 4033340
  have htrace : WordTrace (prefixWord ++ tailWord_4033340) baseStart_4033340 baseEnd_4033340 := by
    simpa [prefixWord, tailWord_4033340, baseEnd_4033340] using wordTrace_append hprefix tailTrace_4033340
  have hstable : (prefixWord ++ tailWord_4033340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033340).length < 2 ^ (prefixWord ++ tailWord_4033340).sum := by decide
  have hdescent : baseEnd_4033340 < baseStart_4033340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033341 : List Nat := [1, 4, 1, 4, 3, 1, 2, 1, 2, 4]
def baseStart_4033341 : Nat := 118140960795 + 4033341 * 2 ^ 59
def prefixEnd_4033341 : Nat := 4983230072969 + 3 ^ 40 * 4033341 * 2
def baseEnd_4033341 : Nat := 690347525495336422829503

theorem tailTrace_4033341 : CollatzResearch.WordTrace tailWord_4033341 prefixEnd_4033341 690347525495336422829503 := by
  unfold tailWord_4033341
  simp only [CollatzResearch.WordTrace]
  refine ⟨147108031680901871646571877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98072021120601247764381251 147108031680901871646571877)
  ·
    refine ⟨27582755940169100933732227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147108031680901871646571877 27582755940169100933732227)
    ·
      refine ⟨41374133910253651400598341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27582755940169100933732227 41374133910253651400598341)
      ·
        refine ⟨7757650108172559637612189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41374133910253651400598341 7757650108172559637612189)
        ·
          refine ⟨2909118790564709864104571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7757650108172559637612189 2909118790564709864104571)
          ·
            refine ⟨4363678185847064796156857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909118790564709864104571 4363678185847064796156857)
            ·
              refine ⟨3272758639385298597117643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363678185847064796156857 3272758639385298597117643)
              ·
                refine ⟨4909137959077947895676465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272758639385298597117643 4909137959077947895676465)
                ·
                  refine ⟨3681853469308460921757349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4909137959077947895676465 3681853469308460921757349)
                  ·
                    refine ⟨690347525495336422829503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3681853469308460921757349 690347525495336422829503)
                    ·
                      rfl

theorem cell23_4033341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 1, 2, 4].length) (baseStart_4033341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033341 prefixEnd_4033341 := by exact prefixLift 4033341
  have htrace : WordTrace (prefixWord ++ tailWord_4033341) baseStart_4033341 baseEnd_4033341 := by
    simpa [prefixWord, tailWord_4033341, baseEnd_4033341] using wordTrace_append hprefix tailTrace_4033341
  have hstable : (prefixWord ++ tailWord_4033341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033341).length < 2 ^ (prefixWord ++ tailWord_4033341).sum := by decide
  have hdescent : baseEnd_4033341 < baseStart_4033341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033370 : List Nat := [3, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2]
def baseStart_4033370 : Nat := 118140960795 + 4033370 * 2 ^ 59
def prefixEnd_4033370 : Nat := 4983230072969 + 3 ^ 40 * 4033370 * 2
def baseEnd_4033370 : Nat := 2071057467424989655025875

theorem tailTrace_4033370 : CollatzResearch.WordTrace tailWord_4033370 prefixEnd_4033370 2071057467424989655025875 := by
  unfold tailWord_4033370
  simp only [CollatzResearch.WordTrace]
  refine ⟨36777272349449202399844391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98072726265197873066251709 36777272349449202399844391)
  ·
    refine ⟨55165908524173803599766587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36777272349449202399844391 55165908524173803599766587)
    ·
      refine ⟨82748862786260705399649881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55165908524173803599766587 82748862786260705399649881)
      ·
        refine ⟨62061647089695529049737411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82748862786260705399649881 62061647089695529049737411)
        ·
          refine ⟨93092470634543293574606117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62061647089695529049737411 93092470634543293574606117)
          ·
            refine ⟨17454838243976867545238647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93092470634543293574606117 17454838243976867545238647)
            ·
              refine ⟨26182257365965301317857971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17454838243976867545238647 26182257365965301317857971)
              ·
                refine ⟨39273386048947951976786957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26182257365965301317857971 39273386048947951976786957)
                ·
                  refine ⟨14727519768355481991295109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39273386048947951976786957 14727519768355481991295109)
                  ·
                    refine ⟨2761409956566652873367833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14727519768355481991295109 2761409956566652873367833)
                    ·
                      refine ⟨2071057467424989655025875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761409956566652873367833 2071057467424989655025875)
                      ·
                        rfl

theorem cell23_4033370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_4033370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033370 prefixEnd_4033370 := by exact prefixLift 4033370
  have htrace : WordTrace (prefixWord ++ tailWord_4033370) baseStart_4033370 baseEnd_4033370 := by
    simpa [prefixWord, tailWord_4033370, baseEnd_4033370] using wordTrace_append hprefix tailTrace_4033370
  have hstable : (prefixWord ++ tailWord_4033370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033370).length < 2 ^ (prefixWord ++ tailWord_4033370).sum := by decide
  have hdescent : baseEnd_4033370 < baseStart_4033370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033387 : List Nat := [1, 1, 1, 1, 2, 2, 5, 4, 2, 2, 2]
def baseStart_4033387 : Nat := 118140960795 + 4033387 * 2 ^ 59
def prefixEnd_4033387 : Nat := 4983230072969 + 3 ^ 40 * 4033387 * 2
def baseEnd_4033387 : Nat := 2071066196596116088513297

theorem tailTrace_4033387 : CollatzResearch.WordTrace tailWord_4033387 prefixEnd_4033387 2071066196596116088513297 := by
  unfold tailWord_4033387
  simp only [CollatzResearch.WordTrace]
  refine ⟨147109709438735221502746415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98073139625823481001830943 147109709438735221502746415)
  ·
    refine ⟨220664564158102832254119623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147109709438735221502746415 220664564158102832254119623)
    ·
      refine ⟨330996846237154248381179435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220664564158102832254119623 330996846237154248381179435)
      ·
        refine ⟨496495269355731372571769153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330996846237154248381179435 496495269355731372571769153)
        ·
          refine ⟨372371452016798529428826865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496495269355731372571769153 372371452016798529428826865)
          ·
            refine ⟨279278589012598897071620149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372371452016798529428826865 279278589012598897071620149)
            ·
              refine ⟨26182367719931146600464389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279278589012598897071620149 26182367719931146600464389)
              ·
                refine ⟨4909193947487089987587073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26182367719931146600464389 4909193947487089987587073)
                ·
                  refine ⟨3681895460615317490690305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4909193947487089987587073 3681895460615317490690305)
                  ·
                    refine ⟨2761421595461488118017729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3681895460615317490690305 2761421595461488118017729)
                    ·
                      refine ⟨2071066196596116088513297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761421595461488118017729 2071066196596116088513297)
                      ·
                        rfl

theorem cell23_4033387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 4, 2, 2, 2].length) (baseStart_4033387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033387 prefixEnd_4033387 := by exact prefixLift 4033387
  have htrace : WordTrace (prefixWord ++ tailWord_4033387) baseStart_4033387 baseEnd_4033387 := by
    simpa [prefixWord, tailWord_4033387, baseEnd_4033387] using wordTrace_append hprefix tailTrace_4033387
  have hstable : (prefixWord ++ tailWord_4033387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033387).length < 2 ^ (prefixWord ++ tailWord_4033387).sum := by decide
  have hdescent : baseEnd_4033387 < baseStart_4033387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033403 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3]
def baseStart_4033403 : Nat := 118140960795 + 4033403 * 2 ^ 59
def prefixEnd_4033403 : Nat := 4983230072969 + 3 ^ 40 * 4033403 * 2
def baseEnd_4033403 : Nat := 2071074412286588025913223

theorem tailTrace_4033403 : CollatzResearch.WordTrace tailWord_4033403 prefixEnd_4033403 2071074412286588025913223 := by
  unfold tailWord_4033403
  simp only [CollatzResearch.WordTrace]
  refine ⟨147110293006677256235328863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98073528671118170823552575 147110293006677256235328863)
  ·
    refine ⟨220665439510015884352993295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147110293006677256235328863 220665439510015884352993295)
    ·
      refine ⟨330998159265023826529489943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220665439510015884352993295 330998159265023826529489943)
      ·
        refine ⟨496497238897535739794234915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330998159265023826529489943 496497238897535739794234915)
        ·
          refine ⟨744745858346303609691352373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496497238897535739794234915 744745858346303609691352373)
          ·
            refine ⟨69819924219965963408564285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 744745858346303609691352373 69819924219965963408564285)
            ·
              refine ⟨26182471582487236278211607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69819924219965963408564285 26182471582487236278211607)
              ·
                refine ⟨39273707373730854417317411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26182471582487236278211607 39273707373730854417317411)
                ·
                  refine ⟨58910561060596281625976117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39273707373730854417317411 58910561060596281625976117)
                  ·
                    refine ⟨5522865099430901402435261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58910561060596281625976117 5522865099430901402435261)
                    ·
                      refine ⟨2071074412286588025913223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522865099430901402435261 2071074412286588025913223)
                      ·
                        rfl

theorem cell23_4033403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 3].length) (baseStart_4033403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033403 prefixEnd_4033403 := by exact prefixLift 4033403
  have htrace : WordTrace (prefixWord ++ tailWord_4033403) baseStart_4033403 baseEnd_4033403 := by
    simpa [prefixWord, tailWord_4033403, baseEnd_4033403] using wordTrace_append hprefix tailTrace_4033403
  have hstable : (prefixWord ++ tailWord_4033403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033403).length < 2 ^ (prefixWord ++ tailWord_4033403).sum := by decide
  have hdescent : baseEnd_4033403 < baseStart_4033403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033483 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 8]
def baseStart_4033483 : Nat := 118140960795 + 4033483 * 2 ^ 59
def prefixEnd_4033483 : Nat := 4983230072969 + 3 ^ 40 * 4033483 * 2
def baseEnd_4033483 : Nat := 230123943415438634768095

theorem tailTrace_4033483 : CollatzResearch.WordTrace tailWord_4033483 prefixEnd_4033483 230123943415438634768095 := by
  unfold tailWord_4033483
  simp only [CollatzResearch.WordTrace]
  refine ⟨147113210846387429898241103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98075473897591619932160735 147113210846387429898241103)
  ·
    refine ⟨220669816269581144847361655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147113210846387429898241103 220669816269581144847361655)
    ·
      refine ⟨331004724404371717271042483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220669816269581144847361655 331004724404371717271042483)
      ·
        refine ⟨496507086606557575906563725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331004724404371717271042483 496507086606557575906563725)
        ·
          refine ⟨186190157477459090964961397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496507086606557575906563725 186190157477459090964961397)
          ·
            refine ⟨17455327263511789777965131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186190157477459090964961397 17455327263511789777965131)
            ·
              refine ⟨26182990895267684666947697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17455327263511789777965131 26182990895267684666947697)
              ·
                refine ⟨19637243171450763500210773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26182990895267684666947697 19637243171450763500210773)
                ·
                  refine ⟨230123943415438634768095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19637243171450763500210773 230123943415438634768095)
                  ·
                    rfl

theorem cell23_4033483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 8].length) (baseStart_4033483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033483 prefixEnd_4033483 := by exact prefixLift 4033483
  have htrace : WordTrace (prefixWord ++ tailWord_4033483) baseStart_4033483 baseEnd_4033483 := by
    simpa [prefixWord, tailWord_4033483, baseEnd_4033483] using wordTrace_append hprefix tailTrace_4033483
  have hstable : (prefixWord ++ tailWord_4033483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033483).length < 2 ^ (prefixWord ++ tailWord_4033483).sum := by decide
  have hdescent : baseEnd_4033483 < baseStart_4033483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033494 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4033494 : Nat := 118140960795 + 4033494 * 2 ^ 59
def prefixEnd_4033494 : Nat := 4983230072969 + 3 ^ 40 * 4033494 * 2
def baseEnd_4033494 : Nat := 2071121139026147169875305

theorem tailTrace_4033494 : CollatzResearch.WordTrace tailWord_4033494 prefixEnd_4033494 2071121139026147169875305 := by
  unfold tailWord_4033494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194600753084223673555721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98075741366231719184594357 9194600753084223673555721)
  ·
    refine ⟨6895950564813167755166791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9194600753084223673555721 6895950564813167755166791)
    ·
      refine ⟨10343925847219751632750187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895950564813167755166791 10343925847219751632750187)
      ·
        refine ⟨15515888770829627449125281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343925847219751632750187 15515888770829627449125281)
        ·
          refine ⟨11636916578122220586843961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15515888770829627449125281 11636916578122220586843961)
          ·
            refine ⟨8727687433591665440132971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11636916578122220586843961 8727687433591665440132971)
            ·
              refine ⟨13091531150387498160199457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8727687433591665440132971 13091531150387498160199457)
              ·
                refine ⟨9818648362790623620149593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091531150387498160199457 9818648362790623620149593)
                ·
                  refine ⟨7363986272092967715112195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818648362790623620149593 7363986272092967715112195)
                  ·
                    refine ⟨11045979408139451572668293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7363986272092967715112195 11045979408139451572668293)
                    ·
                      refine ⟨2071121139026147169875305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11045979408139451572668293 2071121139026147169875305)
                      ·
                        rfl

theorem cell23_4033494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4033494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033494 prefixEnd_4033494 := by exact prefixLift 4033494
  have htrace : WordTrace (prefixWord ++ tailWord_4033494) baseStart_4033494 baseEnd_4033494 := by
    simpa [prefixWord, tailWord_4033494, baseEnd_4033494] using wordTrace_append hprefix tailTrace_4033494
  have hstable : (prefixWord ++ tailWord_4033494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033494).length < 2 ^ (prefixWord ++ tailWord_4033494).sum := by decide
  have hdescent : baseEnd_4033494 < baseStart_4033494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033497 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 3]
def baseStart_4033497 : Nat := 118140960795 + 4033497 * 2 ^ 59
def prefixEnd_4033497 : Nat := 4983230072969 + 3 ^ 40 * 4033497 * 2
def baseEnd_4033497 : Nat := 2071122679468110658137791

theorem tailTrace_4033497 : CollatzResearch.WordTrace tailWord_4033497 prefixEnd_4033497 2071122679468110658137791 := by
  unfold tailWord_4033497
  simp only [CollatzResearch.WordTrace]
  refine ⟨147113721468336710289250745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98075814312224473526167163 147113721468336710289250745)
  ·
    refine ⟨110335291101252532716938059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147113721468336710289250745 110335291101252532716938059)
    ·
      refine ⟨165502936651878799075407089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110335291101252532716938059 165502936651878799075407089)
      ·
        refine ⟨124127202488909099306555317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165502936651878799075407089 124127202488909099306555317)
        ·
          refine ⟨11636925233335228059989561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124127202488909099306555317 11636925233335228059989561)
          ·
            refine ⟨8727693925001421044992171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11636925233335228059989561 8727693925001421044992171)
            ·
              refine ⟨13091540887502131567488257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8727693925001421044992171 13091540887502131567488257)
              ·
                refine ⟨9818655665626598675616193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091540887502131567488257 9818655665626598675616193)
                ·
                  refine ⟨7363991749219949006712145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818655665626598675616193 7363991749219949006712145)
                  ·
                    refine ⟨5522993811914961755034109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7363991749219949006712145 5522993811914961755034109)
                    ·
                      refine ⟨2071122679468110658137791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5522993811914961755034109 2071122679468110658137791)
                      ·
                        rfl

theorem cell23_4033497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 3].length) (baseStart_4033497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033497 prefixEnd_4033497 := by exact prefixLift 4033497
  have htrace : WordTrace (prefixWord ++ tailWord_4033497) baseStart_4033497 baseEnd_4033497 := by
    simpa [prefixWord, tailWord_4033497, baseEnd_4033497] using wordTrace_append hprefix tailTrace_4033497
  have hstable : (prefixWord ++ tailWord_4033497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033497).length < 2 ^ (prefixWord ++ tailWord_4033497).sum := by decide
  have hdescent : baseEnd_4033497 < baseStart_4033497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033561 : List Nat := [1, 2, 1, 2, 1, 1, 8, 2, 1, 1, 3]
def baseStart_4033561 : Nat := 118140960795 + 4033561 * 2 ^ 59
def prefixEnd_4033561 : Nat := 4983230072969 + 3 ^ 40 * 4033561 * 2
def baseEnd_4033561 : Nat := 2071155542229998407737497

theorem tailTrace_4033561 : CollatzResearch.WordTrace tailWord_4033561 prefixEnd_4033561 2071155542229998407737497 := by
  unfold tailWord_4033561
  simp only [CollatzResearch.WordTrace]
  refine ⟨147116055740104849219580537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98077370493403232813053691 147116055740104849219580537)
  ·
    refine ⟨110337041805078636914685403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147116055740104849219580537 110337041805078636914685403)
    ·
      refine ⟨165505562707617955372028105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110337041805078636914685403 165505562707617955372028105)
      ·
        refine ⟨124129172030713466529021079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165505562707617955372028105 124129172030713466529021079)
        ·
          refine ⟨186193758046070199793531619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124129172030713466529021079 186193758046070199793531619)
          ·
            refine ⟨279290637069105299690297429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186193758046070199793531619 279290637069105299690297429)
            ·
              refine ⟨3272937153153577730745673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 279290637069105299690297429 3272937153153577730745673)
              ·
                refine ⟨2454702864865183298059255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3272937153153577730745673 2454702864865183298059255)
                ·
                  refine ⟨3682054297297774947088883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454702864865183298059255 3682054297297774947088883)
                  ·
                    refine ⟨5523081445946662420633325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682054297297774947088883 5523081445946662420633325)
                    ·
                      refine ⟨2071155542229998407737497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523081445946662420633325 2071155542229998407737497)
                      ·
                        rfl

theorem cell23_4033561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 2, 1, 1, 3].length) (baseStart_4033561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033561 prefixEnd_4033561 := by exact prefixLift 4033561
  have htrace : WordTrace (prefixWord ++ tailWord_4033561) baseStart_4033561 baseEnd_4033561 := by
    simpa [prefixWord, tailWord_4033561, baseEnd_4033561] using wordTrace_append hprefix tailTrace_4033561
  have hstable : (prefixWord ++ tailWord_4033561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033561).length < 2 ^ (prefixWord ++ tailWord_4033561).sum := by decide
  have hdescent : baseEnd_4033561 < baseStart_4033561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033584 : List Nat := [2, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2]
def baseStart_4033584 : Nat := 118140960795 + 4033584 * 2 ^ 59
def prefixEnd_4033584 : Nat := 4983230072969 + 3 ^ 40 * 4033584 * 2
def baseEnd_4033584 : Nat := 2071167352285051817749891

theorem tailTrace_4033584 : CollatzResearch.WordTrace tailWord_4033584 prefixEnd_4033584 2071167352285051817749891 := by
  unfold tailWord_4033584
  simp only [CollatzResearch.WordTrace]
  refine ⟨73558447309510762073833903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98077929746014349431778537 73558447309510762073833903)
  ·
    refine ⟨110337670964266143110750855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73558447309510762073833903 110337670964266143110750855)
    ·
      refine ⟨165506506446399214666126283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110337670964266143110750855 165506506446399214666126283)
      ·
        refine ⟨248259759669598821999189425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165506506446399214666126283 248259759669598821999189425)
        ·
          refine ⟨186194819752199116499392069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248259759669598821999189425 186194819752199116499392069)
          ·
            refine ⟨34911528703537334343636013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186194819752199116499392069 34911528703537334343636013)
            ·
              refine ⟨13091823263826500378863505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34911528703537334343636013 13091823263826500378863505)
              ·
                refine ⟨9818867447869875284147629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091823263826500378863505 9818867447869875284147629)
                ·
                  refine ⟨3682075292951203231555361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9818867447869875284147629 3682075292951203231555361)
                  ·
                    refine ⟨2761556469713402423666521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682075292951203231555361 2761556469713402423666521)
                    ·
                      refine ⟨2071167352285051817749891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761556469713402423666521 2071167352285051817749891)
                      ·
                        rfl

theorem cell23_4033584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 3, 2, 2].length) (baseStart_4033584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033584 prefixEnd_4033584 := by exact prefixLift 4033584
  have htrace : WordTrace (prefixWord ++ tailWord_4033584) baseStart_4033584 baseEnd_4033584 := by
    simpa [prefixWord, tailWord_4033584, baseEnd_4033584] using wordTrace_append hprefix tailTrace_4033584
  have hstable : (prefixWord ++ tailWord_4033584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033584).length < 2 ^ (prefixWord ++ tailWord_4033584).sum := by decide
  have hdescent : baseEnd_4033584 < baseStart_4033584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033587 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 3]
def baseStart_4033587 : Nat := 118140960795 + 4033587 * 2 ^ 59
def prefixEnd_4033587 : Nat := 4983230072969 + 3 ^ 40 * 4033587 * 2
def baseEnd_4033587 : Nat := 2071168892727015306012377

theorem tailTrace_4033587 : CollatzResearch.WordTrace tailWord_4033587 prefixEnd_4033587 2071168892727015306012377 := by
  unfold tailWord_4033587
  simp only [CollatzResearch.WordTrace]
  refine ⟨147117004038010655660027015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98078002692007103773351343 147117004038010655660027015)
  ·
    refine ⟨220675506057015983490040523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147117004038010655660027015 220675506057015983490040523)
    ·
      refine ⟨331013259085523975235060785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220675506057015983490040523 331013259085523975235060785)
      ·
        refine ⟨248259944314142981426295589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331013259085523975235060785 248259944314142981426295589)
        ·
          refine ⟨46548739558901809017430423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248259944314142981426295589 46548739558901809017430423)
          ·
            refine ⟨69823109338352713526145635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46548739558901809017430423 69823109338352713526145635)
            ·
              refine ⟨104734664007529070289218453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69823109338352713526145635 104734664007529070289218453)
              ·
                refine ⟨4909437375352925169807115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104734664007529070289218453 4909437375352925169807115)
                ·
                  refine ⟨7364156063029387754710673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909437375352925169807115 7364156063029387754710673)
                  ·
                    refine ⟨5523117047272040816033005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7364156063029387754710673 5523117047272040816033005)
                    ·
                      refine ⟨2071168892727015306012377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523117047272040816033005 2071168892727015306012377)
                      ·
                        rfl

theorem cell23_4033587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 2, 3].length) (baseStart_4033587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033587 prefixEnd_4033587 := by exact prefixLift 4033587
  have htrace : WordTrace (prefixWord ++ tailWord_4033587) baseStart_4033587 baseEnd_4033587 := by
    simpa [prefixWord, tailWord_4033587, baseEnd_4033587] using wordTrace_append hprefix tailTrace_4033587
  have hstable : (prefixWord ++ tailWord_4033587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033587).length < 2 ^ (prefixWord ++ tailWord_4033587).sum := by decide
  have hdescent : baseEnd_4033587 < baseStart_4033587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033588 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_4033588 : Nat := 118140960795 + 4033588 * 2 ^ 59
def prefixEnd_4033588 : Nat := 4983230072969 + 3 ^ 40 * 4033588 * 2
def baseEnd_4033588 : Nat := 2071169406207669802099873

theorem tailTrace_4033588 : CollatzResearch.WordTrace tailWord_4033588 prefixEnd_4033588 2071169406207669802099873 := by
  unfold tailWord_4033588
  simp only [CollatzResearch.WordTrace]
  refine ⟨73558520255503516415406709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98078027007338021887208945 73558520255503516415406709)
  ·
    refine ⟨6896111273953454663944379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73558520255503516415406709 6896111273953454663944379)
    ·
      refine ⟨10344166910930181995916569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896111273953454663944379 10344166910930181995916569)
      ·
        refine ⟨7758125183197636496937427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10344166910930181995916569 7758125183197636496937427)
        ·
          refine ⟨11637187774796454745406141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758125183197636496937427 11637187774796454745406141)
          ·
            refine ⟨4363945415548670529527303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11637187774796454745406141 4363945415548670529527303)
            ·
              refine ⟨6545918123323005794290955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363945415548670529527303 6545918123323005794290955)
              ·
                refine ⟨9818877184984508691436433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545918123323005794290955 9818877184984508691436433)
                ·
                  refine ⟨7364157888738381518577325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9818877184984508691436433 7364157888738381518577325)
                  ·
                    refine ⟨2761559208276893069466497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7364157888738381518577325 2761559208276893069466497)
                    ·
                      refine ⟨2071169406207669802099873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761559208276893069466497 2071169406207669802099873)
                      ·
                        rfl

theorem cell23_4033588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_4033588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033588 prefixEnd_4033588 := by exact prefixLift 4033588
  have htrace : WordTrace (prefixWord ++ tailWord_4033588) baseStart_4033588 baseEnd_4033588 := by
    simpa [prefixWord, tailWord_4033588, baseEnd_4033588] using wordTrace_append hprefix tailTrace_4033588
  have hstable : (prefixWord ++ tailWord_4033588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033588).length < 2 ^ (prefixWord ++ tailWord_4033588).sum := by decide
  have hdescent : baseEnd_4033588 < baseStart_4033588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033597 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4033597 : Nat := 118140960795 + 4033597 * 2 ^ 59
def prefixEnd_4033597 : Nat := 4983230072969 + 3 ^ 40 * 4033597 * 2
def baseEnd_4033597 : Nat := 2071174027533560266887331

theorem tailTrace_4033597 : CollatzResearch.WordTrace tailWord_4033597 prefixEnd_4033597 2071174027533560266887331 := by
  unfold tailWord_4033597
  simp only [CollatzResearch.WordTrace]
  refine ⟨147117368767974427367891045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98078245845316284911927363 147117368767974427367891045)
  ·
    refine ⟨27584506643995205131479571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147117368767974427367891045 27584506643995205131479571)
    ·
      refine ⟨41376759965992807697219357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27584506643995205131479571 41376759965992807697219357)
      ·
        refine ⟨15516284987247302886457259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41376759965992807697219357 15516284987247302886457259)
        ·
          refine ⟨23274427480870954329685889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15516284987247302886457259 23274427480870954329685889)
          ·
            refine ⟨17455820610653215747264417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23274427480870954329685889 17455820610653215747264417)
            ·
              refine ⟨13091865457989911810448313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17455820610653215747264417 13091865457989911810448313)
              ·
                refine ⟨9818899093492433857836235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13091865457989911810448313 9818899093492433857836235)
                ·
                  refine ⟨14728348640238650786754353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9818899093492433857836235 14728348640238650786754353)
                  ·
                    refine ⟨11046261480178988090065765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14728348640238650786754353 11046261480178988090065765)
                    ·
                      refine ⟨2071174027533560266887331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11046261480178988090065765 2071174027533560266887331)
                      ·
                        rfl

theorem cell23_4033597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4033597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033597 prefixEnd_4033597 := by exact prefixLift 4033597
  have htrace : WordTrace (prefixWord ++ tailWord_4033597) baseStart_4033597 baseEnd_4033597 := by
    simpa [prefixWord, tailWord_4033597, baseEnd_4033597] using wordTrace_append hprefix tailTrace_4033597
  have hstable : (prefixWord ++ tailWord_4033597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033597).length < 2 ^ (prefixWord ++ tailWord_4033597).sum := by decide
  have hdescent : baseEnd_4033597 < baseStart_4033597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033618 : List Nat := [3, 2, 2, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_4033618 : Nat := 118140960795 + 4033618 * 2 ^ 59
def prefixEnd_4033618 : Nat := 4983230072969 + 3 ^ 40 * 4033618 * 2
def baseEnd_4033618 : Nat := 2071184810627304684724735

theorem tailTrace_4033618 : CollatzResearch.WordTrace tailWord_4033618 prefixEnd_4033618 2071184810627304684724735 := by
  unfold tailWord_4033618
  simp only [CollatzResearch.WordTrace]
  refine ⟨36779533675224586988601377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98078756467265565302937005 36779533675224586988601377)
  ·
    refine ⟨27584650256418440241451033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36779533675224586988601377 27584650256418440241451033)
    ·
      refine ⟨20688487692313830181088275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27584650256418440241451033 20688487692313830181088275)
      ·
        refine ⟨31032731538470745271632413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20688487692313830181088275 31032731538470745271632413)
        ·
          refine ⟨11637274326926529476862155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31032731538470745271632413 11637274326926529476862155)
          ·
            refine ⟨17455911490389794215293233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637274326926529476862155 17455911490389794215293233)
            ·
              refine ⟨13091933617792345661469925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17455911490389794215293233 13091933617792345661469925)
              ·
                refine ⟨2454737553336064811525611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13091933617792345661469925 2454737553336064811525611)
                ·
                  refine ⟨3682106330004097217288417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454737553336064811525611 3682106330004097217288417)
                  ·
                    refine ⟨2761579747503072912966313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682106330004097217288417 2761579747503072912966313)
                    ·
                      refine ⟨2071184810627304684724735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761579747503072912966313 2071184810627304684724735)
                      ·
                        rfl

theorem cell23_4033618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_4033618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033618 prefixEnd_4033618 := by exact prefixLift 4033618
  have htrace : WordTrace (prefixWord ++ tailWord_4033618) baseStart_4033618 baseEnd_4033618 := by
    simpa [prefixWord, tailWord_4033618, baseEnd_4033618] using wordTrace_append hprefix tailTrace_4033618
  have hstable : (prefixWord ++ tailWord_4033618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033618).length < 2 ^ (prefixWord ++ tailWord_4033618).sum := by decide
  have hdescent : baseEnd_4033618 < baseStart_4033618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033620 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_4033620 : Nat := 118140960795 + 4033620 * 2 ^ 59
def prefixEnd_4033620 : Nat := 4983230072969 + 3 ^ 40 * 4033620 * 2
def baseEnd_4033620 : Nat := 690395279196204558966575

theorem tailTrace_4033620 : CollatzResearch.WordTrace tailWord_4033620 prefixEnd_4033620 690395279196204558966575 := by
  unfold tailWord_4033620
  simp only [CollatzResearch.WordTrace]
  refine ⟨73559103823445551147989157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98078805097927401530652209 73559103823445551147989157)
  ·
    refine ⟨13792331966896040840247967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73559103823445551147989157 13792331966896040840247967)
    ·
      refine ⟨20688497950344061260371951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13792331966896040840247967 20688497950344061260371951)
      ·
        refine ⟨31032746925516091890557927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20688497950344061260371951 31032746925516091890557927)
        ·
          refine ⟨46549120388274137835836891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31032746925516091890557927 46549120388274137835836891)
          ·
            refine ⟨69823680582411206753755337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46549120388274137835836891 69823680582411206753755337)
            ·
              refine ⟨52367760436808405065316503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69823680582411206753755337 52367760436808405065316503)
              ·
                refine ⟨78551640655212607597974755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52367760436808405065316503 78551640655212607597974755)
                ·
                  refine ⟨117827460982818911396962133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78551640655212607597974755 117827460982818911396962133)
                  ·
                    refine ⟨690395279196204558966575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117827460982818911396962133 690395279196204558966575)
                    ·
                      rfl

theorem cell23_4033620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_4033620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033620 prefixEnd_4033620 := by exact prefixLift 4033620
  have htrace : WordTrace (prefixWord ++ tailWord_4033620) baseStart_4033620 baseEnd_4033620 := by
    simpa [prefixWord, tailWord_4033620, baseEnd_4033620] using wordTrace_append hprefix tailTrace_4033620
  have hstable : (prefixWord ++ tailWord_4033620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033620).length < 2 ^ (prefixWord ++ tailWord_4033620).sum := by decide
  have hdescent : baseEnd_4033620 < baseStart_4033620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033680 : List Nat := [2, 1, 1, 1, 1, 1, 4, 5, 7]
def baseStart_4033680 : Nat := 118140960795 + 4033680 * 2 ^ 59
def prefixEnd_4033680 : Nat := 4983230072969 + 3 ^ 40 * 4033680 * 2
def baseEnd_4033680 : Nat := 230135182936431493572161

theorem tailTrace_4033680 : CollatzResearch.WordTrace tailWord_4033680 prefixEnd_4033680 230135182936431493572161 := by
  unfold tailWord_4033680
  simp only [CollatzResearch.WordTrace]
  refine ⟨73560198013336866271581247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98080264017782488362108329 73560198013336866271581247)
  ·
    refine ⟨110340297020005299407371871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73560198013336866271581247 110340297020005299407371871)
    ·
      refine ⟨165510445530007949111057807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110340297020005299407371871 165510445530007949111057807)
      ·
        refine ⟨248265668295011923666586711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165510445530007949111057807 248265668295011923666586711)
        ·
          refine ⟨372398502442517885499880067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248265668295011923666586711 372398502442517885499880067)
          ·
            refine ⟨558597753663776828249820101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372398502442517885499880067 558597753663776828249820101)
            ·
              refine ⟨104737078811958155296841269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 558597753663776828249820101 104737078811958155296841269)
              ·
                refine ⟨9819101138621077059078869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104737078811958155296841269 9819101138621077059078869)
                ·
                  refine ⟨230135182936431493572161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9819101138621077059078869 230135182936431493572161)
                  ·
                    rfl

theorem cell23_4033680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_4033680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033680 prefixEnd_4033680 := by exact prefixLift 4033680
  have htrace : WordTrace (prefixWord ++ tailWord_4033680) baseStart_4033680 baseEnd_4033680 := by
    simpa [prefixWord, tailWord_4033680, baseEnd_4033680] using wordTrace_append hprefix tailTrace_4033680
  have hstable : (prefixWord ++ tailWord_4033680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033680).length < 2 ^ (prefixWord ++ tailWord_4033680).sum := by decide
  have hdescent : baseEnd_4033680 < baseStart_4033680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033694 : List Nat := [4, 3, 1, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4033694 : Nat := 118140960795 + 4033694 * 2 ^ 59
def prefixEnd_4033694 : Nat := 4983230072969 + 3 ^ 40 * 4033694 * 2
def baseEnd_4033694 : Nat := 2071223835157046387374385

theorem tailTrace_4033694 : CollatzResearch.WordTrace tailWord_4033694 prefixEnd_4033694 2071223835157046387374385 := by
  unfold tailWord_4033694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18390113331077876616771517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98080604432415341956114757 18390113331077876616771517)
  ·
    refine ⟨6896292499154203731289319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18390113331077876616771517 6896292499154203731289319)
    ·
      refine ⟨10344438748731305596933979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896292499154203731289319 10344438748731305596933979)
      ·
        refine ⟨15516658123096958395400969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10344438748731305596933979 15516658123096958395400969)
        ·
          refine ⟨11637493592322718796550727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15516658123096958395400969 11637493592322718796550727)
          ·
            refine ⟨17456240388484078194826091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637493592322718796550727 17456240388484078194826091)
            ·
              refine ⟨26184360582726117292239137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17456240388484078194826091 26184360582726117292239137)
              ·
                refine ⟨19638270437044587969179353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26184360582726117292239137 19638270437044587969179353)
                ·
                  refine ⟨14728702827783440976884515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19638270437044587969179353 14728702827783440976884515)
                  ·
                    refine ⟨22093054241675161465326773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14728702827783440976884515 22093054241675161465326773)
                    ·
                      refine ⟨2071223835157046387374385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22093054241675161465326773 2071223835157046387374385)
                      ·
                        rfl

theorem cell23_4033694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4033694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033694 prefixEnd_4033694 := by exact prefixLift 4033694
  have htrace : WordTrace (prefixWord ++ tailWord_4033694) baseStart_4033694 baseEnd_4033694 := by
    simpa [prefixWord, tailWord_4033694, baseEnd_4033694] using wordTrace_append hprefix tailTrace_4033694
  have hstable : (prefixWord ++ tailWord_4033694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033694).length < 2 ^ (prefixWord ++ tailWord_4033694).sum := by decide
  have hdescent : baseEnd_4033694 < baseStart_4033694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033695 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4033695 : Nat := 118140960795 + 4033695 * 2 ^ 59
def prefixEnd_4033695 : Nat := 4983230072969 + 3 ^ 40 * 4033695 * 2
def baseEnd_4033695 : Nat := 2071224348637700883461881

theorem tailTrace_4033695 : CollatzResearch.WordTrace tailWord_4033695 prefixEnd_4033695 2071224348637700883461881 := by
  unfold tailWord_4033695
  simp only [CollatzResearch.WordTrace]
  refine ⟨147120943121619390104958539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98080628747746260069972359 147120943121619390104958539)
  ·
    refine ⟨220681414682429085157437809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147120943121619390104958539 220681414682429085157437809)
    ·
      refine ⟨165511061011821813868078357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220681414682429085157437809 165511061011821813868078357)
      ·
        refine ⟨7758330984929147525066173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165511061011821813868078357 7758330984929147525066173)
        ·
          refine ⟨2909374119348430321899815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7758330984929147525066173 2909374119348430321899815)
          ·
            refine ⟨4364061179022645482849723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909374119348430321899815 4364061179022645482849723)
            ·
              refine ⟨6546091768533968224274585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364061179022645482849723 6546091768533968224274585)
              ·
                refine ⟨4909568826400476168205939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546091768533968224274585 4909568826400476168205939)
                ·
                  refine ⟨7364353239600714252308909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909568826400476168205939 7364353239600714252308909)
                  ·
                    refine ⟨2761632464850267844615841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7364353239600714252308909 2761632464850267844615841)
                    ·
                      refine ⟨2071224348637700883461881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761632464850267844615841 2071224348637700883461881)
                      ·
                        rfl

theorem cell23_4033695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4033695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033695 prefixEnd_4033695 := by exact prefixLift 4033695
  have htrace : WordTrace (prefixWord ++ tailWord_4033695) baseStart_4033695 baseEnd_4033695 := by
    simpa [prefixWord, tailWord_4033695, baseEnd_4033695] using wordTrace_append hprefix tailTrace_4033695
  have hstable : (prefixWord ++ tailWord_4033695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033695).length < 2 ^ (prefixWord ++ tailWord_4033695).sum := by decide
  have hdescent : baseEnd_4033695 < baseStart_4033695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033727 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 2, 5]
def baseStart_4033727 : Nat := 118140960795 + 4033727 * 2 ^ 59
def prefixEnd_4033727 : Nat := 4983230072969 + 3 ^ 40 * 4033727 * 2
def baseEnd_4033727 : Nat := 690413593339548252753911

theorem tailTrace_4033727 : CollatzResearch.WordTrace tailWord_4033727 prefixEnd_4033727 690413593339548252753911 := by
  unfold tailWord_4033727
  simp only [CollatzResearch.WordTrace]
  refine ⟨147122110257503459570123435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98081406838335639713415623 147122110257503459570123435)
  ·
    refine ⟨220683165386255189355185153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147122110257503459570123435 220683165386255189355185153)
    ·
      refine ⟨165512374039691392016388865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220683165386255189355185153 165512374039691392016388865)
      ·
        refine ⟨124134280529768544012291649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165512374039691392016388865 124134280529768544012291649)
        ·
          refine ⟨93100710397326408009218737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124134280529768544012291649 93100710397326408009218737)
          ·
            refine ⟨69825532797994806006914053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93100710397326408009218737 69825532797994806006914053)
            ·
              refine ⟨13092287399624026126296385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69825532797994806006914053 13092287399624026126296385)
              ·
                refine ⟨9819215549718019594722289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092287399624026126296385 9819215549718019594722289)
                ·
                  refine ⟨7364411662288514696041717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9819215549718019594722289 7364411662288514696041717)
                  ·
                    refine ⟨690413593339548252753911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7364411662288514696041717 690413593339548252753911)
                    ·
                      rfl

theorem cell23_4033727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_4033727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033727 prefixEnd_4033727 := by exact prefixLift 4033727
  have htrace : WordTrace (prefixWord ++ tailWord_4033727) baseStart_4033727 baseEnd_4033727 := by
    simpa [prefixWord, tailWord_4033727, baseEnd_4033727] using wordTrace_append hprefix tailTrace_4033727
  have hstable : (prefixWord ++ tailWord_4033727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033727).length < 2 ^ (prefixWord ++ tailWord_4033727).sum := by decide
  have hdescent : baseEnd_4033727 < baseStart_4033727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033764 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 2, 1, 4]
def baseStart_4033764 : Nat := 118140960795 + 4033764 * 2 ^ 59
def prefixEnd_4033764 : Nat := 4983230072969 + 3 ^ 40 * 4033764 * 2
def baseEnd_4033764 : Nat := 2071259778802861113499063

theorem tailTrace_4033764 : CollatzResearch.WordTrace tailWord_4033764 prefixEnd_4033764 2071259778802861113499063 := by
  unfold tailWord_4033764
  simp only [CollatzResearch.WordTrace]
  refine ⟨73561729879184707444610173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98082306505579609926146897 73561729879184707444610173)
  ·
    refine ⟨27585648704694265291728815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73561729879184707444610173 27585648704694265291728815)
    ·
      refine ⟨41378473057041397937593223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27585648704694265291728815 41378473057041397937593223)
      ·
        refine ⟨62067709585562096906389835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41378473057041397937593223 62067709585562096906389835)
        ·
          refine ⟨93101564378343145359584753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62067709585562096906389835 93101564378343145359584753)
          ·
            refine ⟨69826173283757359019688565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93101564378343145359584753 69826173283757359019688565)
            ·
              refine ⟨6546203745352252408095803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69826173283757359019688565 6546203745352252408095803)
              ·
                refine ⟨9819305618028378612143705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546203745352252408095803 9819305618028378612143705)
                ·
                  refine ⟨7364479213521283959107779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9819305618028378612143705 7364479213521283959107779)
                  ·
                    refine ⟨11046718820281925938661669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7364479213521283959107779 11046718820281925938661669)
                    ·
                      refine ⟨2071259778802861113499063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11046718820281925938661669 2071259778802861113499063)
                      ·
                        rfl

theorem cell23_4033764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_4033764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033764 prefixEnd_4033764 := by exact prefixLift 4033764
  have htrace : WordTrace (prefixWord ++ tailWord_4033764) baseStart_4033764 baseEnd_4033764 := by
    simpa [prefixWord, tailWord_4033764, baseEnd_4033764] using wordTrace_append hprefix tailTrace_4033764
  have hstable : (prefixWord ++ tailWord_4033764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033764).length < 2 ^ (prefixWord ++ tailWord_4033764).sum := by decide
  have hdescent : baseEnd_4033764 < baseStart_4033764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033791 : List Nat := [1, 1, 2, 2, 1, 5, 2, 4, 1, 4]
def baseStart_4033791 : Nat := 118140960795 + 4033791 * 2 ^ 59
def prefixEnd_4033791 : Nat := 4983230072969 + 3 ^ 40 * 4033791 * 2
def baseEnd_4033791 : Nat := 690424547593510835953813

theorem tailTrace_4033791 : CollatzResearch.WordTrace tailWord_4033791 prefixEnd_4033791 690424547593510835953813 := by
  unfold tailWord_4033791
  simp only [CollatzResearch.WordTrace]
  refine ⟨147124444529271598500453227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98082963019514399000302151 147124444529271598500453227)
  ·
    refine ⟨220686666793907397750679841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147124444529271598500453227 220686666793907397750679841)
    ·
      refine ⟨165515000095430548313009881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220686666793907397750679841 165515000095430548313009881)
      ·
        refine ⟨124136250071572911234757411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165515000095430548313009881 124136250071572911234757411)
        ·
          refine ⟨186204375107359366852136117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124136250071572911234757411 186204375107359366852136117)
          ·
            refine ⟨17456660166314940642387761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186204375107359366852136117 17456660166314940642387761)
            ·
              refine ⟨13092495124736205481790821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17456660166314940642387761 13092495124736205481790821)
              ·
                refine ⟨2454842835888038527835779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13092495124736205481790821 2454842835888038527835779)
                ·
                  refine ⟨3682264253832057791753669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2454842835888038527835779 3682264253832057791753669)
                  ·
                    refine ⟨690424547593510835953813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3682264253832057791753669 690424547593510835953813)
                    ·
                      rfl

theorem cell23_4033791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 4, 1, 4].length) (baseStart_4033791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033791 prefixEnd_4033791 := by exact prefixLift 4033791
  have htrace : WordTrace (prefixWord ++ tailWord_4033791) baseStart_4033791 baseEnd_4033791 := by
    simpa [prefixWord, tailWord_4033791, baseEnd_4033791] using wordTrace_append hprefix tailTrace_4033791
  have hstable : (prefixWord ++ tailWord_4033791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033791).length < 2 ^ (prefixWord ++ tailWord_4033791).sum := by decide
  have hdescent : baseEnd_4033791 < baseStart_4033791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033841 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 4, 3, 2]
def baseStart_4033841 : Nat := 118140960795 + 4033841 * 2 ^ 59
def prefixEnd_4033841 : Nat := 4983230072969 + 3 ^ 40 * 4033841 * 2
def baseEnd_4033841 : Nat := 2071299316813257312236209

theorem tailTrace_4033841 : CollatzResearch.WordTrace tailWord_4033841 prefixEnd_4033841 2071299316813257312236209 := by
  unfold tailWord_4033841
  simp only [CollatzResearch.WordTrace]
  refine ⟨147126268179090457039773377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98084178786060304693182251 147126268179090457039773377)
  ·
    refine ⟨110344701134317842779830033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147126268179090457039773377 110344701134317842779830033)
    ·
      refine ⟨82758525850738382084872525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110344701134317842779830033 82758525850738382084872525)
      ·
        refine ⟨31034447194026893281827197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82758525850738382084872525 31034447194026893281827197)
        ·
          refine ⟨11637917697760084980685199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31034447194026893281827197 11637917697760084980685199)
          ·
            refine ⟨17456876546640127471027799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11637917697760084980685199 17456876546640127471027799)
            ·
              refine ⟨26185314819960191206541699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17456876546640127471027799 26185314819960191206541699)
              ·
                refine ⟨39277972229940286809812549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26185314819960191206541699 39277972229940286809812549)
                ·
                  refine ⟨7364619793113803776839853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39277972229940286809812549 7364619793113803776839853)
                  ·
                    refine ⟨2761732422417676416314945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7364619793113803776839853 2761732422417676416314945)
                    ·
                      refine ⟨2071299316813257312236209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761732422417676416314945 2071299316813257312236209)
                      ·
                        rfl

theorem cell23_4033841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_4033841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033841 prefixEnd_4033841 := by exact prefixLift 4033841
  have htrace : WordTrace (prefixWord ++ tailWord_4033841) baseStart_4033841 baseEnd_4033841 := by
    simpa [prefixWord, tailWord_4033841, baseEnd_4033841] using wordTrace_append hprefix tailTrace_4033841
  have hstable : (prefixWord ++ tailWord_4033841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033841).length < 2 ^ (prefixWord ++ tailWord_4033841).sum := by decide
  have hdescent : baseEnd_4033841 < baseStart_4033841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033888 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4]
def baseStart_4033888 : Nat := 118140960795 + 4033888 * 2 ^ 59
def prefixEnd_4033888 : Nat := 4983230072969 + 3 ^ 40 * 4033888 * 2
def baseEnd_4033888 : Nat := 2071323450404018628348493

theorem tailTrace_4033888 : CollatzResearch.WordTrace tailWord_4033888 prefixEnd_4033888 2071323450404018628348493 := by
  unfold tailWord_4033888
  simp only [CollatzResearch.WordTrace]
  refine ⟨73563991204960092033367159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98085321606613456044489545 73563991204960092033367159)
  ·
    refine ⟨110345986807440138050050739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73563991204960092033367159 110345986807440138050050739)
    ·
      refine ⟨165518980211160207075076109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110345986807440138050050739 165518980211160207075076109)
      ·
        refine ⟨62069617579185077653153541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165518980211160207075076109 62069617579185077653153541)
        ·
          refine ⟨11638053296097202059966289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62069617579185077653153541 11638053296097202059966289)
          ·
            refine ⟨8728539972072901544974717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11638053296097202059966289 8728539972072901544974717)
            ·
              refine ⟨3273202489527338079365519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8728539972072901544974717 3273202489527338079365519)
              ·
                refine ⟨4909803734291007119048279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273202489527338079365519 4909803734291007119048279)
                ·
                  refine ⟨7364705601436510678572419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4909803734291007119048279 7364705601436510678572419)
                  ·
                    refine ⟨11047058402154766017858629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7364705601436510678572419 11047058402154766017858629)
                    ·
                      refine ⟨2071323450404018628348493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11047058402154766017858629 2071323450404018628348493)
                      ·
                        rfl

theorem cell23_4033888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_4033888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033888 prefixEnd_4033888 := by exact prefixLift 4033888
  have htrace : WordTrace (prefixWord ++ tailWord_4033888) baseStart_4033888 baseEnd_4033888 := by
    simpa [prefixWord, tailWord_4033888, baseEnd_4033888] using wordTrace_append hprefix tailTrace_4033888
  have hstable : (prefixWord ++ tailWord_4033888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033888).length < 2 ^ (prefixWord ++ tailWord_4033888).sum := by decide
  have hdescent : baseEnd_4033888 < baseStart_4033888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033891 : List Nat := [1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 5]
def baseStart_4033891 : Nat := 118140960795 + 4033891 * 2 ^ 59
def prefixEnd_4033891 : Nat := 4983230072969 + 3 ^ 40 * 4033891 * 2
def baseEnd_4033891 : Nat := 2071324990845982116610979

theorem tailTrace_4033891 : CollatzResearch.WordTrace tailWord_4033891 prefixEnd_4033891 2071324990845982116610979 := by
  unfold tailWord_4033891
  simp only [CollatzResearch.WordTrace]
  refine ⟨147128091828909315579093527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98085394552606210386062351 147128091828909315579093527)
  ·
    refine ⟨220692137743363973368640291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147128091828909315579093527 220692137743363973368640291)
    ·
      refine ⟨331038206615045960052960437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220692137743363973368640291 331038206615045960052960437)
      ·
        refine ⟨31034831870160558754965041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331038206615045960052960437 31034831870160558754965041)
        ·
          refine ⟨23276123902620419066223781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31034831870160558754965041 23276123902620419066223781)
          ·
            refine ⟨4364273231741328574916959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23276123902620419066223781 4364273231741328574916959)
            ·
              refine ⟨6546409847611992862375439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364273231741328574916959 6546409847611992862375439)
              ·
                refine ⟨9819614771417989293563159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546409847611992862375439 9819614771417989293563159)
                ·
                  refine ⟨14729422157126983940344739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9819614771417989293563159 14729422157126983940344739)
                  ·
                    refine ⟨22094133235690475910517109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14729422157126983940344739 22094133235690475910517109)
                    ·
                      refine ⟨2071324990845982116610979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22094133235690475910517109 2071324990845982116610979)
                      ·
                        rfl

theorem cell23_4033891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_4033891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033891 prefixEnd_4033891 := by exact prefixLift 4033891
  have htrace : WordTrace (prefixWord ++ tailWord_4033891) baseStart_4033891 baseEnd_4033891 := by
    simpa [prefixWord, tailWord_4033891, baseEnd_4033891] using wordTrace_append hprefix tailTrace_4033891
  have hstable : (prefixWord ++ tailWord_4033891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033891).length < 2 ^ (prefixWord ++ tailWord_4033891).sum := by decide
  have hdescent : baseEnd_4033891 < baseStart_4033891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033897 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 6]
def baseStart_4033897 : Nat := 118140960795 + 4033897 * 2 ^ 59
def prefixEnd_4033897 : Nat := 4983230072969 + 3 ^ 40 * 4033897 * 2
def baseEnd_4033897 : Nat := 2071328071729909093135951

theorem tailTrace_4033897 : CollatzResearch.WordTrace tailWord_4033897 prefixEnd_4033897 2071328071729909093135951 := by
  unfold tailWord_4033897
  simp only [CollatzResearch.WordTrace]
  refine ⟨147128310666887578603811945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98085540444591719069207963 147128310666887578603811945)
  ·
    refine ⟨110346233000165683952858959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147128310666887578603811945 110346233000165683952858959)
    ·
      refine ⟨165519349500248525929288439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110346233000165683952858959 165519349500248525929288439)
      ·
        refine ⟨248279024250372788893932659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165519349500248525929288439 248279024250372788893932659)
        ·
          refine ⟨372418536375559183340898989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248279024250372788893932659 372418536375559183340898989)
          ·
            refine ⟨139656951140834693752837121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372418536375559183340898989 139656951140834693752837121)
            ·
              refine ⟨104742713355626020314627841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139656951140834693752837121 104742713355626020314627841)
              ·
                refine ⟨78557035016719515235970881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104742713355626020314627841 78557035016719515235970881)
                ·
                  refine ⟨58917776262539636426978161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78557035016719515235970881 58917776262539636426978161)
                  ·
                    refine ⟨44188332196904727320233621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58917776262539636426978161 44188332196904727320233621)
                    ·
                      refine ⟨2071328071729909093135951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44188332196904727320233621 2071328071729909093135951)
                      ·
                        rfl

theorem cell23_4033897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_4033897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033897 prefixEnd_4033897 := by exact prefixLift 4033897
  have htrace : WordTrace (prefixWord ++ tailWord_4033897) baseStart_4033897 baseEnd_4033897 := by
    simpa [prefixWord, tailWord_4033897, baseEnd_4033897] using wordTrace_append hprefix tailTrace_4033897
  have hstable : (prefixWord ++ tailWord_4033897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033897).length < 2 ^ (prefixWord ++ tailWord_4033897).sum := by decide
  have hdescent : baseEnd_4033897 < baseStart_4033897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033904 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_4033904 : Nat := 118140960795 + 4033904 * 2 ^ 59
def prefixEnd_4033904 : Nat := 4983230072969 + 3 ^ 40 * 4033904 * 2
def baseEnd_4033904 : Nat := 2071331666094490565748419

theorem tailTrace_4033904 : CollatzResearch.WordTrace tailWord_4033904 prefixEnd_4033904 2071331666094490565748419 := by
  unfold tailWord_4033904
  simp only [CollatzResearch.WordTrace]
  refine ⟨73564282988931109399658383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98085710651908145866211177 73564282988931109399658383)
  ·
    refine ⟨110346424483396664099487575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73564282988931109399658383 110346424483396664099487575)
    ·
      refine ⟨165519636725094996149231363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110346424483396664099487575 165519636725094996149231363)
      ·
        refine ⟨248279455087642494223847045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165519636725094996149231363 248279455087642494223847045)
        ·
          refine ⟨46552397828932967666971321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248279455087642494223847045 46552397828932967666971321)
          ·
            refine ⟨34914298371699725750228491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46552397828932967666971321 34914298371699725750228491)
            ·
              refine ⟨52371447557549588625342737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34914298371699725750228491 52371447557549588625342737)
              ·
                refine ⟨39278585668162191469007053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52371447557549588625342737 39278585668162191469007053)
                ·
                  refine ⟨14729469625560821800877645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39278585668162191469007053 14729469625560821800877645)
                  ·
                    refine ⟨5523551109585308175329117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14729469625560821800877645 5523551109585308175329117)
                    ·
                      refine ⟨2071331666094490565748419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523551109585308175329117 2071331666094490565748419)
                      ·
                        rfl

theorem cell23_4033904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_4033904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033904 prefixEnd_4033904 := by exact prefixLift 4033904
  have htrace : WordTrace (prefixWord ++ tailWord_4033904) baseStart_4033904 baseEnd_4033904 := by
    simpa [prefixWord, tailWord_4033904, baseEnd_4033904] using wordTrace_append hprefix tailTrace_4033904
  have hstable : (prefixWord ++ tailWord_4033904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033904).length < 2 ^ (prefixWord ++ tailWord_4033904).sum := by decide
  have hdescent : baseEnd_4033904 < baseStart_4033904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033922 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_4033922 : Nat := 118140960795 + 4033922 * 2 ^ 59
def prefixEnd_4033922 : Nat := 4983230072969 + 3 ^ 40 * 4033922 * 2
def baseEnd_4033922 : Nat := 2071340908746271495323337

theorem tailTrace_4033922 : CollatzResearch.WordTrace tailWord_4033922 prefixEnd_4033922 2071340908746271495323337 := by
  unfold tailWord_4033922
  simp only [CollatzResearch.WordTrace]
  refine ⟨36782305622949251968368005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98086148327864671915648013 36782305622949251968368005)
  ·
    refine ⟨6896682304302984744069001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36782305622949251968368005 6896682304302984744069001)
    ·
      refine ⟨5172511728227238558051751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6896682304302984744069001 5172511728227238558051751)
      ·
        refine ⟨7758767592340857837077627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172511728227238558051751 7758767592340857837077627)
        ·
          refine ⟨11638151388511286755616441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758767592340857837077627 11638151388511286755616441)
          ·
            refine ⟨8728613541383465066712331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11638151388511286755616441 8728613541383465066712331)
            ·
              refine ⟨13092920312075197600068497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8728613541383465066712331 13092920312075197600068497)
              ·
                refine ⟨9819690234056398200051373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13092920312075197600068497 9819690234056398200051373)
                ·
                  refine ⟨3682383837771149325019265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9819690234056398200051373 3682383837771149325019265)
                  ·
                    refine ⟨2761787878328361993764449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682383837771149325019265 2761787878328361993764449)
                    ·
                      refine ⟨2071340908746271495323337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761787878328361993764449 2071340908746271495323337)
                      ·
                        rfl

theorem cell23_4033922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_4033922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033922 prefixEnd_4033922 := by exact prefixLift 4033922
  have htrace : WordTrace (prefixWord ++ tailWord_4033922) baseStart_4033922 baseEnd_4033922 := by
    simpa [prefixWord, tailWord_4033922, baseEnd_4033922] using wordTrace_append hprefix tailTrace_4033922
  have hstable : (prefixWord ++ tailWord_4033922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033922).length < 2 ^ (prefixWord ++ tailWord_4033922).sum := by decide
  have hdescent : baseEnd_4033922 < baseStart_4033922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033931 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 3, 3, 2]
def baseStart_4033931 : Nat := 118140960795 + 4033931 * 2 ^ 59
def prefixEnd_4033931 : Nat := 4983230072969 + 3 ^ 40 * 4033931 * 2
def baseEnd_4033931 : Nat := 2071345530072161960110795

theorem tailTrace_4033931 : CollatzResearch.WordTrace tailWord_4033931 prefixEnd_4033931 2071345530072161960110795 := by
  unfold tailWord_4033931
  simp only [CollatzResearch.WordTrace]
  refine ⟨147129550748764402410549647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98086367165842934940366431 147129550748764402410549647)
  ·
    refine ⟨220694326123146603615824471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147129550748764402410549647 220694326123146603615824471)
    ·
      refine ⟨331041489184719905423736707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220694326123146603615824471 331041489184719905423736707)
      ·
        refine ⟨496562233777079858135605061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331041489184719905423736707 496562233777079858135605061)
        ·
          refine ⟨93105418833202473400425949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496562233777079858135605061 93105418833202473400425949)
          ·
            refine ⟨34914532062450927525159731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93105418833202473400425949 34914532062450927525159731)
            ·
              refine ⟨52371798093676391287739597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34914532062450927525159731 52371798093676391287739597)
              ·
                refine ⟨19639424285128646732902349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52371798093676391287739597 19639424285128646732902349)
                ·
                  refine ⟨7364784106923242524838381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19639424285128646732902349 7364784106923242524838381)
                  ·
                    refine ⟨2761794040096215946814393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7364784106923242524838381 2761794040096215946814393)
                    ·
                      refine ⟨2071345530072161960110795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761794040096215946814393 2071345530072161960110795)
                      ·
                        rfl

theorem cell23_4033931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 3, 3, 2].length) (baseStart_4033931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033931 prefixEnd_4033931 := by exact prefixLift 4033931
  have htrace : WordTrace (prefixWord ++ tailWord_4033931) baseStart_4033931 baseEnd_4033931 := by
    simpa [prefixWord, tailWord_4033931, baseEnd_4033931] using wordTrace_append hprefix tailTrace_4033931
  have hstable : (prefixWord ++ tailWord_4033931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033931).length < 2 ^ (prefixWord ++ tailWord_4033931).sum := by decide
  have hdescent : baseEnd_4033931 < baseStart_4033931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033964 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 3]
def baseStart_4033964 : Nat := 118140960795 + 4033964 * 2 ^ 59
def prefixEnd_4033964 : Nat := 4983230072969 + 3 ^ 40 * 4033964 * 2
def baseEnd_4033964 : Nat := 2071362474933760330998143

theorem tailTrace_4033964 : CollatzResearch.WordTrace tailWord_4033964 prefixEnd_4033964 2071362474933760330998143 := by
  unfold tailWord_4033964
  simp only [CollatzResearch.WordTrace]
  refine ⟨73565377178822424523250473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98087169571763232697667297 73565377178822424523250473)
  ·
    refine ⟨55174032884116818392437855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73565377178822424523250473 55174032884116818392437855)
    ·
      refine ⟨82761049326175227588656783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55174032884116818392437855 82761049326175227588656783)
      ·
        refine ⟨124141573989262841382985175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82761049326175227588656783 124141573989262841382985175)
        ·
          refine ⟨186212360983894262074477763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124141573989262841382985175 186212360983894262074477763)
          ·
            refine ⟨279318541475841393111716645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186212360983894262074477763 279318541475841393111716645)
            ·
              refine ⟨52372226526720261208446871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279318541475841393111716645 52372226526720261208446871)
              ·
                refine ⟨78558339790080391812670307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52372226526720261208446871 78558339790080391812670307)
                ·
                  refine ⟨117837509685120587719005461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78558339790080391812670307 117837509685120587719005461)
                  ·
                    refine ⟨5523633266490027549328381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117837509685120587719005461 5523633266490027549328381)
                    ·
                      refine ⟨2071362474933760330998143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523633266490027549328381 2071362474933760330998143)
                      ·
                        rfl

theorem cell23_4033964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_4033964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033964 prefixEnd_4033964 := by exact prefixLift 4033964
  have htrace : WordTrace (prefixWord ++ tailWord_4033964) baseStart_4033964 baseEnd_4033964 := by
    simpa [prefixWord, tailWord_4033964, baseEnd_4033964] using wordTrace_append hprefix tailTrace_4033964
  have hstable : (prefixWord ++ tailWord_4033964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033964).length < 2 ^ (prefixWord ++ tailWord_4033964).sum := by decide
  have hdescent : baseEnd_4033964 < baseStart_4033964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4033984 : List Nat := [2, 1, 1, 2, 3, 1, 4, 2, 7]
def baseStart_4033984 : Nat := 118140960795 + 4033984 * 2 ^ 59
def prefixEnd_4033984 : Nat := 4983230072969 + 3 ^ 40 * 4033984 * 2
def baseEnd_4033984 : Nat := 230152527171872250305339

theorem tailTrace_4033984 : CollatzResearch.WordTrace tailWord_4033984 prefixEnd_4033984 230152527171872250305339 := by
  unfold tailWord_4033984
  simp only [CollatzResearch.WordTrace]
  refine ⟨73565741908786196231114503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98087655878381594974819337 73565741908786196231114503)
  ·
    refine ⟨110348612863179294346671755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73565741908786196231114503 110348612863179294346671755)
    ·
      refine ⟨165522919294768941520007633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110348612863179294346671755 165522919294768941520007633)
      ·
        refine ⟨124142189471076706140005725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165522919294768941520007633 124142189471076706140005725)
        ·
          refine ⟨46553321051653764802502147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124142189471076706140005725 46553321051653764802502147)
          ·
            refine ⟨69829981577480647203753221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46553321051653764802502147 69829981577480647203753221)
            ·
              refine ⟨13093121545777621350703729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69829981577480647203753221 13093121545777621350703729)
              ·
                refine ⟨9819841159333216013027797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093121545777621350703729 9819841159333216013027797)
                ·
                  refine ⟨230152527171872250305339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9819841159333216013027797 230152527171872250305339)
                  ·
                    rfl

theorem cell23_4033984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_4033984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4033984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4033984 prefixEnd_4033984 := by exact prefixLift 4033984
  have htrace : WordTrace (prefixWord ++ tailWord_4033984) baseStart_4033984 baseEnd_4033984 := by
    simpa [prefixWord, tailWord_4033984, baseEnd_4033984] using wordTrace_append hprefix tailTrace_4033984
  have hstable : (prefixWord ++ tailWord_4033984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4033984).length < 2 ^ (prefixWord ++ tailWord_4033984).sum := by decide
  have hdescent : baseEnd_4033984 < baseStart_4033984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4033984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034044 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 2, 8]
def baseStart_4034044 : Nat := 118140960795 + 4034044 * 2 ^ 59
def prefixEnd_4034044 : Nat := 4983230072969 + 3 ^ 40 * 4034044 * 2
def baseEnd_4034044 : Nat := 690467851128706672665925

theorem tailTrace_4034044 : CollatzResearch.WordTrace tailWord_4034044 prefixEnd_4034044 690467851128706672665925 := by
  unfold tailWord_4034044
  simp only [CollatzResearch.WordTrace]
  refine ⟨73566836098677511354706593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98089114798236681806275457 73566836098677511354706593)
  ·
    refine ⟨55175127074008133516029945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73566836098677511354706593 55175127074008133516029945)
    ·
      refine ⟨41381345305506100137022459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55175127074008133516029945 41381345305506100137022459)
      ·
        refine ⟨62072017958259150205533689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41381345305506100137022459 62072017958259150205533689)
        ·
          refine ⟨46554013468694362654150267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62072017958259150205533689 46554013468694362654150267)
          ·
            refine ⟨69831020203041543981225401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46554013468694362654150267 69831020203041543981225401)
            ·
              refine ⟨52373265152281157985919051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69831020203041543981225401 52373265152281157985919051)
              ·
                refine ⟨78559897728421736978878577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52373265152281157985919051 78559897728421736978878577)
                ·
                  refine ⟨58919923296316302734158933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78559897728421736978878577 58919923296316302734158933)
                  ·
                    refine ⟨690467851128706672665925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58919923296316302734158933 690467851128706672665925)
                    ·
                      rfl

theorem cell23_4034044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_4034044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034044 prefixEnd_4034044 := by exact prefixLift 4034044
  have htrace : WordTrace (prefixWord ++ tailWord_4034044) baseStart_4034044 baseEnd_4034044 := by
    simpa [prefixWord, tailWord_4034044, baseEnd_4034044] using wordTrace_append hprefix tailTrace_4034044
  have hstable : (prefixWord ++ tailWord_4034044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034044).length < 2 ^ (prefixWord ++ tailWord_4034044).sum := by decide
  have hdescent : baseEnd_4034044 < baseStart_4034044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034051 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 3, 6, 2]
def baseStart_4034051 : Nat := 118140960795 + 4034051 * 2 ^ 59
def prefixEnd_4034051 : Nat := 4983230072969 + 3 ^ 40 * 4034051 * 2
def baseEnd_4034051 : Nat := 2071407147750701490610243

theorem tailTrace_4034051 : CollatzResearch.WordTrace tailWord_4034051 prefixEnd_4034051 2071407147750701490610243 := by
  unfold tailWord_4034051
  simp only [CollatzResearch.WordTrace]
  refine ⟨147133927508329662904918007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98089285005553108603278671 147133927508329662904918007)
  ·
    refine ⟨220700891262494494357377011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147133927508329662904918007 220700891262494494357377011)
    ·
      refine ⟨331051336893741741536065517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220700891262494494357377011 331051336893741741536065517)
      ·
        refine ⟨124144251335153153076024569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331051336893741741536065517 124144251335153153076024569)
        ·
          refine ⟨93108188501364864807018427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124144251335153153076024569 93108188501364864807018427)
          ·
            refine ⟨139662282752047297210527641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93108188501364864807018427 139662282752047297210527641)
            ·
              refine ⟨104746712064035472907895731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139662282752047297210527641 104746712064035472907895731)
              ·
                refine ⟨157120068096053209361843597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104746712064035472907895731 157120068096053209361843597)
                ·
                  refine ⟨58920025536019953510691349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157120068096053209361843597 58920025536019953510691349)
                  ·
                    refine ⟨2761876197000935320813657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58920025536019953510691349 2761876197000935320813657)
                    ·
                      refine ⟨2071407147750701490610243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761876197000935320813657 2071407147750701490610243)
                      ·
                        rfl

theorem cell23_4034051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_4034051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034051 prefixEnd_4034051 := by exact prefixLift 4034051
  have htrace : WordTrace (prefixWord ++ tailWord_4034051) baseStart_4034051 baseEnd_4034051 := by
    simpa [prefixWord, tailWord_4034051, baseEnd_4034051] using wordTrace_append hprefix tailTrace_4034051
  have hstable : (prefixWord ++ tailWord_4034051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034051).length < 2 ^ (prefixWord ++ tailWord_4034051).sum := by decide
  have hdescent : baseEnd_4034051 < baseStart_4034051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034102 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4034102 : Nat := 118140960795 + 4034102 * 2 ^ 59
def prefixEnd_4034102 : Nat := 4983230072969 + 3 ^ 40 * 4034102 * 2
def baseEnd_4034102 : Nat := 2071433335264080791072509

theorem tailTrace_4034102 : CollatzResearch.WordTrace tailWord_4034102 prefixEnd_4034102 2071433335264080791072509 := by
  unfold tailWord_4034102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195986726946556163439035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98090525087429932410016373 9195986726946556163439035)
  ·
    refine ⟨13793980090419834245158553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195986726946556163439035 13793980090419834245158553)
    ·
      refine ⟨10345485067814875683868915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13793980090419834245158553 10345485067814875683868915)
      ·
        refine ⟨15518227601722313525803373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345485067814875683868915 15518227601722313525803373)
        ·
          refine ⟨5819335350645867572176265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15518227601722313525803373 5819335350645867572176265)
          ·
            refine ⟨4364501512984400679132199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5819335350645867572176265 4364501512984400679132199)
            ·
              refine ⟨6546752269476601018698299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364501512984400679132199 6546752269476601018698299)
              ·
                refine ⟨9820128404214901528047449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546752269476601018698299 9820128404214901528047449)
                ·
                  refine ⟨7365096303161176146035587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9820128404214901528047449 7365096303161176146035587)
                  ·
                    refine ⟨11047644454741764219053381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7365096303161176146035587 11047644454741764219053381)
                    ·
                      refine ⟨2071433335264080791072509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11047644454741764219053381 2071433335264080791072509)
                      ·
                        rfl

theorem cell23_4034102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4034102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034102 prefixEnd_4034102 := by exact prefixLift 4034102
  have htrace : WordTrace (prefixWord ++ tailWord_4034102) baseStart_4034102 baseEnd_4034102 := by
    simpa [prefixWord, tailWord_4034102, baseEnd_4034102] using wordTrace_append hprefix tailTrace_4034102
  have hstable : (prefixWord ++ tailWord_4034102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034102).length < 2 ^ (prefixWord ++ tailWord_4034102).sum := by decide
  have hdescent : baseEnd_4034102 < baseStart_4034102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034105 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4034105 : Nat := 118140960795 + 4034105 * 2 ^ 59
def prefixEnd_4034105 : Nat := 4983230072969 + 3 ^ 40 * 4034105 * 2
def baseEnd_4034105 : Nat := 2071434875706044279334995

theorem tailTrace_4034105 : CollatzResearch.WordTrace tailWord_4034105 prefixEnd_4034105 2071434875706044279334995 := by
  unfold tailWord_4034105
  simp only [CollatzResearch.WordTrace]
  refine ⟨147135897050134030127383769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98090598033422686751589179 147135897050134030127383769)
  ·
    refine ⟨110351922787600522595537827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147135897050134030127383769 110351922787600522595537827)
    ·
      refine ⟨165527884181400783893306741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110351922787600522595537827 165527884181400783893306741)
      ·
        refine ⟨15518239142006323489997507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165527884181400783893306741 15518239142006323489997507)
        ·
          refine ⟨23277358713009485234996261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15518239142006323489997507 23277358713009485234996261)
          ·
            refine ⟨4364504758689278481561799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23277358713009485234996261 4364504758689278481561799)
            ·
              refine ⟨6546757138033917722342699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364504758689278481561799 6546757138033917722342699)
              ·
                refine ⟨9820135707050876583514049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546757138033917722342699 9820135707050876583514049)
                ·
                  refine ⟨7365101780288157437635537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9820135707050876583514049 7365101780288157437635537)
                  ·
                    refine ⟨5523826335216118078226653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365101780288157437635537 5523826335216118078226653)
                    ·
                      refine ⟨2071434875706044279334995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523826335216118078226653 2071434875706044279334995)
                      ·
                        rfl

theorem cell23_4034105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4034105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034105 prefixEnd_4034105 := by exact prefixLift 4034105
  have htrace : WordTrace (prefixWord ++ tailWord_4034105) baseStart_4034105 baseEnd_4034105 := by
    simpa [prefixWord, tailWord_4034105, baseEnd_4034105] using wordTrace_append hprefix tailTrace_4034105
  have hstable : (prefixWord ++ tailWord_4034105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034105).length < 2 ^ (prefixWord ++ tailWord_4034105).sum := by decide
  have hdescent : baseEnd_4034105 < baseStart_4034105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034128 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2]
def baseStart_4034128 : Nat := 118140960795 + 4034128 * 2 ^ 59
def prefixEnd_4034128 : Nat := 4983230072969 + 3 ^ 40 * 4034128 * 2
def baseEnd_4034128 : Nat := 2071446685761097689347389

theorem tailTrace_4034128 : CollatzResearch.WordTrace tailWord_4034128 prefixEnd_4034128 2071446685761097689347389 := by
  unfold tailWord_4034128
  simp only [CollatzResearch.WordTrace]
  refine ⟨73568367964525352527735519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98091157286033803370314025 73568367964525352527735519)
  ·
    refine ⟨110352551946788028791603279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73568367964525352527735519 110352551946788028791603279)
    ·
      refine ⟨165528827920182043187404919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110352551946788028791603279 165528827920182043187404919)
      ·
        refine ⟨248293241880273064781107379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165528827920182043187404919 248293241880273064781107379)
        ·
          refine ⟨372439862820409597171661069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248293241880273064781107379 372439862820409597171661069)
          ·
            refine ⟨139664948557653598939372901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372439862820409597171661069 139664948557653598939372901)
            ·
              refine ⟨26187177854560049801132419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139664948557653598939372901 26187177854560049801132419)
              ·
                refine ⟨39280766781840074701698629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26187177854560049801132419 39280766781840074701698629)
                ·
                  refine ⟨7365143771595014006568493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39280766781840074701698629 7365143771595014006568493)
                  ·
                    refine ⟨2761928914348130252463185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7365143771595014006568493 2761928914348130252463185)
                    ·
                      refine ⟨2071446685761097689347389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761928914348130252463185 2071446685761097689347389)
                      ·
                        rfl

theorem cell23_4034128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 4, 3, 2].length) (baseStart_4034128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034128 prefixEnd_4034128 := by exact prefixLift 4034128
  have htrace : WordTrace (prefixWord ++ tailWord_4034128) baseStart_4034128 baseEnd_4034128 := by
    simpa [prefixWord, tailWord_4034128, baseEnd_4034128] using wordTrace_append hprefix tailTrace_4034128
  have hstable : (prefixWord ++ tailWord_4034128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034128).length < 2 ^ (prefixWord ++ tailWord_4034128).sum := by decide
  have hdescent : baseEnd_4034128 < baseStart_4034128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034135 : List Nat := [1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_4034135 : Nat := 118140960795 + 4034135 * 2 ^ 59
def prefixEnd_4034135 : Nat := 4983230072969 + 3 ^ 40 * 4034135 * 2
def baseEnd_4034135 : Nat := 2071450280125679161959857

theorem tailTrace_4034135 : CollatzResearch.WordTrace tailWord_4034135 prefixEnd_4034135 2071450280125679161959857 := by
  unfold tailWord_4034135
  simp only [CollatzResearch.WordTrace]
  refine ⟨147136991240025345250975859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98091327493350230167317239 147136991240025345250975859)
  ·
    refine ⟨220705486860038017876463789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147136991240025345250975859 220705486860038017876463789)
    ·
      refine ⟨82764557572514256703673921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220705486860038017876463789 82764557572514256703673921)
      ·
        refine ⟨62073418179385692527755441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82764557572514256703673921 62073418179385692527755441)
        ·
          refine ⟨46555063634539269395816581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62073418179385692527755441 46555063634539269395816581)
          ·
            refine ⟨8729074431476113011715609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46555063634539269395816581 8729074431476113011715609)
            ·
              refine ⟨6546805823607084758786707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8729074431476113011715609 6546805823607084758786707)
              ·
                refine ⟨9820208735410627138180061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546805823607084758786707 9820208735410627138180061)
                ·
                  refine ⟨3682578275778985176817523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9820208735410627138180061 3682578275778985176817523)
                  ·
                    refine ⟨5523867413668477765226285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682578275778985176817523 5523867413668477765226285)
                    ·
                      refine ⟨2071450280125679161959857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523867413668477765226285 2071450280125679161959857)
                      ·
                        rfl

theorem cell23_4034135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_4034135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034135 prefixEnd_4034135 := by exact prefixLift 4034135
  have htrace : WordTrace (prefixWord ++ tailWord_4034135) baseStart_4034135 baseEnd_4034135 := by
    simpa [prefixWord, tailWord_4034135, baseEnd_4034135] using wordTrace_append hprefix tailTrace_4034135
  have hstable : (prefixWord ++ tailWord_4034135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034135).length < 2 ^ (prefixWord ++ tailWord_4034135).sum := by decide
  have hdescent : baseEnd_4034135 < baseStart_4034135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034161 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 3]
def baseStart_4034161 : Nat := 118140960795 + 4034161 * 2 ^ 59
def prefixEnd_4034161 : Nat := 4983230072969 + 3 ^ 40 * 4034161 * 2
def baseEnd_4034161 : Nat := 2071463630622696060234737

theorem tailTrace_4034161 : CollatzResearch.WordTrace tailWord_4034161 prefixEnd_4034161 2071463630622696060234737 := by
  unfold tailWord_4034161
  simp only [CollatzResearch.WordTrace]
  refine ⟨147137939537931151691422337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98091959691954101127614891 147137939537931151691422337)
  ·
    refine ⟨110353454653448363768566753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147137939537931151691422337 110353454653448363768566753)
    ·
      refine ⟨82765090990086272826425065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110353454653448363768566753 82765090990086272826425065)
      ·
        refine ⟨62073818242564704619818799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82765090990086272826425065 62073818242564704619818799)
        ·
          refine ⟨93110727363847056929728199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62073818242564704619818799 93110727363847056929728199)
          ·
            refine ⟨139666091045770585394592299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93110727363847056929728199 139666091045770585394592299)
            ·
              refine ⟨209499136568655878091888449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139666091045770585394592299 209499136568655878091888449)
              ·
                refine ⟨157124352426491908568916337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209499136568655878091888449 157124352426491908568916337)
                ·
                  refine ⟨117843264319868931426687253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157124352426491908568916337 117843264319868931426687253)
                  ·
                    refine ⟨5523903014993856160625965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117843264319868931426687253 5523903014993856160625965)
                    ·
                      refine ⟨2071463630622696060234737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523903014993856160625965 2071463630622696060234737)
                      ·
                        rfl

theorem cell23_4034161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_4034161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034161 prefixEnd_4034161 := by exact prefixLift 4034161
  have htrace : WordTrace (prefixWord ++ tailWord_4034161) baseStart_4034161 baseEnd_4034161 := by
    simpa [prefixWord, tailWord_4034161, baseEnd_4034161] using wordTrace_append hprefix tailTrace_4034161
  have hstable : (prefixWord ++ tailWord_4034161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034161).length < 2 ^ (prefixWord ++ tailWord_4034161).sum := by decide
  have hdescent : baseEnd_4034161 < baseStart_4034161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034171 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4]
def baseStart_4034171 : Nat := 118140960795 + 4034171 * 2 ^ 59
def prefixEnd_4034171 : Nat := 4983230072969 + 3 ^ 40 * 4034171 * 2
def baseEnd_4034171 : Nat := 2071468765429241021109691

theorem tailTrace_4034171 : CollatzResearch.WordTrace tailWord_4034171 prefixEnd_4034171 2071468765429241021109691 := by
  unfold tailWord_4034171
  simp only [CollatzResearch.WordTrace]
  refine ⟨147138304267894923399286367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98092202845263282266190911 147138304267894923399286367)
  ·
    refine ⟨220707456401842385098929551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147138304267894923399286367 220707456401842385098929551)
    ·
      refine ⟨331061184602763577648394327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220707456401842385098929551 331061184602763577648394327)
      ·
        refine ⟨496591776904145366472591491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331061184602763577648394327 496591776904145366472591491)
        ·
          refine ⟨744887665356218049708887237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496591776904145366472591491 744887665356218049708887237)
          ·
            refine ⟨139666437254290884320416357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 744887665356218049708887237 139666437254290884320416357)
            ·
              refine ⟨26187456985179540810078067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139666437254290884320416357 26187456985179540810078067)
              ·
                refine ⟨39281185477769311215117101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26187456985179540810078067 39281185477769311215117101)
                ·
                  refine ⟨14730444554163491705668913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39281185477769311215117101 14730444554163491705668913)
                  ·
                    refine ⟨11047833415622618779251685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14730444554163491705668913 11047833415622618779251685)
                    ·
                      refine ⟨2071468765429241021109691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11047833415622618779251685 2071468765429241021109691)
                      ·
                        rfl

theorem cell23_4034171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 2, 4].length) (baseStart_4034171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034171 prefixEnd_4034171 := by exact prefixLift 4034171
  have htrace : WordTrace (prefixWord ++ tailWord_4034171) baseStart_4034171 baseEnd_4034171 := by
    simpa [prefixWord, tailWord_4034171, baseEnd_4034171] using wordTrace_append hprefix tailTrace_4034171
  have hstable : (prefixWord ++ tailWord_4034171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034171).length < 2 ^ (prefixWord ++ tailWord_4034171).sum := by decide
  have hdescent : baseEnd_4034171 < baseStart_4034171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034191 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3]
def baseStart_4034191 : Nat := 118140960795 + 4034191 * 2 ^ 59
def prefixEnd_4034191 : Nat := 4983230072969 + 3 ^ 40 * 4034191 * 2
def baseEnd_4034191 : Nat := 2071479035042330942859599

theorem tailTrace_4034191 : CollatzResearch.WordTrace tailWord_4034191 prefixEnd_4034191 2071479035042330942859599 := by
  unfold tailWord_4034191
  simp only [CollatzResearch.WordTrace]
  refine ⟨147139033727822466815014427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98092689151881644543342951 147139033727822466815014427)
  ·
    refine ⟨220708550591733700222521641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147139033727822466815014427 220708550591733700222521641)
    ·
      refine ⟨165531412943800275166891231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220708550591733700222521641 165531412943800275166891231)
      ·
        refine ⟨248297119415700412750336847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165531412943800275166891231 248297119415700412750336847)
        ·
          refine ⟨372445679123550619125505271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248297119415700412750336847 372445679123550619125505271)
          ·
            refine ⟨558668518685325928688257907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372445679123550619125505271 558668518685325928688257907)
            ·
              refine ⟨838002778027988893032386861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558668518685325928688257907 838002778027988893032386861)
              ·
                refine ⟨314251041760495834887145073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 838002778027988893032386861 314251041760495834887145073)
                ·
                  refine ⟨235688281320371876165358805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314251041760495834887145073 235688281320371876165358805)
                  ·
                    refine ⟨5523944093446215847625597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235688281320371876165358805 5523944093446215847625597)
                    ·
                      refine ⟨2071479035042330942859599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523944093446215847625597 2071479035042330942859599)
                      ·
                        rfl

theorem cell23_4034191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_4034191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034191 prefixEnd_4034191 := by exact prefixLift 4034191
  have htrace : WordTrace (prefixWord ++ tailWord_4034191) baseStart_4034191 baseEnd_4034191 := by
    simpa [prefixWord, tailWord_4034191, baseEnd_4034191] using wordTrace_append hprefix tailTrace_4034191
  have hstable : (prefixWord ++ tailWord_4034191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034191).length < 2 ^ (prefixWord ++ tailWord_4034191).sum := by decide
  have hdescent : baseEnd_4034191 < baseStart_4034191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034192 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 1, 2, 2]
def baseStart_4034192 : Nat := 118140960795 + 4034192 * 2 ^ 59
def prefixEnd_4034192 : Nat := 4983230072969 + 3 ^ 40 * 4034192 * 2
def baseEnd_4034192 : Nat := 2071479548522985438947095

theorem tailTrace_4034192 : CollatzResearch.WordTrace tailWord_4034192 prefixEnd_4034192 2071479548522985438947095 := by
  unfold tailWord_4034192
  simp only [CollatzResearch.WordTrace]
  refine ⟨73569535100409421992900415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98092713467212562657200553 73569535100409421992900415)
  ·
    refine ⟨110354302650614132989350623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73569535100409421992900415 110354302650614132989350623)
    ·
      refine ⟨165531453975921199484025935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110354302650614132989350623 165531453975921199484025935)
      ·
        refine ⟨248297180963881799226038903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165531453975921199484025935 248297180963881799226038903)
        ·
          refine ⟨372445771445822698839058355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248297180963881799226038903 372445771445822698839058355)
          ·
            refine ⟨558668657168734048258587533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372445771445822698839058355 558668657168734048258587533)
            ·
              refine ⟨209500746438275268096970325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558668657168734048258587533 209500746438275268096970325)
              ·
                refine ⟨2455086872323538298011371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 209500746438275268096970325 2455086872323538298011371)
                ·
                  refine ⟨3682630308485307447017057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455086872323538298011371 3682630308485307447017057)
                  ·
                    refine ⟨2761972731363980585262793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682630308485307447017057 2761972731363980585262793)
                    ·
                      refine ⟨2071479548522985438947095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2761972731363980585262793 2071479548522985438947095)
                      ·
                        rfl

theorem cell23_4034192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 1, 2, 2].length) (baseStart_4034192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034192 prefixEnd_4034192 := by exact prefixLift 4034192
  have htrace : WordTrace (prefixWord ++ tailWord_4034192) baseStart_4034192 baseEnd_4034192 := by
    simpa [prefixWord, tailWord_4034192, baseEnd_4034192] using wordTrace_append hprefix tailTrace_4034192
  have hstable : (prefixWord ++ tailWord_4034192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034192).length < 2 ^ (prefixWord ++ tailWord_4034192).sum := by decide
  have hdescent : baseEnd_4034192 < baseStart_4034192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034212 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 1, 2, 3]
def baseStart_4034212 : Nat := 118140960795 + 4034212 * 2 ^ 59
def prefixEnd_4034212 : Nat := 4983230072969 + 3 ^ 40 * 4034212 * 2
def baseEnd_4034212 : Nat := 2071489818136075360697003

theorem tailTrace_4034212 : CollatzResearch.WordTrace tailWord_4034212 prefixEnd_4034212 2071489818136075360697003 := by
  unfold tailWord_4034212
  simp only [CollatzResearch.WordTrace]
  refine ⟨73569899830373193700764445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98093199773830924934352593 73569899830373193700764445)
  ·
    refine ⟨27588712436389947637786667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73569899830373193700764445 27588712436389947637786667)
    ·
      refine ⟨41383068654584921456680001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27588712436389947637786667 41383068654584921456680001)
      ·
        refine ⟨31037301490938691092510001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41383068654584921456680001 31037301490938691092510001)
        ·
          refine ⟨23277976118204018319382501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31037301490938691092510001 23277976118204018319382501)
          ·
            refine ⟨4364620522163253434884219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23277976118204018319382501 4364620522163253434884219)
            ·
              refine ⟨6546930783244880152326329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364620522163253434884219 6546930783244880152326329)
              ·
                refine ⟨4910198087433660114244747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6546930783244880152326329 4910198087433660114244747)
                ·
                  refine ⟨7365297131150490171367121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910198087433660114244747 7365297131150490171367121)
                  ·
                    refine ⟨5523972848362867628525341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365297131150490171367121 5523972848362867628525341)
                    ·
                      refine ⟨2071489818136075360697003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523972848362867628525341 2071489818136075360697003)
                      ·
                        rfl

theorem cell23_4034212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_4034212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034212 prefixEnd_4034212 := by exact prefixLift 4034212
  have htrace : WordTrace (prefixWord ++ tailWord_4034212) baseStart_4034212 baseEnd_4034212 := by
    simpa [prefixWord, tailWord_4034212, baseEnd_4034212] using wordTrace_append hprefix tailTrace_4034212
  have hstable : (prefixWord ++ tailWord_4034212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034212).length < 2 ^ (prefixWord ++ tailWord_4034212).sum := by decide
  have hdescent : baseEnd_4034212 < baseStart_4034212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034222 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4034222 : Nat := 118140960795 + 4034222 * 2 ^ 59
def prefixEnd_4034222 : Nat := 4983230072969 + 3 ^ 40 * 4034222 * 2
def baseEnd_4034222 : Nat := 2071494952942620321571957

theorem tailTrace_4034222 : CollatzResearch.WordTrace tailWord_4034222 prefixEnd_4034222 2071494952942620321571957 := by
  unfold tailWord_4034222
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392520548838769888674115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98093442927140106072928613 18392520548838769888674115)
  ·
    refine ⟨27588780823258154833011173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18392520548838769888674115 27588780823258154833011173)
    ·
      refine ⟨5172896404360904031189595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27588780823258154833011173 5172896404360904031189595)
      ·
        refine ⟨7759344606541356046784393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172896404360904031189595 7759344606541356046784393)
        ·
          refine ⟨5819508454906017035088295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7759344606541356046784393 5819508454906017035088295)
          ·
            refine ⟨8729262682359025552632443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819508454906017035088295 8729262682359025552632443)
            ·
              refine ⟨13093894023538538328948665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729262682359025552632443 13093894023538538328948665)
              ·
                refine ⟨9820420517653903746711499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13093894023538538328948665 9820420517653903746711499)
                ·
                  refine ⟨14730630776480855620067249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820420517653903746711499 14730630776480855620067249)
                  ·
                    refine ⟨11047973082360641715050437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14730630776480855620067249 11047973082360641715050437)
                    ·
                      refine ⟨2071494952942620321571957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11047973082360641715050437 2071494952942620321571957)
                      ·
                        rfl

theorem cell23_4034222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4034222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034222 prefixEnd_4034222 := by exact prefixLift 4034222
  have htrace : WordTrace (prefixWord ++ tailWord_4034222) baseStart_4034222 baseEnd_4034222 := by
    simpa [prefixWord, tailWord_4034222, baseEnd_4034222] using wordTrace_append hprefix tailTrace_4034222
  have hstable : (prefixWord ++ tailWord_4034222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034222).length < 2 ^ (prefixWord ++ tailWord_4034222).sum := by decide
  have hdescent : baseEnd_4034222 < baseStart_4034222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034229 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4034229 : Nat := 118140960795 + 4034229 * 2 ^ 59
def prefixEnd_4034229 : Nat := 4983230072969 + 3 ^ 40 * 4034229 * 2
def baseEnd_4034229 : Nat := 2071498547307201794184425

theorem tailTrace_4034229 : CollatzResearch.WordTrace tailWord_4034229 prefixEnd_4034229 2071498547307201794184425 := by
  unfold tailWord_4034229
  simp only [CollatzResearch.WordTrace]
  refine ⟨147140419701684799304897741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98093613134456532869931827 147140419701684799304897741)
  ·
    refine ⟨55177657388131799739336653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147140419701684799304897741 55177657388131799739336653)
    ·
      refine ⟨20691621520549424902251245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55177657388131799739336653 20691621520549424902251245)
      ·
        refine ⟨7759358070206034338344217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20691621520549424902251245 7759358070206034338344217)
        ·
          refine ⟨5819518552654525753758163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7759358070206034338344217 5819518552654525753758163)
          ·
            refine ⟨8729277828981788630637245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819518552654525753758163 8729277828981788630637245)
            ·
              refine ⟨3273479185868170736488967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8729277828981788630637245 3273479185868170736488967)
              ·
                refine ⟨4910218778802256104733451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273479185868170736488967 4910218778802256104733451)
                ·
                  refine ⟨7365328168203384157100177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910218778802256104733451 7365328168203384157100177)
                  ·
                    refine ⟨5523996126152538117825133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7365328168203384157100177 5523996126152538117825133)
                    ·
                      refine ⟨2071498547307201794184425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5523996126152538117825133 2071498547307201794184425)
                      ·
                        rfl

theorem cell23_4034229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4034229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034229 prefixEnd_4034229 := by exact prefixLift 4034229
  have htrace : WordTrace (prefixWord ++ tailWord_4034229) baseStart_4034229 baseEnd_4034229 := by
    simpa [prefixWord, tailWord_4034229, baseEnd_4034229] using wordTrace_append hprefix tailTrace_4034229
  have hstable : (prefixWord ++ tailWord_4034229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034229).length < 2 ^ (prefixWord ++ tailWord_4034229).sum := by decide
  have hdescent : baseEnd_4034229 < baseStart_4034229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034235 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 1, 3, 2]
def baseStart_4034235 : Nat := 118140960795 + 4034235 * 2 ^ 59
def prefixEnd_4034235 : Nat := 4983230072969 + 3 ^ 40 * 4034235 * 2
def baseEnd_4034235 : Nat := 2071501628191128770709397

theorem tailTrace_4034235 : CollatzResearch.WordTrace tailWord_4034235 prefixEnd_4034235 2071501628191128770709397 := by
  unfold tailWord_4034235
  simp only [CollatzResearch.WordTrace]
  refine ⟨147140638539663062329616159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98093759026442041553077439 147140638539663062329616159)
  ·
    refine ⟨220710957809494593494424239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147140638539663062329616159 220710957809494593494424239)
    ·
      refine ⟨331066436714241890241636359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220710957809494593494424239 331066436714241890241636359)
      ·
        refine ⟨496599655071362835362454539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331066436714241890241636359 496599655071362835362454539)
        ·
          refine ⟨744899482607044253043681809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496599655071362835362454539 744899482607044253043681809)
          ·
            refine ⟨558674611955283189782761357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744899482607044253043681809 558674611955283189782761357)
            ·
              refine ⟨209502979483231196168535509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558674611955283189782761357 209502979483231196168535509)
              ·
                refine ⟨4910226081638231160200051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 209502979483231196168535509 4910226081638231160200051)
                ·
                  refine ⟨7365339122457346740300077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4910226081638231160200051 7365339122457346740300077)
                  ·
                    refine ⟨2762002170921505027612529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7365339122457346740300077 2762002170921505027612529)
                    ·
                      refine ⟨2071501628191128770709397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762002170921505027612529 2071501628191128770709397)
                      ·
                        rfl

theorem cell23_4034235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 1, 3, 2].length) (baseStart_4034235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034235 prefixEnd_4034235 := by exact prefixLift 4034235
  have htrace : WordTrace (prefixWord ++ tailWord_4034235) baseStart_4034235 baseEnd_4034235 := by
    simpa [prefixWord, tailWord_4034235, baseEnd_4034235] using wordTrace_append hprefix tailTrace_4034235
  have hstable : (prefixWord ++ tailWord_4034235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034235).length < 2 ^ (prefixWord ++ tailWord_4034235).sum := by decide
  have hdescent : baseEnd_4034235 < baseStart_4034235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034251 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5]
def baseStart_4034251 : Nat := 118140960795 + 4034251 * 2 ^ 59
def prefixEnd_4034251 : Nat := 4983230072969 + 3 ^ 40 * 4034251 * 2
def baseEnd_4034251 : Nat := 2071509843881600708109323

theorem tailTrace_4034251 : CollatzResearch.WordTrace tailWord_4034251 prefixEnd_4034251 2071509843881600708109323 := by
  unfold tailWord_4034251
  simp only [CollatzResearch.WordTrace]
  refine ⟨147141222107605097062198607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98094148071736731374799071 147141222107605097062198607)
  ·
    refine ⟨220711833161407645593297911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147141222107605097062198607 220711833161407645593297911)
    ·
      refine ⟨331067749742111468389946867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220711833161407645593297911 331067749742111468389946867)
      ·
        refine ⟨496601624613167202584920301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331067749742111468389946867 496601624613167202584920301)
        ·
          refine ⟨186225609229937700969345113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496601624613167202584920301 186225609229937700969345113)
          ·
            refine ⟨139669206922453275727008835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186225609229937700969345113 139669206922453275727008835)
            ·
              refine ⟨209503810383679913590513253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139669206922453275727008835 209503810383679913590513253)
              ·
                refine ⟨39281964446939983798221235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209503810383679913590513253 39281964446939983798221235)
                ·
                  refine ⟨58922946670409975697331853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39281964446939983798221235 58922946670409975697331853)
                  ·
                    refine ⟨22096105001403740886499445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58922946670409975697331853 22096105001403740886499445)
                    ·
                      refine ⟨2071509843881600708109323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22096105001403740886499445 2071509843881600708109323)
                      ·
                        rfl

theorem cell23_4034251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 1, 3, 5].length) (baseStart_4034251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034251 prefixEnd_4034251 := by exact prefixLift 4034251
  have htrace : WordTrace (prefixWord ++ tailWord_4034251) baseStart_4034251 baseEnd_4034251 := by
    simpa [prefixWord, tailWord_4034251, baseEnd_4034251] using wordTrace_append hprefix tailTrace_4034251
  have hstable : (prefixWord ++ tailWord_4034251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034251).length < 2 ^ (prefixWord ++ tailWord_4034251).sum := by decide
  have hdescent : baseEnd_4034251 < baseStart_4034251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034258 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_4034258 : Nat := 118140960795 + 4034258 * 2 ^ 59
def prefixEnd_4034258 : Nat := 4983230072969 + 3 ^ 40 * 4034258 * 2
def baseEnd_4034258 : Nat := 690504479415394060240597

theorem tailTrace_4034258 : CollatzResearch.WordTrace tailWord_4034258 prefixEnd_4034258 690504479415394060240597 := by
  unfold tailWord_4034258
  simp only [CollatzResearch.WordTrace]
  refine ⟨36785369354644934314425857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98094318279053158171802285 36785369354644934314425857)
  ·
    refine ⟨27589027015983700735819393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36785369354644934314425857 27589027015983700735819393)
    ·
      refine ⟨20691770261987775551864545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27589027015983700735819393 20691770261987775551864545)
      ·
        refine ⟨15518827696490831663898409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20691770261987775551864545 15518827696490831663898409)
        ·
          refine ⟨11639120772368123747923807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15518827696490831663898409 11639120772368123747923807)
          ·
            refine ⟨17458681158552185621885711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639120772368123747923807 17458681158552185621885711)
            ·
              refine ⟨26188021737828278432828567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458681158552185621885711 26188021737828278432828567)
              ·
                refine ⟨39282032606742417649242851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26188021737828278432828567 39282032606742417649242851)
                ·
                  refine ⟨58923048910113626473864277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39282032606742417649242851 58923048910113626473864277)
                  ·
                    refine ⟨690504479415394060240597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58923048910113626473864277 690504479415394060240597)
                    ·
                      rfl

theorem cell23_4034258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_4034258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034258 prefixEnd_4034258 := by exact prefixLift 4034258
  have htrace : WordTrace (prefixWord ++ tailWord_4034258) baseStart_4034258 baseEnd_4034258 := by
    simpa [prefixWord, tailWord_4034258, baseEnd_4034258] using wordTrace_append hprefix tailTrace_4034258
  have hstable : (prefixWord ++ tailWord_4034258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034258).length < 2 ^ (prefixWord ++ tailWord_4034258).sum := by decide
  have hdescent : baseEnd_4034258 < baseStart_4034258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034265 : List Nat := [1, 2, 1, 2, 3, 3, 1, 3, 1, 4, 2]
def baseStart_4034265 : Nat := 118140960795 + 4034265 * 2 ^ 59
def prefixEnd_4034265 : Nat := 4983230072969 + 3 ^ 40 * 4034265 * 2
def baseEnd_4034265 : Nat := 2071517032610763653334259

theorem tailTrace_4034265 : CollatzResearch.WordTrace tailWord_4034265 prefixEnd_4034265 2071517032610763653334259 := by
  unfold tailWord_4034265
  simp only [CollatzResearch.WordTrace]
  refine ⟨147141732729554377453208249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98094488486369584968805499 147141732729554377453208249)
  ·
    refine ⟨110356299547165783089906187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147141732729554377453208249 110356299547165783089906187)
    ·
      refine ⟨165534449320748674634859281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110356299547165783089906187 165534449320748674634859281)
      ·
        refine ⟨124150836990561505976144461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165534449320748674634859281 124150836990561505976144461)
        ·
          refine ⟨46556563871460564741054173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124150836990561505976144461 46556563871460564741054173)
          ·
            refine ⟨17458711451797711777895315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46556563871460564741054173 17458711451797711777895315)
            ·
              refine ⟨26188067177696567666842973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458711451797711777895315 26188067177696567666842973)
              ·
                refine ⟨9820525191636212875066115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26188067177696567666842973 9820525191636212875066115)
                ·
                  refine ⟨14730787787454319312599173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820525191636212875066115 14730787787454319312599173)
                  ·
                    refine ⟨2762022710147684871112345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14730787787454319312599173 2762022710147684871112345)
                    ·
                      refine ⟨2071517032610763653334259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762022710147684871112345 2071517032610763653334259)
                      ·
                        rfl

theorem cell23_4034265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 3, 1, 4, 2].length) (baseStart_4034265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034265 prefixEnd_4034265 := by exact prefixLift 4034265
  have htrace : WordTrace (prefixWord ++ tailWord_4034265) baseStart_4034265 baseEnd_4034265 := by
    simpa [prefixWord, tailWord_4034265, baseEnd_4034265] using wordTrace_append hprefix tailTrace_4034265
  have hstable : (prefixWord ++ tailWord_4034265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034265).length < 2 ^ (prefixWord ++ tailWord_4034265).sum := by decide
  have hdescent : baseEnd_4034265 < baseStart_4034265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034281 : List Nat := [1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 7]
def baseStart_4034281 : Nat := 118140960795 + 4034281 * 2 ^ 59
def prefixEnd_4034281 : Nat := 4983230072969 + 3 ^ 40 * 4034281 * 2
def baseEnd_4034281 : Nat := 2071525248301235590734185

theorem tailTrace_4034281 : CollatzResearch.WordTrace tailWord_4034281 prefixEnd_4034281 2071525248301235590734185 := by
  unfold tailWord_4034281
  simp only [CollatzResearch.WordTrace]
  refine ⟨147142316297496412185790697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98094877531664274790527131 147142316297496412185790697)
  ·
    refine ⟨110356737223122309139343023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147142316297496412185790697 110356737223122309139343023)
    ·
      refine ⟨165535105834683463709014535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110356737223122309139343023 165535105834683463709014535)
      ·
        refine ⟨248302658752025195563521803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165535105834683463709014535 248302658752025195563521803)
        ·
          refine ⟨372453988128037793345282705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248302658752025195563521803 372453988128037793345282705)
          ·
            refine ⟨279340491096028345008962029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372453988128037793345282705 279340491096028345008962029)
            ·
              refine ⟨104752684161010629378360761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279340491096028345008962029 104752684161010629378360761)
              ·
                refine ⟨78564513120757972033770571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104752684161010629378360761 78564513120757972033770571)
                ·
                  refine ⟨117846769681136958050655857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78564513120757972033770571 117846769681136958050655857)
                  ·
                    refine ⟨88385077260852718537991893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117846769681136958050655857 88385077260852718537991893)
                    ·
                      refine ⟨2071525248301235590734185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88385077260852718537991893 2071525248301235590734185)
                      ·
                        rfl

theorem cell23_4034281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_4034281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034281 prefixEnd_4034281 := by exact prefixLift 4034281
  have htrace : WordTrace (prefixWord ++ tailWord_4034281) baseStart_4034281 baseEnd_4034281 := by
    simpa [prefixWord, tailWord_4034281, baseEnd_4034281] using wordTrace_append hprefix tailTrace_4034281
  have hstable : (prefixWord ++ tailWord_4034281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034281).length < 2 ^ (prefixWord ++ tailWord_4034281).sum := by decide
  have hdescent : baseEnd_4034281 < baseStart_4034281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034292 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4034292 : Nat := 118140960795 + 4034292 * 2 ^ 59
def prefixEnd_4034292 : Nat := 4983230072969 + 3 ^ 40 * 4034292 * 2
def baseEnd_4034292 : Nat := 690510298862811682565545

theorem tailTrace_4034292 : CollatzResearch.WordTrace tailWord_4034292 prefixEnd_4034292 690510298862811682565545 := by
  unfold tailWord_4034292
  simp only [CollatzResearch.WordTrace]
  refine ⟨73571358750228280532220565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98095145000304374042960753 73571358750228280532220565)
  ·
    refine ⟨3448657441416950649947839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73571358750228280532220565 3448657441416950649947839)
    ·
      refine ⟨5172986162125425974921759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448657441416950649947839 5172986162125425974921759)
      ·
        refine ⟨7759479243188138962382639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172986162125425974921759 7759479243188138962382639)
        ·
          refine ⟨11639218864782208443573959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759479243188138962382639 11639218864782208443573959)
          ·
            refine ⟨17458828297173312665360939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639218864782208443573959 17458828297173312665360939)
            ·
              refine ⟨26188242445759968998041409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458828297173312665360939 26188242445759968998041409)
              ·
                refine ⟨19641181834319976748531057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26188242445759968998041409 19641181834319976748531057)
                ·
                  refine ⟨14730886375739982561398293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19641181834319976748531057 14730886375739982561398293)
                  ·
                    refine ⟨690510298862811682565545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14730886375739982561398293 690510298862811682565545)
                    ·
                      rfl

theorem cell23_4034292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4034292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034292 prefixEnd_4034292 := by exact prefixLift 4034292
  have htrace : WordTrace (prefixWord ++ tailWord_4034292) baseStart_4034292 baseEnd_4034292 := by
    simpa [prefixWord, tailWord_4034292, baseEnd_4034292] using wordTrace_append hprefix tailTrace_4034292
  have hstable : (prefixWord ++ tailWord_4034292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034292).length < 2 ^ (prefixWord ++ tailWord_4034292).sum := by decide
  have hdescent : baseEnd_4034292 < baseStart_4034292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034305 : List Nat := [1, 2, 4, 1, 1, 1, 4, 4, 5]
def baseStart_4034305 : Nat := 118140960795 + 4034305 * 2 ^ 59
def prefixEnd_4034305 : Nat := 4983230072969 + 3 ^ 40 * 4034305 * 2
def baseEnd_4034305 : Nat := 230170841315215944092675

theorem tailTrace_4034305 : CollatzResearch.WordTrace tailWord_4034305 prefixEnd_4034305 230170841315215944092675 := by
  unfold tailWord_4034305
  simp only [CollatzResearch.WordTrace]
  refine ⟨147143191649409464284664369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98095461099606309523109579 147143191649409464284664369)
  ·
    refine ⟨110357393737057098213498277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147143191649409464284664369 110357393737057098213498277)
    ·
      refine ⟨20692011325698205915030927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110357393737057098213498277 20692011325698205915030927)
      ·
        refine ⟨31038016988547308872546391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20692011325698205915030927 31038016988547308872546391)
        ·
          refine ⟨46557025482820963308819587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31038016988547308872546391 46557025482820963308819587)
          ·
            refine ⟨69835538224231444963229381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46557025482820963308819587 69835538224231444963229381)
            ·
              refine ⟨13094163417043395930605509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69835538224231444963229381 13094163417043395930605509)
              ·
                refine ⟨2455155640695636736988533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13094163417043395930605509 2455155640695636736988533)
                ·
                  refine ⟨230170841315215944092675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455155640695636736988533 230170841315215944092675)
                  ·
                    rfl

theorem cell23_4034305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 5].length) (baseStart_4034305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034305 prefixEnd_4034305 := by exact prefixLift 4034305
  have htrace : WordTrace (prefixWord ++ tailWord_4034305) baseStart_4034305 baseEnd_4034305 := by
    simpa [prefixWord, tailWord_4034305, baseEnd_4034305] using wordTrace_append hprefix tailTrace_4034305
  have hstable : (prefixWord ++ tailWord_4034305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034305).length < 2 ^ (prefixWord ++ tailWord_4034305).sum := by decide
  have hdescent : baseEnd_4034305 < baseStart_4034305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034310 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4034310 : Nat := 118140960795 + 4034310 * 2 ^ 59
def prefixEnd_4034310 : Nat := 4983230072969 + 3 ^ 40 * 4034310 * 2
def baseEnd_4034310 : Nat := 2071540139240215977271553

theorem tailTrace_4034310 : CollatzResearch.WordTrace tailWord_4034310 prefixEnd_4034310 2071540139240215977271553 := by
  unfold tailWord_4034310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598230437949729691831137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98095582676260900092397589 4598230437949729691831137)
  ·
    refine ⟨3448672828462297268873353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4598230437949729691831137 3448672828462297268873353)
    ·
      refine ⟨2586504621346722951655015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448672828462297268873353 2586504621346722951655015)
      ·
        refine ⟨3879756932020084427482523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586504621346722951655015 3879756932020084427482523)
        ·
          refine ⟨5819635398030126641223785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879756932020084427482523 5819635398030126641223785)
          ·
            refine ⟨4364726548522594980917839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5819635398030126641223785 4364726548522594980917839)
            ·
              refine ⟨6547089822783892471376759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364726548522594980917839 6547089822783892471376759)
              ·
                refine ⟨9820634734175838707065139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547089822783892471376759 9820634734175838707065139)
                ·
                  refine ⟨14730952101263758060597709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820634734175838707065139 14730952101263758060597709)
                  ·
                    refine ⟨5524107037973909272724141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14730952101263758060597709 5524107037973909272724141)
                    ·
                      refine ⟨2071540139240215977271553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524107037973909272724141 2071540139240215977271553)
                      ·
                        rfl

theorem cell23_4034310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4034310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034310 prefixEnd_4034310 := by exact prefixLift 4034310
  have htrace : WordTrace (prefixWord ++ tailWord_4034310) baseStart_4034310 baseEnd_4034310 := by
    simpa [prefixWord, tailWord_4034310, baseEnd_4034310] using wordTrace_append hprefix tailTrace_4034310
  have hstable : (prefixWord ++ tailWord_4034310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034310).length < 2 ^ (prefixWord ++ tailWord_4034310).sum := by decide
  have hdescent : baseEnd_4034310 < baseStart_4034310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034318 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 1, 7]
def baseStart_4034318 : Nat := 118140960795 + 4034318 * 2 ^ 59
def prefixEnd_4034318 : Nat := 4983230072969 + 3 ^ 40 * 4034318 * 2
def baseEnd_4034318 : Nat := 690514749028483981990505

theorem tailTrace_4034318 : CollatzResearch.WordTrace tailWord_4034318 prefixEnd_4034318 690514749028483981990505 := by
  unfold tailWord_4034318
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392958224795295938110951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98095777198908245003258405 18392958224795295938110951)
  ·
    refine ⟨27589437337192943907166427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18392958224795295938110951 27589437337192943907166427)
    ·
      refine ⟨41384156005789415860749641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27589437337192943907166427 41384156005789415860749641)
      ·
        refine ⟨31038117004342061895562231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41384156005789415860749641 31038117004342061895562231)
        ·
          refine ⟨46557175506513092843343347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31038117004342061895562231 46557175506513092843343347)
          ·
            refine ⟨69835763259769639265015021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46557175506513092843343347 69835763259769639265015021)
            ·
              refine ⟨26188411222413614724380633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69835763259769639265015021 26188411222413614724380633)
              ·
                refine ⟨19641308416810211043285475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26188411222413614724380633 19641308416810211043285475)
                ·
                  refine ⟨29461962625215316564928213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19641308416810211043285475 29461962625215316564928213)
                  ·
                    refine ⟨690514749028483981990505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29461962625215316564928213 690514749028483981990505)
                    ·
                      rfl

theorem cell23_4034318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_4034318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034318 prefixEnd_4034318 := by exact prefixLift 4034318
  have htrace : WordTrace (prefixWord ++ tailWord_4034318) baseStart_4034318 baseEnd_4034318 := by
    simpa [prefixWord, tailWord_4034318, baseEnd_4034318] using wordTrace_append hprefix tailTrace_4034318
  have hstable : (prefixWord ++ tailWord_4034318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034318).length < 2 ^ (prefixWord ++ tailWord_4034318).sum := by decide
  have hdescent : baseEnd_4034318 < baseStart_4034318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034415 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 5, 5, 2]
def baseStart_4034415 : Nat := 118140960795 + 4034415 * 2 ^ 59
def prefixEnd_4034415 : Nat := 4983230072969 + 3 ^ 40 * 4034415 * 2
def baseEnd_4034415 : Nat := 2071594054708938066458569

theorem tailTrace_4034415 : CollatzResearch.WordTrace tailWord_4034415 prefixEnd_4034415 2071594054708938066458569 := by
  unfold tailWord_4034415
  simp only [CollatzResearch.WordTrace]
  refine ⟨147147203679010953071168699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98098135786007302047445799 147147203679010953071168699)
  ·
    refine ⟨220720805518516429606753049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147147203679010953071168699 220720805518516429606753049)
    ·
      refine ⟨165540604138887322205064787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220720805518516429606753049 165540604138887322205064787)
      ·
        refine ⟨248310906208330983307597181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165540604138887322205064787 248310906208330983307597181)
        ·
          refine ⟨93116589828124118740348943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248310906208330983307597181 93116589828124118740348943)
          ·
            refine ⟨139674884742186178110523415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93116589828124118740348943 139674884742186178110523415)
            ·
              refine ⟨209512327113279267165785123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139674884742186178110523415 209512327113279267165785123)
              ·
                refine ⟨314268490669918900748677685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209512327113279267165785123 314268490669918900748677685)
                ·
                  refine ⟨29462671000304896945188533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314268490669918900748677685 29462671000304896945188533)
                  ·
                    refine ⟨2762125406278584088611425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29462671000304896945188533 2762125406278584088611425)
                    ·
                      refine ⟨2071594054708938066458569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762125406278584088611425 2071594054708938066458569)
                      ·
                        rfl

theorem cell23_4034415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 5, 5, 2].length) (baseStart_4034415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034415 prefixEnd_4034415 := by exact prefixLift 4034415
  have htrace : WordTrace (prefixWord ++ tailWord_4034415) baseStart_4034415 baseEnd_4034415 := by
    simpa [prefixWord, tailWord_4034415, baseEnd_4034415] using wordTrace_append hprefix tailTrace_4034415
  have hstable : (prefixWord ++ tailWord_4034415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034415).length < 2 ^ (prefixWord ++ tailWord_4034415).sum := by decide
  have hdescent : baseEnd_4034415 < baseStart_4034415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034439 : List Nat := [1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_4034439 : Nat := 118140960795 + 4034439 * 2 ^ 59
def prefixEnd_4034439 : Nat := 4983230072969 + 3 ^ 40 * 4034439 * 2
def baseEnd_4034439 : Nat := 2071606378244645972558459

theorem tailTrace_4034439 : CollatzResearch.WordTrace tailWord_4034439 prefixEnd_4034439 2071606378244645972558459 := by
  unfold tailWord_4034439
  simp only [CollatzResearch.WordTrace]
  refine ⟨147148079030924005170042371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98098719353949336780028247 147148079030924005170042371)
  ·
    refine ⟨220722118546386007755063557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147148079030924005170042371 220722118546386007755063557)
    ·
      refine ⟨41385397227447376454074417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220722118546386007755063557 41385397227447376454074417)
      ·
        refine ⟨31039047920585532340555813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41385397227447376454074417 31039047920585532340555813)
        ·
          refine ⟨5819821485109787313854215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31039047920585532340555813 5819821485109787313854215)
          ·
            refine ⟨8729732227664680970781323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819821485109787313854215 8729732227664680970781323)
            ·
              refine ⟨13094598341497021456171985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729732227664680970781323 13094598341497021456171985)
              ·
                refine ⟨9820948756122766092128989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094598341497021456171985 9820948756122766092128989)
                ·
                  refine ⟨3682855783546037284548371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9820948756122766092128989 3682855783546037284548371)
                  ·
                    refine ⟨5524283675319055926822557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682855783546037284548371 5524283675319055926822557)
                    ·
                      refine ⟨2071606378244645972558459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524283675319055926822557 2071606378244645972558459)
                      ·
                        rfl

theorem cell23_4034439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_4034439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034439 prefixEnd_4034439 := by exact prefixLift 4034439
  have htrace : WordTrace (prefixWord ++ tailWord_4034439) baseStart_4034439 baseEnd_4034439 := by
    simpa [prefixWord, tailWord_4034439, baseEnd_4034439] using wordTrace_append hprefix tailTrace_4034439
  have hstable : (prefixWord ++ tailWord_4034439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034439).length < 2 ^ (prefixWord ++ tailWord_4034439).sum := by decide
  have hdescent : baseEnd_4034439 < baseStart_4034439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034455 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 1, 6]
def baseStart_4034455 : Nat := 118140960795 + 4034455 * 2 ^ 59
def prefixEnd_4034455 : Nat := 4983230072969 + 3 ^ 40 * 4034455 * 2
def baseEnd_4034455 : Nat := 690538197978372636652795

theorem tailTrace_4034455 : CollatzResearch.WordTrace tailWord_4034455 prefixEnd_4034455 690538197978372636652795 := by
  unfold tailWord_4034455
  simp only [CollatzResearch.WordTrace]
  refine ⟨147148662598866039902624819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98099108399244026601749879 147148662598866039902624819)
  ·
    refine ⟨220722993898299059853937229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147148662598866039902624819 220722993898299059853937229)
    ·
      refine ⟨82771122711862147445226461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220722993898299059853937229 82771122711862147445226461)
      ·
        refine ⟨31039171016948305291959923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82771122711862147445226461 31039171016948305291959923)
        ·
          refine ⟨46558756525422457937939885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31039171016948305291959923 46558756525422457937939885)
          ·
            refine ⟨17459533697033421726727457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46558756525422457937939885 17459533697033421726727457)
            ·
              refine ⟨13094650272775066295045593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17459533697033421726727457 13094650272775066295045593)
              ·
                refine ⟨9820987704581299721284195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094650272775066295045593 9820987704581299721284195)
                ·
                  refine ⟨14731481556871949581926293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9820987704581299721284195 14731481556871949581926293)
                  ·
                    refine ⟨690538197978372636652795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14731481556871949581926293 690538197978372636652795)
                    ·
                      rfl

theorem cell23_4034455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_4034455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034455 prefixEnd_4034455 := by exact prefixLift 4034455
  have htrace : WordTrace (prefixWord ++ tailWord_4034455) baseStart_4034455 baseEnd_4034455 := by
    simpa [prefixWord, tailWord_4034455, baseEnd_4034455] using wordTrace_append hprefix tailTrace_4034455
  have hstable : (prefixWord ++ tailWord_4034455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034455).length < 2 ^ (prefixWord ++ tailWord_4034455).sum := by decide
  have hdescent : baseEnd_4034455 < baseStart_4034455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034479 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 3, 2, 2]
def baseStart_4034479 : Nat := 118140960795 + 4034479 * 2 ^ 59
def prefixEnd_4034479 : Nat := 4983230072969 + 3 ^ 40 * 4034479 * 2
def baseEnd_4034479 : Nat := 2071626917470825816058275

theorem tailTrace_4034479 : CollatzResearch.WordTrace tailWord_4034479 prefixEnd_4034479 2071626917470825816058275 := by
  unfold tailWord_4034479
  simp only [CollatzResearch.WordTrace]
  refine ⟨147149537950779092001498491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98099691967186061334332327 147149537950779092001498491)
  ·
    refine ⟨220724306926168638002247737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147149537950779092001498491 220724306926168638002247737)
    ·
      refine ⟨165543230194626478501685803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220724306926168638002247737 165543230194626478501685803)
      ·
        refine ⟨248314845291939717752528705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165543230194626478501685803 248314845291939717752528705)
        ·
          refine ⟨186236133968954788314396529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248314845291939717752528705 186236133968954788314396529)
          ·
            refine ⟨139677100476716091235797397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186236133968954788314396529 139677100476716091235797397)
            ·
              refine ⟨6547364084846066776678003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139677100476716091235797397 6547364084846066776678003)
              ·
                refine ⟨9821046127269100165017005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547364084846066776678003 9821046127269100165017005)
                ·
                  refine ⟨3682892297725912561881377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9821046127269100165017005 3682892297725912561881377)
                  ·
                    refine ⟨2762169223294434421411033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682892297725912561881377 2762169223294434421411033)
                    ·
                      refine ⟨2071626917470825816058275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762169223294434421411033 2071626917470825816058275)
                      ·
                        rfl

theorem cell23_4034479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 3, 2, 2].length) (baseStart_4034479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034479 prefixEnd_4034479 := by exact prefixLift 4034479
  have htrace : WordTrace (prefixWord ++ tailWord_4034479) baseStart_4034479 baseEnd_4034479 := by
    simpa [prefixWord, tailWord_4034479, baseEnd_4034479] using wordTrace_append hprefix tailTrace_4034479
  have hstable : (prefixWord ++ tailWord_4034479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034479).length < 2 ^ (prefixWord ++ tailWord_4034479).sum := by decide
  have hdescent : baseEnd_4034479 < baseStart_4034479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034489 : List Nat := [1, 2, 1, 4, 2, 1, 5, 1, 2, 4]
def baseStart_4034489 : Nat := 118140960795 + 4034489 * 2 ^ 59
def prefixEnd_4034489 : Nat := 4983230072969 + 3 ^ 40 * 4034489 * 2
def baseEnd_4034489 : Nat := 690544017425790258977743

theorem tailTrace_4034489 : CollatzResearch.WordTrace tailWord_4034489 prefixEnd_4034489 690544017425790258977743 := by
  unfold tailWord_4034489
  simp only [CollatzResearch.WordTrace]
  refine ⟨147149902680742863709362521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98099935120495242472908347 147149902680742863709362521)
  ·
    refine ⟨110362427010557147782021891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147149902680742863709362521 110362427010557147782021891)
    ·
      refine ⟨165543640515835721673032837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110362427010557147782021891 165543640515835721673032837)
      ·
        refine ⟨31039432596719197813693657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165543640515835721673032837 31039432596719197813693657)
        ·
          refine ⟨23279574447539398360270243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31039432596719197813693657 23279574447539398360270243)
          ·
            refine ⟨34919361671309097540405365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23279574447539398360270243 34919361671309097540405365)
            ·
              refine ⟨3273690156685227894413003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34919361671309097540405365 3273690156685227894413003)
              ·
                refine ⟨4910535235027841841619505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273690156685227894413003 4910535235027841841619505)
                ·
                  refine ⟨3682901426270881381214629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910535235027841841619505 3682901426270881381214629)
                  ·
                    refine ⟨690544017425790258977743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3682901426270881381214629 690544017425790258977743)
                    ·
                      rfl

theorem cell23_4034489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 2, 4].length) (baseStart_4034489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034489 prefixEnd_4034489 := by exact prefixLift 4034489
  have htrace : WordTrace (prefixWord ++ tailWord_4034489) baseStart_4034489 baseEnd_4034489 := by
    simpa [prefixWord, tailWord_4034489, baseEnd_4034489] using wordTrace_append hprefix tailTrace_4034489
  have hstable : (prefixWord ++ tailWord_4034489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034489).length < 2 ^ (prefixWord ++ tailWord_4034489).sum := by decide
  have hdescent : baseEnd_4034489 < baseStart_4034489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034512 : List Nat := [2, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3]
def baseStart_4034512 : Nat := 118140960795 + 4034512 * 2 ^ 59
def prefixEnd_4034512 : Nat := 4983230072969 + 3 ^ 40 * 4034512 * 2
def baseEnd_4034512 : Nat := 2071643862332424186945623

theorem tailTrace_4034512 : CollatzResearch.WordTrace tailWord_4034512 prefixEnd_4034512 2071643862332424186945623 := by
  unfold tailWord_4034512
  simp only [CollatzResearch.WordTrace]
  refine ⟨73575370779829769318724895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98100494373106359091633193 73575370779829769318724895)
  ·
    refine ⟨110363056169744653978087343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73575370779829769318724895 110363056169744653978087343)
    ·
      refine ⟨165544584254616980967131015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110363056169744653978087343 165544584254616980967131015)
      ·
        refine ⟨248316876381925471450696523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165544584254616980967131015 248316876381925471450696523)
        ·
          refine ⟨372475314572888207176044785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248316876381925471450696523 372475314572888207176044785)
          ·
            refine ⟨279356485929666155382033589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372475314572888207176044785 279356485929666155382033589)
            ·
              refine ⟨26189670555906202067065649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279356485929666155382033589 26189670555906202067065649)
              ·
                refine ⟨19642252916929651550299237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26189670555906202067065649 19642252916929651550299237)
                ·
                  refine ⟨3682922421924309665681107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19642252916929651550299237 3682922421924309665681107)
                  ·
                    refine ⟨5524383632886464498521661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682922421924309665681107 5524383632886464498521661)
                    ·
                      refine ⟨2071643862332424186945623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524383632886464498521661 2071643862332424186945623)
                      ·
                        rfl

theorem cell23_4034512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 2, 4, 1, 3].length) (baseStart_4034512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034512 prefixEnd_4034512 := by exact prefixLift 4034512
  have htrace : WordTrace (prefixWord ++ tailWord_4034512) baseStart_4034512 baseEnd_4034512 := by
    simpa [prefixWord, tailWord_4034512, baseEnd_4034512] using wordTrace_append hprefix tailTrace_4034512
  have hstable : (prefixWord ++ tailWord_4034512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034512).length < 2 ^ (prefixWord ++ tailWord_4034512).sum := by decide
  have hdescent : baseEnd_4034512 < baseStart_4034512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034530 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_4034530 : Nat := 118140960795 + 4034530 * 2 ^ 59
def prefixEnd_4034530 : Nat := 4983230072969 + 3 ^ 40 * 4034530 * 2
def baseEnd_4034530 : Nat := 2071653104984205116520541

theorem tailTrace_4034530 : CollatzResearch.WordTrace tailWord_4034530 prefixEnd_4034530 2071653104984205116520541 := by
  unfold tailWord_4034530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36787849518398581927901261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98100932049062885141070029 36787849518398581927901261)
  ·
    refine ⟨13795443569399468222962973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36787849518398581927901261 13795443569399468222962973)
    ·
      refine ⟨5173291338524800583611115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13795443569399468222962973 5173291338524800583611115)
      ·
        refine ⟨7759937007787200875416673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173291338524800583611115 7759937007787200875416673)
        ·
          refine ⟨5819952755840400656562505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7759937007787200875416673 5819952755840400656562505)
          ·
            refine ⟨4364964566880300492421879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5819952755840400656562505 4364964566880300492421879)
            ·
              refine ⟨6547446850320450738632819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364964566880300492421879 6547446850320450738632819)
              ·
                refine ⟨9821170275480676107949229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547446850320450738632819 9821170275480676107949229)
                ·
                  refine ⟨3682938853305253540480961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9821170275480676107949229 3682938853305253540480961)
                  ·
                    refine ⟨2762204139978940155360721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682938853305253540480961 2762204139978940155360721)
                    ·
                      refine ⟨2071653104984205116520541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762204139978940155360721 2071653104984205116520541)
                      ·
                        rfl

theorem cell23_4034530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_4034530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034530 prefixEnd_4034530 := by exact prefixLift 4034530
  have htrace : WordTrace (prefixWord ++ tailWord_4034530) baseStart_4034530 baseEnd_4034530 := by
    simpa [prefixWord, tailWord_4034530, baseEnd_4034530] using wordTrace_append hprefix tailTrace_4034530
  have hstable : (prefixWord ++ tailWord_4034530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034530).length < 2 ^ (prefixWord ++ tailWord_4034530).sum := by decide
  have hdescent : baseEnd_4034530 < baseStart_4034530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034555 : List Nat := [1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5]
def baseStart_4034555 : Nat := 118140960795 + 4034555 * 2 ^ 59
def prefixEnd_4034555 : Nat := 4983230072969 + 3 ^ 40 * 4034555 * 2
def baseEnd_4034555 : Nat := 2071665942000567518707925

theorem tailTrace_4034555 : CollatzResearch.WordTrace tailWord_4034555 prefixEnd_4034555 2071665942000567518707925 := by
  unfold tailWord_4034555
  simp only [CollatzResearch.WordTrace]
  refine ⟨147152309898503756981265119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98101539932335837987510079 147152309898503756981265119)
  ·
    refine ⟨220728464847755635471897679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147152309898503756981265119 220728464847755635471897679)
    ·
      refine ⟨331092697271633453207846519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220728464847755635471897679 331092697271633453207846519)
      ·
        refine ⟨496639045907450179811769779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331092697271633453207846519 496639045907450179811769779)
        ·
          refine ⟨744958568861175269717654669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496639045907450179811769779 744958568861175269717654669)
          ·
            refine ⟨279359463322940726144120501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744958568861175269717654669 279359463322940726144120501)
            ·
              refine ⟨26189949686525693076011297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279359463322940726144120501 26189949686525693076011297)
              ·
                refine ⟨19642462264894269807008473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26189949686525693076011297 19642462264894269807008473)
                ·
                  refine ⟨14731846698670702355256355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19642462264894269807008473 14731846698670702355256355)
                  ·
                    refine ⟨22097770048006053532884533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14731846698670702355256355 22097770048006053532884533)
                    ·
                      refine ⟨2071665942000567518707925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22097770048006053532884533 2071665942000567518707925)
                      ·
                        rfl

theorem cell23_4034555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 5].length) (baseStart_4034555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034555 prefixEnd_4034555 := by exact prefixLift 4034555
  have htrace : WordTrace (prefixWord ++ tailWord_4034555) baseStart_4034555 baseEnd_4034555 := by
    simpa [prefixWord, tailWord_4034555, baseEnd_4034555] using wordTrace_append hprefix tailTrace_4034555
  have hstable : (prefixWord ++ tailWord_4034555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034555).length < 2 ^ (prefixWord ++ tailWord_4034555).sum := by decide
  have hdescent : baseEnd_4034555 < baseStart_4034555 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034580 : List Nat := [2, 4, 3, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_4034580 : Nat := 118140960795 + 4034580 * 2 ^ 59
def prefixEnd_4034580 : Nat := 4983230072969 + 3 ^ 40 * 4034580 * 2
def baseEnd_4034580 : Nat := 2071678779016929920895311

theorem tailTrace_4034580 : CollatzResearch.WordTrace tailWord_4034580 prefixEnd_4034580 2071678779016929920895311 := by
  unfold tailWord_4034580
  simp only [CollatzResearch.WordTrace]
  refine ⟨73576610861706593125462597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98102147815608790833950129 73576610861706593125462597)
  ·
    refine ⟨13795614536569986211024237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73576610861706593125462597 13795614536569986211024237)
    ·
      refine ⟨5173355451213744829134089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13795614536569986211024237 5173355451213744829134089)
      ·
        refine ⟨3880016588410308621850567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5173355451213744829134089 3880016588410308621850567)
        ·
          refine ⟨5820024882615462932775851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880016588410308621850567 5820024882615462932775851)
          ·
            refine ⟨8730037323923194399163777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820024882615462932775851 8730037323923194399163777)
            ·
              refine ⟨6547527992942395799372833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8730037323923194399163777 6547527992942395799372833)
              ·
                refine ⟨4910645994706796849529625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6547527992942395799372833 4910645994706796849529625)
                ·
                  refine ⟨3682984496030097637147219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910645994706796849529625 3682984496030097637147219)
                  ·
                    refine ⟨5524476744045146455720829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3682984496030097637147219 5524476744045146455720829)
                    ·
                      refine ⟨2071678779016929920895311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524476744045146455720829 2071678779016929920895311)
                      ·
                        rfl

theorem cell23_4034580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_4034580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034580 prefixEnd_4034580 := by exact prefixLift 4034580
  have htrace : WordTrace (prefixWord ++ tailWord_4034580) baseStart_4034580 baseEnd_4034580 := by
    simpa [prefixWord, tailWord_4034580, baseEnd_4034580] using wordTrace_append hprefix tailTrace_4034580
  have hstable : (prefixWord ++ tailWord_4034580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034580).length < 2 ^ (prefixWord ++ tailWord_4034580).sum := by decide
  have hdescent : baseEnd_4034580 < baseStart_4034580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034586 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2]
def baseStart_4034586 : Nat := 118140960795 + 4034586 * 2 ^ 59
def prefixEnd_4034586 : Nat := 4983230072969 + 3 ^ 40 * 4034586 * 2
def baseEnd_4034586 : Nat := 2071681859900856897420283

theorem tailTrace_4034586 : CollatzResearch.WordTrace tailWord_4034586 prefixEnd_4034586 2071681859900856897420283 := by
  unfold tailWord_4034586
  simp only [CollatzResearch.WordTrace]
  refine ⟨36788360140347862318910903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98102293707594299517095741 36788360140347862318910903)
  ·
    refine ⟨55182540210521793478366355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36788360140347862318910903 55182540210521793478366355)
    ·
      refine ⟨82773810315782690217549533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55182540210521793478366355 82773810315782690217549533)
      ·
        refine ⟨31040178868418508831581075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82773810315782690217549533 31040178868418508831581075)
        ·
          refine ⟨46560268302627763247371613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31040178868418508831581075 46560268302627763247371613)
          ·
            refine ⟨17460100613485411217764355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46560268302627763247371613 17460100613485411217764355)
            ·
              refine ⟨26190150920228116826646533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17460100613485411217764355 26190150920228116826646533)
              ·
                refine ⟨4910653297542771904996225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26190150920228116826646533 4910653297542771904996225)
                ·
                  refine ⟨3682989973157078928747169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910653297542771904996225 3682989973157078928747169)
                  ·
                    refine ⟨2762242479867809196560377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3682989973157078928747169 2762242479867809196560377)
                    ·
                      refine ⟨2071681859900856897420283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762242479867809196560377 2071681859900856897420283)
                      ·
                        rfl

theorem cell23_4034586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_4034586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034586 prefixEnd_4034586 := by exact prefixLift 4034586
  have htrace : WordTrace (prefixWord ++ tailWord_4034586) baseStart_4034586 baseEnd_4034586 := by
    simpa [prefixWord, tailWord_4034586, baseEnd_4034586] using wordTrace_append hprefix tailTrace_4034586
  have hstable : (prefixWord ++ tailWord_4034586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034586).length < 2 ^ (prefixWord ++ tailWord_4034586).sum := by decide
  have hdescent : baseEnd_4034586 < baseStart_4034586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034615 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_4034615 : Nat := 118140960795 + 4034615 * 2 ^ 59
def prefixEnd_4034615 : Nat := 4983230072969 + 3 ^ 40 * 4034615 * 2
def baseEnd_4034615 : Nat := 2071696750839837283957649

theorem tailTrace_4034615 : CollatzResearch.WordTrace tailWord_4034615 prefixEnd_4034615 2071696750839837283957649 := by
  unfold tailWord_4034615
  simp only [CollatzResearch.WordTrace]
  refine ⟨147154498278286387228449299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98102998852190924818966199 147154498278286387228449299)
  ·
    refine ⟨220731747417429580842673949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147154498278286387228449299 220731747417429580842673949)
    ·
      refine ⟨82774405281536092816002731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220731747417429580842673949 82774405281536092816002731)
      ·
        refine ⟨124161607922304139224004097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82774405281536092816002731 124161607922304139224004097)
        ·
          refine ⟨93121205941728104418003073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124161607922304139224004097 93121205941728104418003073)
          ·
            refine ⟨69840904456296078313502305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93121205941728104418003073 69840904456296078313502305)
            ·
              refine ⟨52380678342222058735126729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69840904456296078313502305 52380678342222058735126729)
              ·
                refine ⟨39285508756666544051345047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52380678342222058735126729 39285508756666544051345047)
                ·
                  refine ⟨58928263134999816077017571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39285508756666544051345047 58928263134999816077017571)
                  ·
                    refine ⟨88392394702499724115526357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58928263134999816077017571 88392394702499724115526357)
                    ·
                      refine ⟨2071696750839837283957649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88392394702499724115526357 2071696750839837283957649)
                      ·
                        rfl

theorem cell23_4034615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_4034615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034615 prefixEnd_4034615 := by exact prefixLift 4034615
  have htrace : WordTrace (prefixWord ++ tailWord_4034615) baseStart_4034615 baseEnd_4034615 := by
    simpa [prefixWord, tailWord_4034615, baseEnd_4034615] using wordTrace_append hprefix tailTrace_4034615
  have hstable : (prefixWord ++ tailWord_4034615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034615).length < 2 ^ (prefixWord ++ tailWord_4034615).sum := by decide
  have hdescent : baseEnd_4034615 < baseStart_4034615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034654 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_4034654 : Nat := 118140960795 + 4034654 * 2 ^ 59
def prefixEnd_4034654 : Nat := 4983230072969 + 3 ^ 40 * 4034654 * 2
def baseEnd_4034654 : Nat := 2071716776585362631369971

theorem tailTrace_4034654 : CollatzResearch.WordTrace tailWord_4034654 prefixEnd_4034654 2071716776585362631369971 := by
  unfold tailWord_4034654
  simp only [CollatzResearch.WordTrace]
  refine ⟨18394490090643137111139877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98103947150096731259412677 18394490090643137111139877)
  ·
    refine ⟨3448966891995588208338727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18394490090643137111139877 3448966891995588208338727)
    ·
      refine ⟨5173450337993382312508091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448966891995588208338727 5173450337993382312508091)
      ·
        refine ⟨7760175506990073468762137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173450337993382312508091 7760175506990073468762137)
        ·
          refine ⟨5820131630242555101571603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760175506990073468762137 5820131630242555101571603)
          ·
            refine ⟨8730197445363832652357405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820131630242555101571603 8730197445363832652357405)
            ·
              refine ⟨3273824042011437244634027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8730197445363832652357405 3273824042011437244634027)
              ·
                refine ⟨4910736063017155866951041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273824042011437244634027 4910736063017155866951041)
                ·
                  refine ⟨3683052047262866900213281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910736063017155866951041 3683052047262866900213281)
                  ·
                    refine ⟨2762289035447150175159961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3683052047262866900213281 2762289035447150175159961)
                    ·
                      refine ⟨2071716776585362631369971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762289035447150175159961 2071716776585362631369971)
                      ·
                        rfl

theorem cell23_4034654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_4034654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034654 prefixEnd_4034654 := by exact prefixLift 4034654
  have htrace : WordTrace (prefixWord ++ tailWord_4034654) baseStart_4034654 baseEnd_4034654 := by
    simpa [prefixWord, tailWord_4034654, baseEnd_4034654] using wordTrace_append hprefix tailTrace_4034654
  have hstable : (prefixWord ++ tailWord_4034654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034654).length < 2 ^ (prefixWord ++ tailWord_4034654).sum := by decide
  have hdescent : baseEnd_4034654 < baseStart_4034654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034659 : List Nat := [1, 1, 1, 5, 1, 1, 4, 1, 2, 4, 2]
def baseStart_4034659 : Nat := 118140960795 + 4034659 * 2 ^ 59
def prefixEnd_4034659 : Nat := 4983230072969 + 3 ^ 40 * 4034659 * 2
def baseEnd_4034659 : Nat := 2071719343988635111807447

theorem tailTrace_4034659 : CollatzResearch.WordTrace tailWord_4034659 prefixEnd_4034659 2071719343988635111807447 := by
  unfold tailWord_4034659
  simp only [CollatzResearch.WordTrace]
  refine ⟨147156103090126982743051031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98104068726751321828700687 147156103090126982743051031)
  ·
    refine ⟨220734154635190474114576547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147156103090126982743051031 220734154635190474114576547)
    ·
      refine ⟨331101231952785711171864821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220734154635190474114576547 331101231952785711171864821)
      ·
        refine ⟨31040740495573660422362327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 331101231952785711171864821 31040740495573660422362327)
        ·
          refine ⟨46561110743360490633543491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31040740495573660422362327 46561110743360490633543491)
          ·
            refine ⟨69841666115040735950315237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46561110743360490633543491 69841666115040735950315237)
            ·
              refine ⟨13095312396570137990684107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69841666115040735950315237 13095312396570137990684107)
              ·
                refine ⟨19642968594855206986026161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13095312396570137990684107 19642968594855206986026161)
                ·
                  refine ⟨14732226446141405239519621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19642968594855206986026161 14732226446141405239519621)
                  ·
                    refine ⟨2762292458651513482409929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14732226446141405239519621 2762292458651513482409929)
                    ·
                      refine ⟨2071719343988635111807447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762292458651513482409929 2071719343988635111807447)
                      ·
                        rfl

theorem cell23_4034659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_4034659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034659 prefixEnd_4034659 := by exact prefixLift 4034659
  have htrace : WordTrace (prefixWord ++ tailWord_4034659) baseStart_4034659 baseEnd_4034659 := by
    simpa [prefixWord, tailWord_4034659, baseEnd_4034659] using wordTrace_append hprefix tailTrace_4034659
  have hstable : (prefixWord ++ tailWord_4034659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034659).length < 2 ^ (prefixWord ++ tailWord_4034659).sum := by decide
  have hdescent : baseEnd_4034659 < baseStart_4034659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034669 : List Nat := [1, 5, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4034669 : Nat := 118140960795 + 4034669 * 2 ^ 59
def prefixEnd_4034669 : Nat := 4983230072969 + 3 ^ 40 * 4034669 * 2
def baseEnd_4034669 : Nat := 690574826265060024227467

theorem tailTrace_4034669 : CollatzResearch.WordTrace tailWord_4034669 prefixEnd_4034669 690574826265060024227467 := by
  unfold tailWord_4034669
  simp only [CollatzResearch.WordTrace]
  refine ⟨147156467820090754450915061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98104311880060502967276707 147156467820090754450915061)
  ·
    refine ⟨13795918858133508229773287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147156467820090754450915061 13795918858133508229773287)
    ·
      refine ⟨20693878287200262344659931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13795918858133508229773287 20693878287200262344659931)
      ·
        refine ⟨31040817430800393516989897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20693878287200262344659931 31040817430800393516989897)
        ·
          refine ⟨23280613073100295137742423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31040817430800393516989897 23280613073100295137742423)
          ·
            refine ⟨34920919609650442706613635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23280613073100295137742423 34920919609650442706613635)
            ·
              refine ⟨52381379414475664059920453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34920919609650442706613635 52381379414475664059920453)
              ·
                refine ⟨9821508640214187011235085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52381379414475664059920453 9821508640214187011235085)
                ·
                  refine ⟨3683065740080320129213157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9821508640214187011235085 3683065740080320129213157)
                  ·
                    refine ⟨690574826265060024227467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3683065740080320129213157 690574826265060024227467)
                    ·
                      rfl

theorem cell23_4034669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4034669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034669 prefixEnd_4034669 := by exact prefixLift 4034669
  have htrace : WordTrace (prefixWord ++ tailWord_4034669) baseStart_4034669 baseEnd_4034669 := by
    simpa [prefixWord, tailWord_4034669, baseEnd_4034669] using wordTrace_append hprefix tailTrace_4034669
  have hstable : (prefixWord ++ tailWord_4034669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034669).length < 2 ^ (prefixWord ++ tailWord_4034669).sum := by decide
  have hdescent : baseEnd_4034669 < baseStart_4034669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034675 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9]
def baseStart_4034675 : Nat := 118140960795 + 4034675 * 2 ^ 59
def prefixEnd_4034675 : Nat := 4983230072969 + 3 ^ 40 * 4034675 * 2
def baseEnd_4034675 : Nat := 2071727559679107049207373

theorem tailTrace_4034675 : CollatzResearch.WordTrace tailWord_4034675 prefixEnd_4034675 2071727559679107049207373 := by
  unfold tailWord_4034675
  simp only [CollatzResearch.WordTrace]
  refine ⟨147156686658069017475633479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98104457772046011650422319 147156686658069017475633479)
  ·
    refine ⟨220735029987103526213450219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147156686658069017475633479 220735029987103526213450219)
    ·
      refine ⟨331102544980655289320175329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220735029987103526213450219 331102544980655289320175329)
      ·
        refine ⟨248326908735491466990131497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331102544980655289320175329 248326908735491466990131497)
        ·
          refine ⟨186245181551618600242598623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248326908735491466990131497 186245181551618600242598623)
          ·
            refine ⟨279367772327427900363897935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186245181551618600242598623 279367772327427900363897935)
            ·
              refine ⟨419051658491141850545846903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279367772327427900363897935 419051658491141850545846903)
              ·
                refine ⟨628577487736712775818770355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419051658491141850545846903 628577487736712775818770355)
                ·
                  refine ⟨942866231605069163728155533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628577487736712775818770355 942866231605069163728155533)
                  ·
                    refine ⟨353574836851900936398058325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 942866231605069163728155533 353574836851900936398058325)
                    ·
                      refine ⟨2071727559679107049207373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 353574836851900936398058325 2071727559679107049207373)
                      ·
                        rfl

theorem cell23_4034675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 9].length) (baseStart_4034675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034675 prefixEnd_4034675 := by exact prefixLift 4034675
  have htrace : WordTrace (prefixWord ++ tailWord_4034675) baseStart_4034675 baseEnd_4034675 := by
    simpa [prefixWord, tailWord_4034675, baseEnd_4034675] using wordTrace_append hprefix tailTrace_4034675
  have hstable : (prefixWord ++ tailWord_4034675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034675).length < 2 ^ (prefixWord ++ tailWord_4034675).sum := by decide
  have hdescent : baseEnd_4034675 < baseStart_4034675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034696 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4034696 : Nat := 118140960795 + 4034696 * 2 ^ 59
def prefixEnd_4034696 : Nat := 4983230072969 + 3 ^ 40 * 4034696 * 2
def baseEnd_4034696 : Nat := 2071738342772851467044777

theorem tailTrace_4034696 : CollatzResearch.WordTrace tailWord_4034696 prefixEnd_4034696 2071738342772851467044777 := by
  unfold tailWord_4034696
  simp only [CollatzResearch.WordTrace]
  refine ⟨73578726295496469031073971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98104968393995292041431961 73578726295496469031073971)
  ·
    refine ⟨110368089443244703546610957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73578726295496469031073971 110368089443244703546610957)
    ·
      refine ⟨41388033541216763829979109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110368089443244703546610957 41388033541216763829979109)
      ·
        refine ⟨7760256288978143218121083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41388033541216763829979109 7760256288978143218121083)
        ·
          refine ⟨11640384433467214827181625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760256288978143218121083 11640384433467214827181625)
          ·
            refine ⟨8730288325100411120386219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11640384433467214827181625 8730288325100411120386219)
            ·
              refine ⟨13095432487650616680579329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8730288325100411120386219 13095432487650616680579329)
              ·
                refine ⟨9821574365737962510434497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13095432487650616680579329 9821574365737962510434497)
                ·
                  refine ⟨7366180774303471882825873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9821574365737962510434497 7366180774303471882825873)
                  ·
                    refine ⟨5524635580727603912119405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366180774303471882825873 5524635580727603912119405)
                    ·
                      refine ⟨2071738342772851467044777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524635580727603912119405 2071738342772851467044777)
                      ·
                        rfl

theorem cell23_4034696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4034696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034696 prefixEnd_4034696 := by exact prefixLift 4034696
  have htrace : WordTrace (prefixWord ++ tailWord_4034696) baseStart_4034696 baseEnd_4034696 := by
    simpa [prefixWord, tailWord_4034696, baseEnd_4034696] using wordTrace_append hprefix tailTrace_4034696
  have hstable : (prefixWord ++ tailWord_4034696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034696).length < 2 ^ (prefixWord ++ tailWord_4034696).sum := by decide
  have hdescent : baseEnd_4034696 < baseStart_4034696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034754 : List Nat := [3, 5, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_4034754 : Nat := 118140960795 + 4034754 * 2 ^ 59
def prefixEnd_4034754 : Nat := 4983230072969 + 3 ^ 40 * 4034754 * 2
def baseEnd_4034754 : Nat := 690589374883604080039837

theorem tailTrace_4034754 : CollatzResearch.WordTrace tailWord_4034754 prefixEnd_4034754 690589374883604080039837 := by
  unfold tailWord_4034754
  simp only [CollatzResearch.WordTrace]
  refine ⟨36789892006195703491939829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98106378683188542645172877 36789892006195703491939829)
  ·
    refine ⟨3449052375580847202369359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36789892006195703491939829 3449052375580847202369359)
    ·
      refine ⟨5173578563371270803554039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3449052375580847202369359 5173578563371270803554039)
      ·
        refine ⟨7760367845056906205331059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173578563371270803554039 7760367845056906205331059)
        ·
          refine ⟨11640551767585359307996589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760367845056906205331059 11640551767585359307996589)
          ·
            refine ⟨4365206912844509740498721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11640551767585359307996589 4365206912844509740498721)
            ·
              refine ⟨3273905184633382305374041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365206912844509740498721 3273905184633382305374041)
              ·
                refine ⟨2455428888475036729030531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3273905184633382305374041 2455428888475036729030531)
                ·
                  refine ⟨3683143332712555093545797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455428888475036729030531 3683143332712555093545797)
                  ·
                    refine ⟨690589374883604080039837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3683143332712555093545797 690589374883604080039837)
                    ·
                      rfl

theorem cell23_4034754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_4034754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034754 prefixEnd_4034754 := by exact prefixLift 4034754
  have htrace : WordTrace (prefixWord ++ tailWord_4034754) baseStart_4034754 baseEnd_4034754 := by
    simpa [prefixWord, tailWord_4034754, baseEnd_4034754] using wordTrace_append hprefix tailTrace_4034754
  have hstable : (prefixWord ++ tailWord_4034754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034754).length < 2 ^ (prefixWord ++ tailWord_4034754).sum := by decide
  have hdescent : baseEnd_4034754 < baseStart_4034754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034769 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 3]
def baseStart_4034769 : Nat := 118140960795 + 4034769 * 2 ^ 59
def prefixEnd_4034769 : Nat := 4983230072969 + 3 ^ 40 * 4034769 * 2
def baseEnd_4034769 : Nat := 2071775826860629681431941

theorem tailTrace_4034769 : CollatzResearch.WordTrace tailWord_4034769 prefixEnd_4034769 2071775826860629681431941 := by
  unfold tailWord_4034769
  simp only [CollatzResearch.WordTrace]
  refine ⟨147160115119728471529555361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98106743413152314353036907 147160115119728471529555361)
  ·
    refine ⟨110370086339796353647166521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147160115119728471529555361 110370086339796353647166521)
    ·
      refine ⟨82777564754847265235374891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110370086339796353647166521 82777564754847265235374891)
      ·
        refine ⟨124166347132270897853062337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82777564754847265235374891 124166347132270897853062337)
        ·
          refine ⟨93124760349203173389796753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124166347132270897853062337 93124760349203173389796753)
          ·
            refine ⟨69843570261902380042347565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93124760349203173389796753 69843570261902380042347565)
            ·
              refine ⟨26191338848213392515880337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69843570261902380042347565 26191338848213392515880337)
              ·
                refine ⟨19643504136160044386910253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26191338848213392515880337 19643504136160044386910253)
                ·
                  refine ⟨7366314051060016645091345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19643504136160044386910253 7366314051060016645091345)
                  ·
                    refine ⟨5524735538295012483818509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7366314051060016645091345 5524735538295012483818509)
                    ·
                      refine ⟨2071775826860629681431941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524735538295012483818509 2071775826860629681431941)
                      ·
                        rfl

theorem cell23_4034769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_4034769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034769 prefixEnd_4034769 := by exact prefixLift 4034769
  have htrace : WordTrace (prefixWord ++ tailWord_4034769) baseStart_4034769 baseEnd_4034769 := by
    simpa [prefixWord, tailWord_4034769, baseEnd_4034769] using wordTrace_append hprefix tailTrace_4034769
  have hstable : (prefixWord ++ tailWord_4034769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034769).length < 2 ^ (prefixWord ++ tailWord_4034769).sum := by decide
  have hdescent : baseEnd_4034769 < baseStart_4034769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034776 : List Nat := [2, 1, 2, 2, 4, 1, 2, 3, 2, 4]
def baseStart_4034776 : Nat := 118140960795 + 4034776 * 2 ^ 59
def prefixEnd_4034776 : Nat := 4983230072969 + 3 ^ 40 * 4034776 * 2
def baseEnd_4034776 : Nat := 690593140408403718014803

theorem tailTrace_4034776 : CollatzResearch.WordTrace tailWord_4034776 prefixEnd_4034776 690593140408403718014803 := by
  unfold tailWord_4034776
  simp only [CollatzResearch.WordTrace]
  refine ⟨73580185215351555862530091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98106913620468741150040121 73580185215351555862530091)
  ·
    refine ⟨110370277823027333793795137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73580185215351555862530091 110370277823027333793795137)
    ·
      refine ⟨82777708367270500345346353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110370277823027333793795137 82777708367270500345346353)
      ·
        refine ⟨62083281275452875259009765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82777708367270500345346353 62083281275452875259009765)
        ·
          refine ⟨11640615239147414111064331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62083281275452875259009765 11640615239147414111064331)
          ·
            refine ⟨17460922858721121166596497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11640615239147414111064331 17460922858721121166596497)
            ·
              refine ⟨13095692144040840874947373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17460922858721121166596497 13095692144040840874947373)
              ·
                refine ⟨4910884554015315328105265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13095692144040840874947373 4910884554015315328105265)
                ·
                  refine ⟨3683163415511486496078949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4910884554015315328105265 3683163415511486496078949)
                  ·
                    refine ⟨690593140408403718014803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3683163415511486496078949 690593140408403718014803)
                    ·
                      rfl

theorem cell23_4034776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_4034776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034776 prefixEnd_4034776 := by exact prefixLift 4034776
  have htrace : WordTrace (prefixWord ++ tailWord_4034776) baseStart_4034776 baseEnd_4034776 := by
    simpa [prefixWord, tailWord_4034776, baseEnd_4034776] using wordTrace_append hprefix tailTrace_4034776
  have hstable : (prefixWord ++ tailWord_4034776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034776).length < 2 ^ (prefixWord ++ tailWord_4034776).sum := by decide
  have hdescent : baseEnd_4034776 < baseStart_4034776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034787 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4034787 : Nat := 118140960795 + 4034787 * 2 ^ 59
def prefixEnd_4034787 : Nat := 4983230072969 + 3 ^ 40 * 4034787 * 2
def baseEnd_4034787 : Nat := 2071785069512410611006859

theorem tailTrace_4034787 : CollatzResearch.WordTrace tailWord_4034787 prefixEnd_4034787 2071785069512410611006859 := by
  unfold tailWord_4034787
  simp only [CollatzResearch.WordTrace]
  refine ⟨147160771633663260603710615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98107181089108840402473743 147160771633663260603710615)
  ·
    refine ⟨220741157450494890905565923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147160771633663260603710615 220741157450494890905565923)
    ·
      refine ⟨331111736175742336358348885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220741157450494890905565923 331111736175742336358348885)
      ·
        refine ⟨3880215658309480504199401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 331111736175742336358348885 3880215658309480504199401)
        ·
          refine ⟨2910161743732110378149551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3880215658309480504199401 2910161743732110378149551)
          ·
            refine ⟨4365242615598165567224327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910161743732110378149551 4365242615598165567224327)
            ·
              refine ⟨6547863923397248350836491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365242615598165567224327 6547863923397248350836491)
              ·
                refine ⟨9821795885095872526254737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6547863923397248350836491 9821795885095872526254737)
                ·
                  refine ⟨7366346913821904394691053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9821795885095872526254737 7366346913821904394691053)
                  ·
                    refine ⟨2762380092683214148009145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7366346913821904394691053 2762380092683214148009145)
                    ·
                      refine ⟨2071785069512410611006859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762380092683214148009145 2071785069512410611006859)
                      ·
                        rfl

theorem cell23_4034787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4034787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034787 prefixEnd_4034787 := by exact prefixLift 4034787
  have htrace : WordTrace (prefixWord ++ tailWord_4034787) baseStart_4034787 baseEnd_4034787 := by
    simpa [prefixWord, tailWord_4034787, baseEnd_4034787] using wordTrace_append hprefix tailTrace_4034787
  have hstable : (prefixWord ++ tailWord_4034787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034787).length < 2 ^ (prefixWord ++ tailWord_4034787).sum := by decide
  have hdescent : baseEnd_4034787 < baseStart_4034787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034826 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2]
def baseStart_4034826 : Nat := 118140960795 + 4034826 * 2 ^ 59
def prefixEnd_4034826 : Nat := 4983230072969 + 3 ^ 40 * 4034826 * 2
def baseEnd_4034826 : Nat := 2071805095257935958419179

theorem tailTrace_4034826 : CollatzResearch.WordTrace tailWord_4034826 prefixEnd_4034826 2071805095257935958419179 := by
  unfold tailWord_4034826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36790548520130492566095083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98108129387014646842920221 36790548520130492566095083)
  ·
    refine ⟨55185822780195738849142625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36790548520130492566095083 55185822780195738849142625)
    ·
      refine ⟨41389367085146804136856969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55185822780195738849142625 41389367085146804136856969)
      ·
        refine ⟨31042025313860103102642727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41389367085146804136856969 31042025313860103102642727)
        ·
          refine ⟨46563037970790154653964091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31042025313860103102642727 46563037970790154653964091)
          ·
            refine ⟨69844556956185231980946137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46563037970790154653964091 69844556956185231980946137)
            ·
              refine ⟨52383417717138923985709603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69844556956185231980946137 52383417717138923985709603)
              ·
                refine ⟨78575126575708385978564405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52383417717138923985709603 78575126575708385978564405)
                ·
                  refine ⟨7366418116472661185490413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78575126575708385978564405 7366418116472661185490413)
                  ·
                    refine ⟨2762406793677247944558905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7366418116472661185490413 2762406793677247944558905)
                    ·
                      refine ⟨2071805095257935958419179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762406793677247944558905 2071805095257935958419179)
                      ·
                        rfl

theorem cell23_4034826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_4034826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034826 prefixEnd_4034826 := by exact prefixLift 4034826
  have htrace : WordTrace (prefixWord ++ tailWord_4034826) baseStart_4034826 baseEnd_4034826 := by
    simpa [prefixWord, tailWord_4034826, baseEnd_4034826] using wordTrace_append hprefix tailTrace_4034826
  have hstable : (prefixWord ++ tailWord_4034826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034826).length < 2 ^ (prefixWord ++ tailWord_4034826).sum := by decide
  have hdescent : baseEnd_4034826 < baseStart_4034826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034884 : List Nat := [2, 3, 4, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4034884 : Nat := 118140960795 + 4034884 * 2 ^ 59
def prefixEnd_4034884 : Nat := 4983230072969 + 3 ^ 40 * 4034884 * 2
def baseEnd_4034884 : Nat := 2071834877135896731493913

theorem tailTrace_4034884 : CollatzResearch.WordTrace tailWord_4034884 prefixEnd_4034884 2071834877135896731493913 := by
  unfold tailWord_4034884
  simp only [CollatzResearch.WordTrace]
  refine ⟨73582154757155923084995853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98109539676207897446661137 73582154757155923084995853)
  ·
    refine ⟨27593308033933471156873445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73582154757155923084995853 27593308033933471156873445)
    ·
      refine ⟨5173745256362525841913771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27593308033933471156873445 5173745256362525841913771)
      ·
        refine ⟨7760617884543788762870657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173745256362525841913771 7760617884543788762870657)
        ·
          refine ⟨5820463413407841572152993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760617884543788762870657 5820463413407841572152993)
          ·
            refine ⟨4365347560055881179114745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5820463413407841572152993 4365347560055881179114745)
            ·
              refine ⟨3274010670041910884336059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365347560055881179114745 3274010670041910884336059)
              ·
                refine ⟨4911016005062866326504089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274010670041910884336059 4911016005062866326504089)
                ·
                  refine ⟨3683262003797149744878067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911016005062866326504089 3683262003797149744878067)
                  ·
                    refine ⟨5524893005695724617317101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3683262003797149744878067 5524893005695724617317101)
                    ·
                      refine ⟨2071834877135896731493913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524893005695724617317101 2071834877135896731493913)
                      ·
                        rfl

theorem cell23_4034884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4034884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034884 prefixEnd_4034884 := by exact prefixLift 4034884
  have htrace : WordTrace (prefixWord ++ tailWord_4034884) baseStart_4034884 baseEnd_4034884 := by
    simpa [prefixWord, tailWord_4034884, baseEnd_4034884] using wordTrace_append hprefix tailTrace_4034884
  have hstable : (prefixWord ++ tailWord_4034884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034884).length < 2 ^ (prefixWord ++ tailWord_4034884).sum := by decide
  have hdescent : baseEnd_4034884 < baseStart_4034884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034889 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 3]
def baseStart_4034889 : Nat := 118140960795 + 4034889 * 2 ^ 59
def prefixEnd_4034889 : Nat := 4983230072969 + 3 ^ 40 * 4034889 * 2
def baseEnd_4034889 : Nat := 2071837444539169211931389

theorem tailTrace_4034889 : CollatzResearch.WordTrace tailWord_4034889 prefixEnd_4034889 2071837444539169211931389 := by
  unfold tailWord_4034889
  simp only [CollatzResearch.WordTrace]
  refine ⟨147164491879293732023923721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98109661252862488015949147 147164491879293732023923721)
  ·
    refine ⟨110373368909470299017942791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147164491879293732023923721 110373368909470299017942791)
    ·
      refine ⟨165560053364205448526914187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110373368909470299017942791 165560053364205448526914187)
      ·
        refine ⟨248340080046308172790371281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165560053364205448526914187 248340080046308172790371281)
        ·
          refine ⟨186255060034731129592778461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248340080046308172790371281 186255060034731129592778461)
          ·
            refine ⟨69845647513024173597291923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186255060034731129592778461 69845647513024173597291923)
            ·
              refine ⟨104768471269536260395937885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69845647513024173597291923 104768471269536260395937885)
              ·
                refine ⟨39288176726076097648476707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104768471269536260395937885 39288176726076097648476707)
                ·
                  refine ⟨58932265089114146472715061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39288176726076097648476707 58932265089114146472715061)
                  ·
                    refine ⟨5524899852104451231817037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58932265089114146472715061 5524899852104451231817037)
                    ·
                      refine ⟨2071837444539169211931389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5524899852104451231817037 2071837444539169211931389)
                      ·
                        rfl

theorem cell23_4034889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 5, 3].length) (baseStart_4034889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034889 prefixEnd_4034889 := by exact prefixLift 4034889
  have htrace : WordTrace (prefixWord ++ tailWord_4034889) baseStart_4034889 baseEnd_4034889 := by
    simpa [prefixWord, tailWord_4034889, baseEnd_4034889] using wordTrace_append hprefix tailTrace_4034889
  have hstable : (prefixWord ++ tailWord_4034889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034889).length < 2 ^ (prefixWord ++ tailWord_4034889).sum := by decide
  have hdescent : baseEnd_4034889 < baseStart_4034889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034929 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 4]
def baseStart_4034929 : Nat := 118140960795 + 4034929 * 2 ^ 59
def prefixEnd_4034929 : Nat := 4983230072969 + 3 ^ 40 * 4034929 * 2
def baseEnd_4034929 : Nat := 2071857983765349055431205

theorem tailTrace_4034929 : CollatzResearch.WordTrace tailWord_4034929 prefixEnd_4034929 2071857983765349055431205 := by
  unfold tailWord_4034929
  simp only [CollatzResearch.WordTrace]
  refine ⟨147165950799148818855379841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98110633866099212570253227 147165950799148818855379841)
  ·
    refine ⟨110374463099361614141534881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147165950799148818855379841 110374463099361614141534881)
    ·
      refine ⟨82780847324521210606151161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110374463099361614141534881 82780847324521210606151161)
      ·
        refine ⟨62085635493390907954613371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82780847324521210606151161 62085635493390907954613371)
        ·
          refine ⟨93128453240086361931920057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62085635493390907954613371 93128453240086361931920057)
          ·
            refine ⟨69846339930064771448940043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93128453240086361931920057 69846339930064771448940043)
            ·
              refine ⟨104769509895097157173410065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69846339930064771448940043 104769509895097157173410065)
              ·
                refine ⟨78577132421322867880057549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104769509895097157173410065 78577132421322867880057549)
                ·
                  refine ⟨29466424657996075455021581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78577132421322867880057549 29466424657996075455021581)
                  ·
                    refine ⟨11049909246748528295633093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29466424657996075455021581 11049909246748528295633093)
                    ·
                      refine ⟨2071857983765349055431205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11049909246748528295633093 2071857983765349055431205)
                      ·
                        rfl

theorem cell23_4034929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_4034929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034929 prefixEnd_4034929 := by exact prefixLift 4034929
  have htrace : WordTrace (prefixWord ++ tailWord_4034929) baseStart_4034929 baseEnd_4034929 := by
    simpa [prefixWord, tailWord_4034929, baseEnd_4034929] using wordTrace_append hprefix tailTrace_4034929
  have hstable : (prefixWord ++ tailWord_4034929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034929).length < 2 ^ (prefixWord ++ tailWord_4034929).sum := by decide
  have hdescent : baseEnd_4034929 < baseStart_4034929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034930 : List Nat := [3, 2, 1, 2, 1, 5, 2, 2, 5]
def baseStart_4034930 : Nat := 118140960795 + 4034930 * 2 ^ 59
def prefixEnd_4034930 : Nat := 4983230072969 + 3 ^ 40 * 4034930 * 2
def baseEnd_4034930 : Nat := 230206499694000394613189

theorem tailTrace_4034930 : CollatzResearch.WordTrace tailWord_4034930 prefixEnd_4034930 230206499694000394613189 := by
  unfold tailWord_4034930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36791496818036299006541561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98110658181430130684110829 36791496818036299006541561)
  ·
    refine ⟨27593622613527224254906171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36791496818036299006541561 27593622613527224254906171)
    ·
      refine ⟨41390433920290836382359257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27593622613527224254906171 41390433920290836382359257)
      ·
        refine ⟨31042825440218127286769443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41390433920290836382359257 31042825440218127286769443)
        ·
          refine ⟨46564238160327190930154165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31042825440218127286769443 46564238160327190930154165)
          ·
            refine ⟨4365397327530674149701953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46564238160327190930154165 4365397327530674149701953)
            ·
              refine ⟨3274047995648005612276465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4365397327530674149701953 3274047995648005612276465)
              ·
                refine ⟨2455535996736004209207349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274047995648005612276465 2455535996736004209207349)
                ·
                  refine ⟨230206499694000394613189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455535996736004209207349 230206499694000394613189)
                  ·
                    rfl

theorem cell23_4034930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_4034930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034930 prefixEnd_4034930 := by exact prefixLift 4034930
  have htrace : WordTrace (prefixWord ++ tailWord_4034930) baseStart_4034930 baseEnd_4034930 := by
    simpa [prefixWord, tailWord_4034930, baseEnd_4034930] using wordTrace_append hprefix tailTrace_4034930
  have hstable : (prefixWord ++ tailWord_4034930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034930).length < 2 ^ (prefixWord ++ tailWord_4034930).sum := by decide
  have hdescent : baseEnd_4034930 < baseStart_4034930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034933 : List Nat := [1, 3, 4, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_4034933 : Nat := 118140960795 + 4034933 * 2 ^ 59
def prefixEnd_4034933 : Nat := 4983230072969 + 3 ^ 40 * 4034933 * 2
def baseEnd_4034933 : Nat := 2071860037687967039781187

theorem tailTrace_4034933 : CollatzResearch.WordTrace tailWord_4034933 prefixEnd_4034933 2071860037687967039781187 := by
  unfold tailWord_4034933
  simp only [CollatzResearch.WordTrace]
  refine ⟨147166096691134327538525453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98110731127422885025683635 147166096691134327538525453)
  ·
    refine ⟨55187286259175372826947045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147166096691134327538525453 55187286259175372826947045)
    ·
      refine ⟨10347616173595382405052571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55187286259175372826947045 10347616173595382405052571)
      ·
        refine ⟨15521424260393073607578857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10347616173595382405052571 15521424260393073607578857)
        ·
          refine ⟨11641068195294805205684143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15521424260393073607578857 11641068195294805205684143)
          ·
            refine ⟨17461602292942207808526215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11641068195294805205684143 17461602292942207808526215)
            ·
              refine ⟨26192403439413311712789323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461602292942207808526215 26192403439413311712789323)
              ·
                refine ⟨39288605159119967569183985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26192403439413311712789323 39288605159119967569183985)
                ·
                  refine ⟨29466453869339975676887989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39288605159119967569183985 29466453869339975676887989)
                  ·
                    refine ⟨2762480050250622719708249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29466453869339975676887989 2762480050250622719708249)
                    ·
                      refine ⟨2071860037687967039781187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762480050250622719708249 2071860037687967039781187)
                      ·
                        rfl

theorem cell23_4034933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_4034933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034933 prefixEnd_4034933 := by exact prefixLift 4034933
  have htrace : WordTrace (prefixWord ++ tailWord_4034933) baseStart_4034933 baseEnd_4034933 := by
    simpa [prefixWord, tailWord_4034933, baseEnd_4034933] using wordTrace_append hprefix tailTrace_4034933
  have hstable : (prefixWord ++ tailWord_4034933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034933).length < 2 ^ (prefixWord ++ tailWord_4034933).sum := by decide
  have hdescent : baseEnd_4034933 < baseStart_4034933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034956 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 5, 4]
def baseStart_4034956 : Nat := 118140960795 + 4034956 * 2 ^ 59
def prefixEnd_4034956 : Nat := 4983230072969 + 3 ^ 40 * 4034956 * 2
def baseEnd_4034956 : Nat := 690623949247673483264527

theorem tailTrace_4034956 : CollatzResearch.WordTrace tailWord_4034956 prefixEnd_4034956 690623949247673483264527 := by
  unfold tailWord_4034956
  simp only [CollatzResearch.WordTrace]
  refine ⟨73583467785025501233306361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98111290380034001644408481 73583467785025501233306361)
  ·
    refine ⟨55187600838769125924979771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73583467785025501233306361 55187600838769125924979771)
    ·
      refine ⟨82781401258153688887469657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55187600838769125924979771 82781401258153688887469657)
      ·
        refine ⟨62086050943615266665602243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82781401258153688887469657 62086050943615266665602243)
        ·
          refine ⟨93129076415422899998403365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62086050943615266665602243 93129076415422899998403365)
          ·
            refine ⟨17461701827891793749700631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93129076415422899998403365 17461701827891793749700631)
            ·
              refine ⟨26192552741837690624550947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461701827891793749700631 26192552741837690624550947)
              ·
                refine ⟨39288829112756535936826421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26192552741837690624550947 39288829112756535936826421)
                ·
                  refine ⟨3683327729320925244077477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39288829112756535936826421 3683327729320925244077477)
                  ·
                    refine ⟨690623949247673483264527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3683327729320925244077477 690623949247673483264527)
                    ·
                      rfl

theorem cell23_4034956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 5, 4].length) (baseStart_4034956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034956 prefixEnd_4034956 := by exact prefixLift 4034956
  have htrace : WordTrace (prefixWord ++ tailWord_4034956) baseStart_4034956 baseEnd_4034956 := by
    simpa [prefixWord, tailWord_4034956, baseEnd_4034956] using wordTrace_append hprefix tailTrace_4034956
  have hstable : (prefixWord ++ tailWord_4034956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034956).length < 2 ^ (prefixWord ++ tailWord_4034956).sum := by decide
  have hdescent : baseEnd_4034956 < baseStart_4034956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4034969 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 8]
def baseStart_4034969 : Nat := 118140960795 + 4034969 * 2 ^ 59
def prefixEnd_4034969 : Nat := 4983230072969 + 3 ^ 40 * 4034969 * 2
def baseEnd_4034969 : Nat := 230208724776836544325669

theorem tailTrace_4034969 : CollatzResearch.WordTrace tailWord_4034969 prefixEnd_4034969 230208724776836544325669 := by
  unfold tailWord_4034969
  simp only [CollatzResearch.WordTrace]
  refine ⟨147167409719003905686835961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98111606479335937124557307 147167409719003905686835961)
  ·
    refine ⟨110375557289252929265126971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147167409719003905686835961 110375557289252929265126971)
    ·
      refine ⟨165563335933879393897690457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110375557289252929265126971 165563335933879393897690457)
      ·
        refine ⟨124172501950409545423267843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165563335933879393897690457 124172501950409545423267843)
        ·
          refine ⟨186258752925614318134901765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124172501950409545423267843 186258752925614318134901765)
          ·
            refine ⟨34923516173552684650294081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186258752925614318134901765 34923516173552684650294081)
            ·
              refine ⟨26192637130164513487720561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34923516173552684650294081 26192637130164513487720561)
              ·
                refine ⟨19644477847623385115790421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26192637130164513487720561 19644477847623385115790421)
                ·
                  refine ⟨230208724776836544325669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19644477847623385115790421 230208724776836544325669)
                  ·
                    rfl

theorem cell23_4034969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 8].length) (baseStart_4034969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4034969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4034969 prefixEnd_4034969 := by exact prefixLift 4034969
  have htrace : WordTrace (prefixWord ++ tailWord_4034969) baseStart_4034969 baseEnd_4034969 := by
    simpa [prefixWord, tailWord_4034969, baseEnd_4034969] using wordTrace_append hprefix tailTrace_4034969
  have hstable : (prefixWord ++ tailWord_4034969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4034969).length < 2 ^ (prefixWord ++ tailWord_4034969).sum := by decide
  have hdescent : baseEnd_4034969 < baseStart_4034969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4034969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035023 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 2, 3, 2]
def baseStart_4035023 : Nat := 118140960795 + 4035023 * 2 ^ 59
def prefixEnd_4035023 : Nat := 4983230072969 + 3 ^ 40 * 4035023 * 2
def baseEnd_4035023 : Nat := 2071906250946871687655773

theorem tailTrace_4035023 : CollatzResearch.WordTrace tailWord_4035023 prefixEnd_4035023 2071906250946871687655773 := by
  unfold tailWord_4035023
  simp only [CollatzResearch.WordTrace]
  refine ⟨147169379260808272909301723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98112919507205515272867815 147169379260808272909301723)
  ·
    refine ⟨220754068891212409363952585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147169379260808272909301723 220754068891212409363952585)
    ·
      refine ⟨165565551668409307022964439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220754068891212409363952585 165565551668409307022964439)
      ·
        refine ⟨248348327502613960534446659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165565551668409307022964439 248348327502613960534446659)
        ·
          refine ⟨372522491253920940801669989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248348327502613960534446659 372522491253920940801669989)
          ·
            refine ⟨69847967110110176400313123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372522491253920940801669989 69847967110110176400313123)
            ·
              refine ⟨104771950665165264600469685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69847967110110176400313123 104771950665165264600469685)
              ·
                refine ⟨9822370374859243556294033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104771950665165264600469685 9822370374859243556294033)
                ·
                  refine ⟨7366777781144432667220525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9822370374859243556294033 7366777781144432667220525)
                  ·
                    refine ⟨2762541667929162250207697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7366777781144432667220525 2762541667929162250207697)
                    ·
                      refine ⟨2071906250946871687655773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762541667929162250207697 2071906250946871687655773)
                      ·
                        rfl

theorem cell23_4035023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 2, 3, 2].length) (baseStart_4035023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035023 prefixEnd_4035023 := by exact prefixLift 4035023
  have htrace : WordTrace (prefixWord ++ tailWord_4035023) baseStart_4035023 baseEnd_4035023 := by
    simpa [prefixWord, tailWord_4035023, baseEnd_4035023] using wordTrace_append hprefix tailTrace_4035023
  have hstable : (prefixWord ++ tailWord_4035023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035023).length < 2 ^ (prefixWord ++ tailWord_4035023).sum := by decide
  have hdescent : baseEnd_4035023 < baseStart_4035023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035056 : List Nat := [2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_4035056 : Nat := 118140960795 + 4035056 * 2 ^ 59
def prefixEnd_4035056 : Nat := 4983230072969 + 3 ^ 40 * 4035056 * 2
def baseEnd_4035056 : Nat := 2071923195808470058543121

theorem tailTrace_4035056 : CollatzResearch.WordTrace tailWord_4035056 prefixEnd_4035056 2071923195808470058543121 := by
  unfold tailWord_4035056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73585291434844359772626511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98113721913125813030168681 73585291434844359772626511)
  ·
    refine ⟨110377937152266539658939767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73585291434844359772626511 110377937152266539658939767)
    ·
      refine ⟨165566905728399809488409651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110377937152266539658939767 165566905728399809488409651)
      ·
        refine ⟨248350358592599714232614477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165566905728399809488409651 248350358592599714232614477)
        ·
          refine ⟨93131384472224892837230429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248350358592599714232614477 93131384472224892837230429)
          ·
            refine ⟨34924269177084334813961411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93131384472224892837230429 34924269177084334813961411)
            ·
              refine ⟨52386403765626502220942117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34924269177084334813961411 52386403765626502220942117)
              ·
                refine ⟨9822450706054969166426647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52386403765626502220942117 9822450706054969166426647)
                ·
                  refine ⟨14733676059082453749639971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822450706054969166426647 14733676059082453749639971)
                  ·
                    refine ⟨22100514088623680624459957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14733676059082453749639971 22100514088623680624459957)
                    ·
                      refine ⟨2071923195808470058543121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22100514088623680624459957 2071923195808470058543121)
                      ·
                        rfl

theorem cell23_4035056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_4035056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035056 prefixEnd_4035056 := by exact prefixLift 4035056
  have htrace : WordTrace (prefixWord ++ tailWord_4035056) baseStart_4035056 baseEnd_4035056 := by
    simpa [prefixWord, tailWord_4035056, baseEnd_4035056] using wordTrace_append hprefix tailTrace_4035056
  have hstable : (prefixWord ++ tailWord_4035056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035056).length < 2 ^ (prefixWord ++ tailWord_4035056).sum := by decide
  have hdescent : baseEnd_4035056 < baseStart_4035056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035074 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4035074 : Nat := 118140960795 + 4035074 * 2 ^ 59
def prefixEnd_4035074 : Nat := 4983230072969 + 3 ^ 40 * 4035074 * 2
def baseEnd_4035074 : Nat := 2071932438460250988118039

theorem tailTrace_4035074 : CollatzResearch.WordTrace tailWord_4035074 prefixEnd_4035074 2071932438460250988118039 := by
  unfold tailWord_4035074
  simp only [CollatzResearch.WordTrace]
  refine ⟨36792809845905877154852069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98114159589082339079605517 36792809845905877154852069)
  ·
    refine ⟨6898651846107351966534763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36792809845905877154852069 6898651846107351966534763)
    ·
      refine ⟨10347977769161027949802145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898651846107351966534763 10347977769161027949802145)
      ·
        refine ⟨7760983326870770962351609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10347977769161027949802145 7760983326870770962351609)
        ·
          refine ⟨5820737495153078221763707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7760983326870770962351609 5820737495153078221763707)
          ·
            refine ⟨8731106242729617332645561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820737495153078221763707 8731106242729617332645561)
            ·
              refine ⟨6548329682047212999484171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8731106242729617332645561 6548329682047212999484171)
              ·
                refine ⟨9822494523070819499226257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548329682047212999484171 9822494523070819499226257)
                ·
                  refine ⟨7366870892303114624419693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9822494523070819499226257 7366870892303114624419693)
                  ·
                    refine ⟨2762576584613667984157385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7366870892303114624419693 2762576584613667984157385)
                    ·
                      refine ⟨2071932438460250988118039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762576584613667984157385 2071932438460250988118039)
                      ·
                        rfl

theorem cell23_4035074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4035074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035074 prefixEnd_4035074 := by exact prefixLift 4035074
  have htrace : WordTrace (prefixWord ++ tailWord_4035074) baseStart_4035074 baseEnd_4035074 := by
    simpa [prefixWord, tailWord_4035074, baseEnd_4035074] using wordTrace_append hprefix tailTrace_4035074
  have hstable : (prefixWord ++ tailWord_4035074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035074).length < 2 ^ (prefixWord ++ tailWord_4035074).sum := by decide
  have hdescent : baseEnd_4035074 < baseStart_4035074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035083 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4]
def baseStart_4035083 : Nat := 118140960795 + 4035083 * 2 ^ 59
def prefixEnd_4035083 : Nat := 4983230072969 + 3 ^ 40 * 4035083 * 2
def baseEnd_4035083 : Nat := 2071937059786141452905497

theorem tailTrace_4035083 : CollatzResearch.WordTrace tailWord_4035083 prefixEnd_4035083 2071937059786141452905497 := by
  unfold tailWord_4035083
  simp only [CollatzResearch.WordTrace]
  refine ⟨147171567640590903156485903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98114378427060602104323935 147171567640590903156485903)
  ·
    refine ⟨220757351460886354734728855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147171567640590903156485903 220757351460886354734728855)
    ·
      refine ⟨331136027191329532102093283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220757351460886354734728855 331136027191329532102093283)
      ·
        refine ⟨496704040786994298153139925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331136027191329532102093283 496704040786994298153139925)
        ·
          refine ⟨11641500955945178862964217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 496704040786994298153139925 11641500955945178862964217)
          ·
            refine ⟨8731125716958884147223163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11641500955945178862964217 8731125716958884147223163)
            ·
              refine ⟨13096688575438326220834745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731125716958884147223163 13096688575438326220834745)
              ·
                refine ⟨9822516431578744665626059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13096688575438326220834745 9822516431578744665626059)
                ·
                  refine ⟨14733774647368116998439089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9822516431578744665626059 14733774647368116998439089)
                  ·
                    refine ⟨11050330985526087748829317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14733774647368116998439089 11050330985526087748829317)
                    ·
                      refine ⟨2071937059786141452905497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11050330985526087748829317 2071937059786141452905497)
                      ·
                        rfl

theorem cell23_4035083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_4035083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035083 prefixEnd_4035083 := by exact prefixLift 4035083
  have htrace : WordTrace (prefixWord ++ tailWord_4035083) baseStart_4035083 baseEnd_4035083 := by
    simpa [prefixWord, tailWord_4035083, baseEnd_4035083] using wordTrace_append hprefix tailTrace_4035083
  have hstable : (prefixWord ++ tailWord_4035083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035083).length < 2 ^ (prefixWord ++ tailWord_4035083).sum := by decide
  have hdescent : baseEnd_4035083 < baseStart_4035083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035120 : List Nat := [2, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3]
def baseStart_4035120 : Nat := 118140960795 + 4035120 * 2 ^ 59
def prefixEnd_4035120 : Nat := 4983230072969 + 3 ^ 40 * 4035120 * 2
def baseEnd_4035120 : Nat := 2071956058570357808142827

theorem tailTrace_4035120 : CollatzResearch.WordTrace tailWord_4035120 prefixEnd_4035120 2071956058570357808142827 := by
  unfold tailWord_4035120
  simp only [CollatzResearch.WordTrace]
  refine ⟨73586458570728429237791407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98115278094304572317055209 73586458570728429237791407)
  ·
    refine ⟨110379687856092643856687111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73586458570728429237791407 110379687856092643856687111)
    ·
      refine ⟨165569531784138965785030667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110379687856092643856687111 165569531784138965785030667)
      ·
        refine ⟨248354297676208448677546001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165569531784138965785030667 248354297676208448677546001)
        ·
          refine ⟨186265723257156336508159501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248354297676208448677546001 186265723257156336508159501)
          ·
            refine ⟨69849646221433626190559813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186265723257156336508159501 69849646221433626190559813)
            ·
              refine ⟨13096808666518804910729965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69849646221433626190559813 13096808666518804910729965)
              ·
                refine ⟨4911303249944551841523737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13096808666518804910729965 4911303249944551841523737)
                ·
                  refine ⟨3683477437458413881142803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4911303249944551841523737 3683477437458413881142803)
                  ·
                    refine ⟨5525216156187620821714205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3683477437458413881142803 5525216156187620821714205)
                    ·
                      refine ⟨2071956058570357808142827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5525216156187620821714205 2071956058570357808142827)
                      ·
                        rfl

theorem cell23_4035120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 2, 1, 3].length) (baseStart_4035120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035120 prefixEnd_4035120 := by exact prefixLift 4035120
  have htrace : WordTrace (prefixWord ++ tailWord_4035120) baseStart_4035120 baseEnd_4035120 := by
    simpa [prefixWord, tailWord_4035120, baseEnd_4035120] using wordTrace_append hprefix tailTrace_4035120
  have hstable : (prefixWord ++ tailWord_4035120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035120).length < 2 ^ (prefixWord ++ tailWord_4035120).sum := by decide
  have hdescent : baseEnd_4035120 < baseStart_4035120 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035130 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2]
def baseStart_4035130 : Nat := 118140960795 + 4035130 * 2 ^ 59
def prefixEnd_4035130 : Nat := 4983230072969 + 3 ^ 40 * 4035130 * 2
def baseEnd_4035130 : Nat := 2071961193376902769017781

theorem tailTrace_4035130 : CollatzResearch.WordTrace tailWord_4035130 prefixEnd_4035130 2071961193376902769017781 := by
  unfold tailWord_4035130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36793320467855157545861711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98115521247613753455631229 36793320467855157545861711)
  ·
    refine ⟨55189980701782736318792567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36793320467855157545861711 55189980701782736318792567)
    ·
      refine ⟨82784971052674104478188851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55189980701782736318792567 82784971052674104478188851)
      ·
        refine ⟨124177456579011156717283277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82784971052674104478188851 124177456579011156717283277)
        ·
          refine ⟨46566546217129183768981229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124177456579011156717283277 46566546217129183768981229)
          ·
            refine ⟨17462454831423443913367961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46566546217129183768981229 17462454831423443913367961)
            ·
              refine ⟨13096841123567582935025971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17462454831423443913367961 13096841123567582935025971)
              ·
                refine ⟨19645261685351374402538957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13096841123567582935025971 19645261685351374402538957)
                ·
                  refine ⟨7366973132006765400952109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19645261685351374402538957 7366973132006765400952109)
                  ·
                    refine ⟨2762614924502537025357041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7366973132006765400952109 2762614924502537025357041)
                    ·
                      refine ⟨2071961193376902769017781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762614924502537025357041 2071961193376902769017781)
                      ·
                        rfl

theorem cell23_4035130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_4035130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035130 prefixEnd_4035130 := by exact prefixLift 4035130
  have htrace : WordTrace (prefixWord ++ tailWord_4035130) baseStart_4035130 baseEnd_4035130 := by
    simpa [prefixWord, tailWord_4035130, baseEnd_4035130] using wordTrace_append hprefix tailTrace_4035130
  have hstable : (prefixWord ++ tailWord_4035130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035130).length < 2 ^ (prefixWord ++ tailWord_4035130).sum := by decide
  have hdescent : baseEnd_4035130 < baseStart_4035130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035147 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 1, 3, 2]
def baseStart_4035147 : Nat := 118140960795 + 4035147 * 2 ^ 59
def prefixEnd_4035147 : Nat := 4983230072969 + 3 ^ 40 * 4035147 * 2
def baseEnd_4035147 : Nat := 2071969922548029202505203

theorem tailTrace_4035147 : CollatzResearch.WordTrace tailWord_4035147 prefixEnd_4035147 2071969922548029202505203 := by
  unfold tailWord_4035147
  simp only [CollatzResearch.WordTrace]
  refine ⟨147173901912359042086815695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98115934608239361391210463 147173901912359042086815695)
  ·
    refine ⟨220760852868538563130223543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147173901912359042086815695 220760852868538563130223543)
    ·
      refine ⟨331141279302807844695335315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220760852868538563130223543 331141279302807844695335315)
      ·
        refine ⟨496711918954211767043002973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331141279302807844695335315 496711918954211767043002973)
        ·
          refine ⟨186266969607829412641126115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496711918954211767043002973 186266969607829412641126115)
          ·
            refine ⟨279400454411744118961689173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186266969607829412641126115 279400454411744118961689173)
            ·
              refine ⟨3274224075137626394082295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 279400454411744118961689173 3274224075137626394082295)
              ·
                refine ⟨4911336112706439591123443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274224075137626394082295 4911336112706439591123443)
                ·
                  refine ⟨7367004169059659386685165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911336112706439591123443 7367004169059659386685165)
                  ·
                    refine ⟨2762626563397372270006937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7367004169059659386685165 2762626563397372270006937)
                    ·
                      refine ⟨2071969922548029202505203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762626563397372270006937 2071969922548029202505203)
                      ·
                        rfl

theorem cell23_4035147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 1, 3, 2].length) (baseStart_4035147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035147 prefixEnd_4035147 := by exact prefixLift 4035147
  have htrace : WordTrace (prefixWord ++ tailWord_4035147) baseStart_4035147 baseEnd_4035147 := by
    simpa [prefixWord, tailWord_4035147, baseEnd_4035147] using wordTrace_append hprefix tailTrace_4035147
  have hstable : (prefixWord ++ tailWord_4035147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035147).length < 2 ^ (prefixWord ++ tailWord_4035147).sum := by decide
  have hdescent : baseEnd_4035147 < baseStart_4035147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035200 : List Nat := [2, 1, 1, 2, 1, 5, 3, 3, 5]
def baseStart_4035200 : Nat := 118140960795 + 4035200 * 2 ^ 59
def prefixEnd_4035200 : Nat := 4983230072969 + 3 ^ 40 * 4035200 * 2
def baseEnd_4035200 : Nat := 230221904113635277238051

theorem tailTrace_4035200 : CollatzResearch.WordTrace tailWord_4035200 prefixEnd_4035200 230221904113635277238051 := by
  unfold tailWord_4035200
  simp only [CollatzResearch.WordTrace]
  refine ⟨73587917490583516069247527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98117223320778021425663369 73587917490583516069247527)
  ·
    refine ⟨110381876235875274103871291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73587917490583516069247527 110381876235875274103871291)
    ·
      refine ⟨165572814353812911155806937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110381876235875274103871291 165572814353812911155806937)
      ·
        refine ⟨124179610765359683366855203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165572814353812911155806937 124179610765359683366855203)
        ·
          refine ⟨186269416148039525050282805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124179610765359683366855203 186269416148039525050282805)
          ·
            refine ⟨17462757763878705473464013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186269416148039525050282805 17462757763878705473464013)
            ·
              refine ⟨6548534161454514552549005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17462757763878705473464013 6548534161454514552549005)
              ·
                refine ⟨2455700310545442957205877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6548534161454514552549005 2455700310545442957205877)
                ·
                  refine ⟨230221904113635277238051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2455700310545442957205877 230221904113635277238051)
                  ·
                    rfl

theorem cell23_4035200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 3, 3, 5].length) (baseStart_4035200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035200 prefixEnd_4035200 := by exact prefixLift 4035200
  have htrace : WordTrace (prefixWord ++ tailWord_4035200) baseStart_4035200 baseEnd_4035200 := by
    simpa [prefixWord, tailWord_4035200, baseEnd_4035200] using wordTrace_append hprefix tailTrace_4035200
  have hstable : (prefixWord ++ tailWord_4035200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035200).length < 2 ^ (prefixWord ++ tailWord_4035200).sum := by decide
  have hdescent : baseEnd_4035200 < baseStart_4035200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035216 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_4035216 : Nat := 118140960795 + 4035216 * 2 ^ 59
def prefixEnd_4035216 : Nat := 4983230072969 + 3 ^ 40 * 4035216 * 2
def baseEnd_4035216 : Nat := 2072005352713189432542385

theorem tailTrace_4035216 : CollatzResearch.WordTrace tailWord_4035216 prefixEnd_4035216 2072005352713189432542385 := by
  unfold tailWord_4035216
  simp only [CollatzResearch.WordTrace]
  refine ⟨73588209274554533435538751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98117612366072711247385001 73588209274554533435538751)
  ·
    refine ⟨110382313911831800153308127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73588209274554533435538751 110382313911831800153308127)
    ·
      refine ⟨165573470867747700229962191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110382313911831800153308127 165573470867747700229962191)
      ·
        refine ⟨248360206301621550344943287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165573470867747700229962191 248360206301621550344943287)
        ·
          refine ⟨372540309452432325517414931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248360206301621550344943287 372540309452432325517414931)
          ·
            refine ⟨558810464178648488276122397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372540309452432325517414931 558810464178648488276122397)
            ·
              refine ⟨209553924066993183103545899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558810464178648488276122397 209553924066993183103545899)
              ·
                refine ⟨314330886100489774655318849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209553924066993183103545899 314330886100489774655318849)
                ·
                  refine ⟨235748164575367330991489137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314330886100489774655318849 235748164575367330991489137)
                  ·
                    refine ⟨176811123431525498243616853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235748164575367330991489137 176811123431525498243616853)
                    ·
                      refine ⟨2072005352713189432542385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 176811123431525498243616853 2072005352713189432542385)
                      ·
                        rfl

theorem cell23_4035216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_4035216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035216 prefixEnd_4035216 := by exact prefixLift 4035216
  have htrace : WordTrace (prefixWord ++ tailWord_4035216) baseStart_4035216 baseEnd_4035216 := by
    simpa [prefixWord, tailWord_4035216, baseEnd_4035216] using wordTrace_append hprefix tailTrace_4035216
  have hstable : (prefixWord ++ tailWord_4035216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035216).length < 2 ^ (prefixWord ++ tailWord_4035216).sum := by decide
  have hdescent : baseEnd_4035216 < baseStart_4035216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035223 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4035223 : Nat := 118140960795 + 4035223 * 2 ^ 59
def prefixEnd_4035223 : Nat := 4983230072969 + 3 ^ 40 * 4035223 * 2
def baseEnd_4035223 : Nat := 2072008947077770905154853

theorem tailTrace_4035223 : CollatzResearch.WordTrace tailWord_4035223 prefixEnd_4035223 2072008947077770905154853 := by
  unfold tailWord_4035223
  simp only [CollatzResearch.WordTrace]
  refine ⟨147176673860083707066582323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98117782573389138044388215 147176673860083707066582323)
  ·
    refine ⟨220765010790125560599873485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147176673860083707066582323 220765010790125560599873485)
    ·
      refine ⟨82786879046297085224952557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220765010790125560599873485 82786879046297085224952557)
      ·
        refine ⟨31045079642361406959357209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82786879046297085224952557 31045079642361406959357209)
        ·
          refine ⟨23283809731771055219517907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31045079642361406959357209 23283809731771055219517907)
          ·
            refine ⟨34925714597656582829276861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283809731771055219517907 34925714597656582829276861)
            ·
              refine ⟨13097142974121218560978823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34925714597656582829276861 13097142974121218560978823)
              ·
                refine ⟨19645714461181827841468235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13097142974121218560978823 19645714461181827841468235)
                ·
                  refine ⟨29468571691772741762202353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19645714461181827841468235 29468571691772741762202353)
                  ·
                    refine ⟨22101428768829556321651765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29468571691772741762202353 22101428768829556321651765)
                    ·
                      refine ⟨2072008947077770905154853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22101428768829556321651765 2072008947077770905154853)
                      ·
                        rfl

theorem cell23_4035223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4035223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035223 prefixEnd_4035223 := by exact prefixLift 4035223
  have htrace : WordTrace (prefixWord ++ tailWord_4035223) baseStart_4035223 baseEnd_4035223 := by
    simpa [prefixWord, tailWord_4035223, baseEnd_4035223] using wordTrace_append hprefix tailTrace_4035223
  have hstable : (prefixWord ++ tailWord_4035223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035223).length < 2 ^ (prefixWord ++ tailWord_4035223).sum := by decide
  have hdescent : baseEnd_4035223 < baseStart_4035223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035230 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_4035230 : Nat := 118140960795 + 4035230 * 2 ^ 59
def prefixEnd_4035230 : Nat := 4983230072969 + 3 ^ 40 * 4035230 * 2
def baseEnd_4035230 : Nat := 690670847147450792589107

theorem tailTrace_4035230 : CollatzResearch.WordTrace tailWord_4035230 prefixEnd_4035230 690670847147450792589107 := by
  unfold tailWord_4035230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397116146382293407760893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98117952780705564841391429 18397116146382293407760893)
  ·
    refine ⟨6898918554893360027910335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18397116146382293407760893 6898918554893360027910335)
    ·
      refine ⟨10348377832340040041865503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898918554893360027910335 10348377832340040041865503)
      ·
        refine ⟨15522566748510060062798255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10348377832340040041865503 15522566748510060062798255)
        ·
          refine ⟨23283850122765090094197383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15522566748510060062798255 23283850122765090094197383)
          ·
            refine ⟨34925775184147635141296075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23283850122765090094197383 34925775184147635141296075)
            ·
              refine ⟨52388662776221452711944113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34925775184147635141296075 52388662776221452711944113)
              ·
                refine ⟨39291497082166089533958085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52388662776221452711944113 39291497082166089533958085)
                ·
                  refine ⟨7367155702906141787617141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39291497082166089533958085 7367155702906141787617141)
                  ·
                    refine ⟨690670847147450792589107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7367155702906141787617141 690670847147450792589107)
                    ·
                      rfl

theorem cell23_4035230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_4035230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035230 prefixEnd_4035230 := by exact prefixLift 4035230
  have htrace : WordTrace (prefixWord ++ tailWord_4035230) baseStart_4035230 baseEnd_4035230 := by
    simpa [prefixWord, tailWord_4035230, baseEnd_4035230] using wordTrace_append hprefix tailTrace_4035230
  have hstable : (prefixWord ++ tailWord_4035230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035230).length < 2 ^ (prefixWord ++ tailWord_4035230).sum := by decide
  have hdescent : baseEnd_4035230 < baseStart_4035230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035250 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_4035250 : Nat := 118140960795 + 4035250 * 2 ^ 59
def prefixEnd_4035250 : Nat := 4983230072969 + 3 ^ 40 * 4035250 * 2
def baseEnd_4035250 : Nat := 2072022811055442299517229

theorem tailTrace_4035250 : CollatzResearch.WordTrace tailWord_4035250 prefixEnd_4035250 2072022811055442299517229 := by
  unfold tailWord_4035250
  simp only [CollatzResearch.WordTrace]
  refine ⟨36794414657746472669453801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98118439087323927118543469 36794414657746472669453801)
  ·
    refine ⟨27595810993309854502090351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36794414657746472669453801 27595810993309854502090351)
    ·
      refine ⟨41393716489964781753135527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27595810993309854502090351 41393716489964781753135527)
      ·
        refine ⟨62090574734947172629703291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41393716489964781753135527 62090574734947172629703291)
        ·
          refine ⟨93135862102420758944554937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62090574734947172629703291 93135862102420758944554937)
          ·
            refine ⟨69851896576815569208416203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93135862102420758944554937 69851896576815569208416203)
            ·
              refine ⟨104777844865223353812624305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69851896576815569208416203 104777844865223353812624305)
              ·
                refine ⟨78583383648917515359468229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104777844865223353812624305 78583383648917515359468229)
                ·
                  refine ⟨14734384434172034129900293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78583383648917515359468229 14734384434172034129900293)
                  ·
                    refine ⟨2762697081407256399356305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14734384434172034129900293 2762697081407256399356305)
                    ·
                      refine ⟨2072022811055442299517229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762697081407256399356305 2072022811055442299517229)
                      ·
                        rfl

theorem cell23_4035250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_4035250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035250 prefixEnd_4035250 := by exact prefixLift 4035250
  have htrace : WordTrace (prefixWord ++ tailWord_4035250) baseStart_4035250 baseEnd_4035250 := by
    simpa [prefixWord, tailWord_4035250, baseEnd_4035250] using wordTrace_append hprefix tailTrace_4035250
  have hstable : (prefixWord ++ tailWord_4035250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035250).length < 2 ^ (prefixWord ++ tailWord_4035250).sum := by decide
  have hdescent : baseEnd_4035250 < baseStart_4035250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035284 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4035284 : Nat := 118140960795 + 4035284 * 2 ^ 59
def prefixEnd_4035284 : Nat := 4983230072969 + 3 ^ 40 * 4035284 * 2
def baseEnd_4035284 : Nat := 2072040269397695166492073

theorem tailTrace_4035284 : CollatzResearch.WordTrace tailWord_4035284 prefixEnd_4035284 2072040269397695166492073 := by
  unfold tailWord_4035284
  simp only [CollatzResearch.WordTrace]
  refine ⟨73589449356431357242276453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98119265808575142989701937 73589449356431357242276453)
  ·
    refine ⟨13798021754330879482926835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73589449356431357242276453 13798021754330879482926835)
    ·
      refine ⟨20697032631496319224390253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13798021754330879482926835 20697032631496319224390253)
      ·
        refine ⟨7761387236811119709146345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20697032631496319224390253 7761387236811119709146345)
        ·
          refine ⟨5821040427608339781859759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7761387236811119709146345 5821040427608339781859759)
          ·
            refine ⟨8731560641412509672789639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821040427608339781859759 8731560641412509672789639)
            ·
              refine ⟨13097340962118764509184459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8731560641412509672789639 13097340962118764509184459)
              ·
                refine ⟨19646011443178146763776689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13097340962118764509184459 19646011443178146763776689)
                ·
                  refine ⟨14734508582383610072832517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19646011443178146763776689 14734508582383610072832517)
                  ·
                    refine ⟨2762720359196926888656097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14734508582383610072832517 2762720359196926888656097)
                    ·
                      refine ⟨2072040269397695166492073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762720359196926888656097 2072040269397695166492073)
                      ·
                        rfl

theorem cell23_4035284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4035284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035284 prefixEnd_4035284 := by exact prefixLift 4035284
  have htrace : WordTrace (prefixWord ++ tailWord_4035284) baseStart_4035284 baseEnd_4035284 := by
    simpa [prefixWord, tailWord_4035284, baseEnd_4035284] using wordTrace_append hprefix tailTrace_4035284
  have hstable : (prefixWord ++ tailWord_4035284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035284).length < 2 ^ (prefixWord ++ tailWord_4035284).sum := by decide
  have hdescent : baseEnd_4035284 < baseStart_4035284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035304 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_4035304 : Nat := 118140960795 + 4035304 * 2 ^ 59
def prefixEnd_4035304 : Nat := 4983230072969 + 3 ^ 40 * 4035304 * 2
def baseEnd_4035304 : Nat := 2072050539010785088241981

theorem tailTrace_4035304 : CollatzResearch.WordTrace tailWord_4035304 prefixEnd_4035304 2072050539010785088241981 := by
  unfold tailWord_4035304
  simp only [CollatzResearch.WordTrace]
  refine ⟨73589814086395128950140483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98119752115193505266853977 73589814086395128950140483)
  ·
    refine ⟨110384721129592693425210725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73589814086395128950140483 110384721129592693425210725)
    ·
      refine ⟨20697135211798630017227011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110384721129592693425210725 20697135211798630017227011)
      ·
        refine ⟨31045702817697945025840517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20697135211798630017227011 31045702817697945025840517)
        ·
          refine ⟨5821069278318364692345097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31045702817697945025840517 5821069278318364692345097)
          ·
            refine ⟨4365801958738773519258823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821069278318364692345097 4365801958738773519258823)
            ·
              refine ⟨6548702938108160278888235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365801958738773519258823 6548702938108160278888235)
              ·
                refine ⟨9823054407162240418332353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548702938108160278888235 9823054407162240418332353)
                ·
                  refine ⟨7367290805371680313749265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9823054407162240418332353 7367290805371680313749265)
                  ·
                    refine ⟨5525468104028760235311949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7367290805371680313749265 5525468104028760235311949)
                    ·
                      refine ⟨2072050539010785088241981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5525468104028760235311949 2072050539010785088241981)
                      ·
                        rfl

theorem cell23_4035304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_4035304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035304 prefixEnd_4035304 := by exact prefixLift 4035304
  have htrace : WordTrace (prefixWord ++ tailWord_4035304) baseStart_4035304 baseEnd_4035304 := by
    simpa [prefixWord, tailWord_4035304, baseEnd_4035304] using wordTrace_append hprefix tailTrace_4035304
  have hstable : (prefixWord ++ tailWord_4035304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035304).length < 2 ^ (prefixWord ++ tailWord_4035304).sum := by decide
  have hdescent : baseEnd_4035304 < baseStart_4035304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035320 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 1, 5]
def baseStart_4035320 : Nat := 118140960795 + 4035320 * 2 ^ 59
def prefixEnd_4035320 : Nat := 4983230072969 + 3 ^ 40 * 4035320 * 2
def baseEnd_4035320 : Nat := 690686251567085675213969

theorem tailTrace_4035320 : CollatzResearch.WordTrace tailWord_4035320 prefixEnd_4035320 690686251567085675213969 := by
  unfold tailWord_4035320
  simp only [CollatzResearch.WordTrace]
  refine ⟨73590105870366146316431707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98120141160488195088575609 73590105870366146316431707)
  ·
    refine ⟨110385158805549219474647561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73590105870366146316431707 110385158805549219474647561)
    ·
      refine ⟨82788869104161914605985671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110385158805549219474647561 82788869104161914605985671)
      ·
        refine ⟨124183303656242871908978507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82788869104161914605985671 124183303656242871908978507)
        ·
          refine ⟨186274955484364307863467761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124183303656242871908978507 186274955484364307863467761)
          ·
            refine ⟨139706216613273230897600821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186274955484364307863467761 139706216613273230897600821)
            ·
              refine ⟨13097457807494365396650077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139706216613273230897600821 13097457807494365396650077)
              ·
                refine ⟨4911546677810387023743779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13097457807494365396650077 4911546677810387023743779)
                ·
                  refine ⟨7367320016715580535615669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911546677810387023743779 7367320016715580535615669)
                  ·
                    refine ⟨690686251567085675213969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7367320016715580535615669 690686251567085675213969)
                    ·
                      rfl

theorem cell23_4035320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_4035320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035320 prefixEnd_4035320 := by exact prefixLift 4035320
  have htrace : WordTrace (prefixWord ++ tailWord_4035320) baseStart_4035320 baseEnd_4035320 := by
    simpa [prefixWord, tailWord_4035320, baseEnd_4035320] using wordTrace_append hprefix tailTrace_4035320
  have hstable : (prefixWord ++ tailWord_4035320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035320).length < 2 ^ (prefixWord ++ tailWord_4035320).sum := by decide
  have hdescent : baseEnd_4035320 < baseStart_4035320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035333 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 3, 6]
def baseStart_4035333 : Nat := 118140960795 + 4035333 * 2 ^ 59
def prefixEnd_4035333 : Nat := 4983230072969 + 3 ^ 40 * 4035333 * 2
def baseEnd_4035333 : Nat := 690688476649921824926449

theorem tailTrace_4035333 : CollatzResearch.WordTrace tailWord_4035333 prefixEnd_4035333 690688476649921824926449 := by
  unfold tailWord_4035333
  simp only [CollatzResearch.WordTrace]
  refine ⟨147180685889685195853086653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98120457259790130568724435 147180685889685195853086653)
  ·
    refine ⟨55192757208631948444907495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147180685889685195853086653 55192757208631948444907495)
    ·
      refine ⟨82789135812947922667361243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55192757208631948444907495 82789135812947922667361243)
      ·
        refine ⟨124183703719421884001041865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82789135812947922667361243 124183703719421884001041865)
        ·
          refine ⟨93137777789566413000781399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124183703719421884001041865 93137777789566413000781399)
          ·
            refine ⟨139706666684349619501172099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93137777789566413000781399 139706666684349619501172099)
            ·
              refine ⟨209560000026524429251758149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139706666684349619501172099 209560000026524429251758149)
              ·
                refine ⟨39292500004973330484704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209560000026524429251758149 39292500004973330484704653)
                ·
                  refine ⟨14734687501864998931764245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39292500004973330484704653 14734687501864998931764245)
                  ·
                    refine ⟨690688476649921824926449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14734687501864998931764245 690688476649921824926449)
                    ·
                      rfl

theorem cell23_4035333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 3, 6].length) (baseStart_4035333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035333 prefixEnd_4035333 := by exact prefixLift 4035333
  have htrace : WordTrace (prefixWord ++ tailWord_4035333) baseStart_4035333 baseEnd_4035333 := by
    simpa [prefixWord, tailWord_4035333, baseEnd_4035333] using wordTrace_append hprefix tailTrace_4035333
  have hstable : (prefixWord ++ tailWord_4035333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035333).length < 2 ^ (prefixWord ++ tailWord_4035333).sum := by decide
  have hdescent : baseEnd_4035333 < baseStart_4035333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035374 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4035374 : Nat := 118140960795 + 4035374 * 2 ^ 59
def prefixEnd_4035374 : Nat := 4983230072969 + 3 ^ 40 * 4035374 * 2
def baseEnd_4035374 : Nat := 2072086482656599814366659

theorem tailTrace_4035374 : CollatzResearch.WordTrace tailWord_4035374 prefixEnd_4035374 2072086482656599814366659 := by
  unfold tailWord_4035374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18397772660317082481916147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98121454188357773236886117 18397772660317082481916147)
  ·
    refine ⟨27596658990475623722874221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18397772660317082481916147 27596658990475623722874221)
    ·
      refine ⟨10348747121428358896077833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27596658990475623722874221 10348747121428358896077833)
      ·
        refine ⟨7761560341071269172058375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10348747121428358896077833 7761560341071269172058375)
        ·
          refine ⟨11642340511606903758087563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761560341071269172058375 11642340511606903758087563)
          ·
            refine ⟨17463510767410355637131345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11642340511606903758087563 17463510767410355637131345)
            ·
              refine ⟨13097633075557766727848509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17463510767410355637131345 13097633075557766727848509)
              ·
                refine ⟨4911612403334162522943191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13097633075557766727848509 4911612403334162522943191)
                ·
                  refine ⟨7367418605001243784414787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911612403334162522943191 7367418605001243784414787)
                  ·
                    refine ⟨11051127907501865676622181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367418605001243784414787 11051127907501865676622181)
                    ·
                      refine ⟨2072086482656599814366659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11051127907501865676622181 2072086482656599814366659)
                      ·
                        rfl

theorem cell23_4035374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4035374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035374 prefixEnd_4035374 := by exact prefixLift 4035374
  have htrace : WordTrace (prefixWord ++ tailWord_4035374) baseStart_4035374 baseEnd_4035374 := by
    simpa [prefixWord, tailWord_4035374, baseEnd_4035374] using wordTrace_append hprefix tailTrace_4035374
  have hstable : (prefixWord ++ tailWord_4035374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035374).length < 2 ^ (prefixWord ++ tailWord_4035374).sum := by decide
  have hdescent : baseEnd_4035374 < baseStart_4035374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035377 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4035377 : Nat := 118140960795 + 4035377 * 2 ^ 59
def prefixEnd_4035377 : Nat := 4983230072969 + 3 ^ 40 * 4035377 * 2
def baseEnd_4035377 : Nat := 2072088023098563302629145

theorem tailTrace_4035377 : CollatzResearch.WordTrace tailWord_4035377 prefixEnd_4035377 2072088023098563302629145 := by
  unfold tailWord_4035377
  simp only [CollatzResearch.WordTrace]
  refine ⟨147182290701525791367688385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98121527134350527578458923 147182290701525791367688385)
  ·
    refine ⟨110386718026144343525766289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147182290701525791367688385 110386718026144343525766289)
    ·
      refine ⟨82790038519608257644324717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110386718026144343525766289 82790038519608257644324717)
      ·
        refine ⟨31046264444853096616621769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82790038519608257644324717 31046264444853096616621769)
        ·
          refine ⟨23284698333639822462466327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31046264444853096616621769 23284698333639822462466327)
          ·
            refine ⟨34927047500459733693699491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23284698333639822462466327 34927047500459733693699491)
            ·
              refine ⟨52390571250689600540549237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34927047500459733693699491 52390571250689600540549237)
              ·
                refine ⟨4911616054752150050676491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52390571250689600540549237 4911616054752150050676491)
                ·
                  refine ⟨7367424082128225076014737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4911616054752150050676491 7367424082128225076014737)
                  ·
                    refine ⟨5525568061596168807011053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7367424082128225076014737 5525568061596168807011053)
                    ·
                      refine ⟨2072088023098563302629145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5525568061596168807011053 2072088023098563302629145)
                      ·
                        rfl

theorem cell23_4035377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4035377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035377 prefixEnd_4035377 := by exact prefixLift 4035377
  have htrace : WordTrace (prefixWord ++ tailWord_4035377) baseStart_4035377 baseEnd_4035377 := by
    simpa [prefixWord, tailWord_4035377, baseEnd_4035377] using wordTrace_append hprefix tailTrace_4035377
  have hstable : (prefixWord ++ tailWord_4035377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035377).length < 2 ^ (prefixWord ++ tailWord_4035377).sum := by decide
  have hdescent : baseEnd_4035377 < baseStart_4035377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035391 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 3, 2, 2]
def baseStart_4035391 : Nat := 118140960795 + 4035391 * 2 ^ 59
def prefixEnd_4035391 : Nat := 4983230072969 + 3 ^ 40 * 4035391 * 2
def baseEnd_4035391 : Nat := 2072095211827726247854081

theorem tailTrace_4035391 : CollatzResearch.WordTrace tailWord_4035391 prefixEnd_4035391 2072095211827726247854081 := by
  unfold tailWord_4035391
  simp only [CollatzResearch.WordTrace]
  refine ⟨147182801323475071758698027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98121867548983381172465351 147182801323475071758698027)
  ·
    refine ⟨220774201985212607638047041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147182801323475071758698027 220774201985212607638047041)
    ·
      refine ⟨165580651488909455728535281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220774201985212607638047041 165580651488909455728535281)
      ·
        refine ⟨124185488616682091796401461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165580651488909455728535281 124185488616682091796401461)
        ·
          refine ⟨11642389557813946105912637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124185488616682091796401461 11642389557813946105912637)
          ·
            refine ⟨4365896084180229789717239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11642389557813946105912637 4365896084180229789717239)
            ·
              refine ⟨6548844126270344684575859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365896084180229789717239 6548844126270344684575859)
              ·
                refine ⟨9823266189405517026863789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548844126270344684575859 9823266189405517026863789)
                ·
                  refine ⟨3683724821027068885073921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9823266189405517026863789 3683724821027068885073921)
                  ·
                    refine ⟨2762793615770301663805441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3683724821027068885073921 2762793615770301663805441)
                    ·
                      refine ⟨2072095211827726247854081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762793615770301663805441 2072095211827726247854081)
                      ·
                        rfl

theorem cell23_4035391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_4035391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035391 prefixEnd_4035391 := by exact prefixLift 4035391
  have htrace : WordTrace (prefixWord ++ tailWord_4035391) baseStart_4035391 baseEnd_4035391 := by
    simpa [prefixWord, tailWord_4035391, baseEnd_4035391] using wordTrace_append hprefix tailTrace_4035391
  have hstable : (prefixWord ++ tailWord_4035391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035391).length < 2 ^ (prefixWord ++ tailWord_4035391).sum := by decide
  have hdescent : baseEnd_4035391 < baseStart_4035391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035458 : List Nat := [3, 4, 2, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4035458 : Nat := 118140960795 + 4035458 * 2 ^ 59
def prefixEnd_4035458 : Nat := 4983230072969 + 3 ^ 40 * 4035458 * 2
def baseEnd_4035458 : Nat := 2072129615031577485716273

theorem tailTrace_4035458 : CollatzResearch.WordTrace tailWord_4035458 prefixEnd_4035458 2072129615031577485716273 := by
  unfold tailWord_4035458
  simp only [CollatzResearch.WordTrace]
  refine ⟨36796311253558085550346757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98123496676154894800924685 36796311253558085550346757)
  ·
    refine ⟨6899308360042141040690017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36796311253558085550346757 6899308360042141040690017)
    ·
      refine ⟨5174481270031605780517513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6899308360042141040690017 5174481270031605780517513)
      ·
        refine ⟨3880860952523704335388135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5174481270031605780517513 3880860952523704335388135)
        ·
          refine ⟨5821291428785556503082203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880860952523704335388135 5821291428785556503082203)
          ·
            refine ⟨8731937143178334754623305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821291428785556503082203 8731937143178334754623305)
            ·
              refine ⟨6548952857383751065967479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8731937143178334754623305 6548952857383751065967479)
              ·
                refine ⟨9823429286075626598951219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548952857383751065967479 9823429286075626598951219)
                ·
                  refine ⟨14735143929113439898426829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823429286075626598951219 14735143929113439898426829)
                  ·
                    refine ⟨5525678973417539961910061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14735143929113439898426829 5525678973417539961910061)
                    ·
                      refine ⟨2072129615031577485716273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5525678973417539961910061 2072129615031577485716273)
                      ·
                        rfl

theorem cell23_4035458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4035458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035458 prefixEnd_4035458 := by exact prefixLift 4035458
  have htrace : WordTrace (prefixWord ++ tailWord_4035458) baseStart_4035458 baseEnd_4035458 := by
    simpa [prefixWord, tailWord_4035458, baseEnd_4035458] using wordTrace_append hprefix tailTrace_4035458
  have hstable : (prefixWord ++ tailWord_4035458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035458).length < 2 ^ (prefixWord ++ tailWord_4035458).sum := by decide
  have hdescent : baseEnd_4035458 < baseStart_4035458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035464 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_4035464 : Nat := 118140960795 + 4035464 * 2 ^ 59
def prefixEnd_4035464 : Nat := 4983230072969 + 3 ^ 40 * 4035464 * 2
def baseEnd_4035464 : Nat := 2072132695915504462241245

theorem tailTrace_4035464 : CollatzResearch.WordTrace tailWord_4035464 prefixEnd_4035464 2072132695915504462241245 := by
  unfold tailWord_4035464
  simp only [CollatzResearch.WordTrace]
  refine ⟨73592731926105302613052723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98123642568140403484070297 73592731926105302613052723)
  ·
    refine ⟨110389097889157953919579085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73592731926105302613052723 110389097889157953919579085)
    ·
      refine ⟨41395911708434232719842157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110389097889157953919579085 41395911708434232719842157)
      ·
        refine ⟨15523466890662837269940809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41395911708434232719842157 15523466890662837269940809)
        ·
          refine ⟨11642600167997127952455607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15523466890662837269940809 11642600167997127952455607)
          ·
            refine ⟨17463900251995691928683411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11642600167997127952455607 17463900251995691928683411)
            ·
              refine ⟨26195850377993537893025117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17463900251995691928683411 26195850377993537893025117)
              ·
                refine ⟨9823443891747576709884419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26195850377993537893025117 9823443891747576709884419)
                ·
                  refine ⟨14735165837621365064826629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823443891747576709884419 14735165837621365064826629)
                  ·
                    refine ⟨2762843594554005949654993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14735165837621365064826629 2762843594554005949654993)
                    ·
                      refine ⟨2072132695915504462241245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762843594554005949654993 2072132695915504462241245)
                      ·
                        rfl

theorem cell23_4035464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_4035464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035464 prefixEnd_4035464 := by exact prefixLift 4035464
  have htrace : WordTrace (prefixWord ++ tailWord_4035464) baseStart_4035464 baseEnd_4035464 := by
    simpa [prefixWord, tailWord_4035464, baseEnd_4035464] using wordTrace_append hprefix tailTrace_4035464
  have hstable : (prefixWord ++ tailWord_4035464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035464).length < 2 ^ (prefixWord ++ tailWord_4035464).sum := by decide
  have hdescent : baseEnd_4035464 < baseStart_4035464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035507 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 5, 2]
def baseStart_4035507 : Nat := 118140960795 + 4035507 * 2 ^ 59
def prefixEnd_4035507 : Nat := 4983230072969 + 3 ^ 40 * 4035507 * 2
def baseEnd_4035507 : Nat := 2072154775583647794003547

theorem tailTrace_4035507 : CollatzResearch.WordTrace tailWord_4035507 prefixEnd_4035507 2072154775583647794003547 := by
  unfold tailWord_4035507
  simp only [CollatzResearch.WordTrace]
  refine ⟨147187032191054823569920775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98124688127369882379947183 147187032191054823569920775)
  ·
    refine ⟨220780548286582235354881163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147187032191054823569920775 220780548286582235354881163)
    ·
      refine ⟨331170822429873353032321745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220780548286582235354881163 331170822429873353032321745)
      ·
        refine ⟨248378116822405014774241309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331170822429873353032321745 248378116822405014774241309)
        ·
          refine ⟨93141793808401880540340491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248378116822405014774241309 93141793808401880540340491)
          ·
            refine ⟨139712690712602820810510737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93141793808401880540340491 139712690712602820810510737)
            ·
              refine ⟨104784518034452115607883053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139712690712602820810510737 104784518034452115607883053)
              ·
                refine ⟨39294194262919543352956145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104784518034452115607883053 39294194262919543352956145)
                ·
                  refine ⟨29470645697189657514717109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39294194262919543352956145 29470645697189657514717109)
                  ·
                    refine ⟨2762873034111530392004729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29470645697189657514717109 2762873034111530392004729)
                    ·
                      refine ⟨2072154775583647794003547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2762873034111530392004729 2072154775583647794003547)
                      ·
                        rfl

theorem cell23_4035507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 5, 2].length) (baseStart_4035507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035507 prefixEnd_4035507 := by exact prefixLift 4035507
  have htrace : WordTrace (prefixWord ++ tailWord_4035507) baseStart_4035507 baseEnd_4035507 := by
    simpa [prefixWord, tailWord_4035507, baseEnd_4035507] using wordTrace_append hprefix tailTrace_4035507
  have hstable : (prefixWord ++ tailWord_4035507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035507).length < 2 ^ (prefixWord ++ tailWord_4035507).sum := by decide
  have hdescent : baseEnd_4035507 < baseStart_4035507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035530 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 1, 10]
def baseStart_4035530 : Nat := 118140960795 + 4035530 * 2 ^ 59
def prefixEnd_4035530 : Nat := 4983230072969 + 3 ^ 40 * 4035530 * 2
def baseEnd_4035530 : Nat := 690722195212900401338647

theorem tailTrace_4035530 : CollatzResearch.WordTrace tailWord_4035530 prefixEnd_4035530 690722195212900401338647 := by
  unfold tailWord_4035530
  simp only [CollatzResearch.WordTrace]
  refine ⟨36796967767492874624502011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98125247379980998998672029 36796967767492874624502011)
  ·
    refine ⟨55195451651239311936753017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36796967767492874624502011 55195451651239311936753017)
    ·
      refine ⟨41396588738429483952564763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55195451651239311936753017 41396588738429483952564763)
      ·
        refine ⟨62094883107644225928847145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41396588738429483952564763 62094883107644225928847145)
        ·
          refine ⟨46571162330733169446635359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62094883107644225928847145 46571162330733169446635359)
          ·
            refine ⟨69856743496099754169953039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46571162330733169446635359 69856743496099754169953039)
            ·
              refine ⟨104785115244149631254929559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69856743496099754169953039 104785115244149631254929559)
              ·
                refine ⟨157177672866224446882394339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104785115244149631254929559 157177672866224446882394339)
                ·
                  refine ⟨235766509299336670323591509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157177672866224446882394339 235766509299336670323591509)
                  ·
                    refine ⟨690722195212900401338647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 235766509299336670323591509 690722195212900401338647)
                    ·
                      rfl

theorem cell23_4035530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_4035530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035530 prefixEnd_4035530 := by exact prefixLift 4035530
  have htrace : WordTrace (prefixWord ++ tailWord_4035530) baseStart_4035530 baseEnd_4035530 := by
    simpa [prefixWord, tailWord_4035530, baseEnd_4035530] using wordTrace_append hprefix tailTrace_4035530
  have hstable : (prefixWord ++ tailWord_4035530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035530).length < 2 ^ (prefixWord ++ tailWord_4035530).sum := by decide
  have hdescent : baseEnd_4035530 < baseStart_4035530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035537 : List Nat := [1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 4]
def baseStart_4035537 : Nat := 118140960795 + 4035537 * 2 ^ 59
def prefixEnd_4035537 : Nat := 4983230072969 + 3 ^ 40 * 4035537 * 2
def baseEnd_4035537 : Nat := 2072170180003282676628409

theorem tailTrace_4035537 : CollatzResearch.WordTrace tailWord_4035537 prefixEnd_4035537 2072170180003282676628409 := by
  unfold tailWord_4035537
  simp only [CollatzResearch.WordTrace]
  refine ⟨147188126380946138693512865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98125417587297425795675243 147188126380946138693512865)
  ·
    refine ⟨110391094785709604020134649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147188126380946138693512865 110391094785709604020134649)
    ·
      refine ⟨82793321089282203015100987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110391094785709604020134649 82793321089282203015100987)
      ·
        refine ⟨124189981633923304522651481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82793321089282203015100987 124189981633923304522651481)
        ·
          refine ⟨93142486225442478391988611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124189981633923304522651481 93142486225442478391988611)
          ·
            refine ⟨139713729338163717587982917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93142486225442478391988611 139713729338163717587982917)
            ·
              refine ⟨26196324250905697047746797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139713729338163717587982917 26196324250905697047746797)
              ·
                refine ⟨9823621594089636392905049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26196324250905697047746797 9823621594089636392905049)
                ·
                  refine ⟨7367716195567227294678787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9823621594089636392905049 7367716195567227294678787)
                  ·
                    refine ⟨11051574293350840942018181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367716195567227294678787 11051574293350840942018181)
                    ·
                      refine ⟨2072170180003282676628409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11051574293350840942018181 2072170180003282676628409)
                      ·
                        rfl

theorem cell23_4035537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_4035537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035537 prefixEnd_4035537 := by exact prefixLift 4035537
  have htrace : WordTrace (prefixWord ++ tailWord_4035537) baseStart_4035537 baseEnd_4035537 := by
    simpa [prefixWord, tailWord_4035537, baseEnd_4035537] using wordTrace_append hprefix tailTrace_4035537
  have hstable : (prefixWord ++ tailWord_4035537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035537).length < 2 ^ (prefixWord ++ tailWord_4035537).sum := by decide
  have hdescent : baseEnd_4035537 < baseStart_4035537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035577 : List Nat := [1, 2, 1, 3, 1, 3, 3, 3, 6]
def baseStart_4035577 : Nat := 118140960795 + 4035577 * 2 ^ 59
def prefixEnd_4035577 : Nat := 4983230072969 + 3 ^ 40 * 4035577 * 2
def baseEnd_4035577 : Nat := 230243413247718057792025

theorem tailTrace_4035577 : CollatzResearch.WordTrace tailWord_4035577 prefixEnd_4035577 230243413247718057792025 := by
  unfold tailWord_4035577
  simp only [CollatzResearch.WordTrace]
  refine ⟨147189585300801225524968985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98126390200534150349979323 147189585300801225524968985)
  ·
    refine ⟨110392188975600919143726739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147189585300801225524968985 110392188975600919143726739)
    ·
      refine ⟨165588283463401378715590109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110392188975600919143726739 165588283463401378715590109)
      ·
        refine ⟨62095606298775517018346291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165588283463401378715590109 62095606298775517018346291)
        ·
          refine ⟨93143409448163275527519437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62095606298775517018346291 93143409448163275527519437)
          ·
            refine ⟨34928778543061228322819789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93143409448163275527519437 34928778543061228322819789)
            ·
              refine ⟨13098291953647960621057421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34928778543061228322819789 13098291953647960621057421)
              ·
                refine ⟨4911859482617985232896533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13098291953647960621057421 4911859482617985232896533)
                ·
                  refine ⟨230243413247718057792025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4911859482617985232896533 230243413247718057792025)
                  ·
                    rfl

theorem cell23_4035577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 6].length) (baseStart_4035577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035577 prefixEnd_4035577 := by exact prefixLift 4035577
  have htrace : WordTrace (prefixWord ++ tailWord_4035577) baseStart_4035577 baseEnd_4035577 := by
    simpa [prefixWord, tailWord_4035577, baseEnd_4035577] using wordTrace_append hprefix tailTrace_4035577
  have hstable : (prefixWord ++ tailWord_4035577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035577).length < 2 ^ (prefixWord ++ tailWord_4035577).sum := by decide
  have hdescent : baseEnd_4035577 < baseStart_4035577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035627 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4]
def baseStart_4035627 : Nat := 118140960795 + 4035627 * 2 ^ 59
def prefixEnd_4035627 : Nat := 4983230072969 + 3 ^ 40 * 4035627 * 2
def baseEnd_4035627 : Nat := 2072216393262187324502995

theorem tailTrace_4035627 : CollatzResearch.WordTrace tailWord_4035627 prefixEnd_4035627 2072216393262187324502995 := by
  unfold tailWord_4035627
  simp only [CollatzResearch.WordTrace]
  refine ⟨147191408950620084064289135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98127605967080056042859423 147191408950620084064289135)
  ·
    refine ⟨220787113425930126096433703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147191408950620084064289135 220787113425930126096433703)
    ·
      refine ⟨331180670138895189144650555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220787113425930126096433703 331180670138895189144650555)
      ·
        refine ⟨496771005208342783716975833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331180670138895189144650555 496771005208342783716975833)
        ·
          refine ⟨372578253906257087787731875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496771005208342783716975833 372578253906257087787731875)
          ·
            refine ⟨558867380859385631681597813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372578253906257087787731875 558867380859385631681597813)
            ·
              refine ⟨52393816955567402970149795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 558867380859385631681597813 52393816955567402970149795)
              ·
                refine ⟨78590725433351104455224693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52393816955567402970149795 78590725433351104455224693)
                ·
                  refine ⟨7367880509376666042677315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78590725433351104455224693 7367880509376666042677315)
                  ·
                    refine ⟨11051820764064999064015973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367880509376666042677315 11051820764064999064015973)
                    ·
                      refine ⟨2072216393262187324502995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11051820764064999064015973 2072216393262187324502995)
                      ·
                        rfl

theorem cell23_4035627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4].length) (baseStart_4035627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035627 prefixEnd_4035627 := by exact prefixLift 4035627
  have htrace : WordTrace (prefixWord ++ tailWord_4035627) baseStart_4035627 baseEnd_4035627 := by
    simpa [prefixWord, tailWord_4035627, baseEnd_4035627] using wordTrace_append hprefix tailTrace_4035627
  have hstable : (prefixWord ++ tailWord_4035627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035627).length < 2 ^ (prefixWord ++ tailWord_4035627).sum := by decide
  have hdescent : baseEnd_4035627 < baseStart_4035627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035638 : List Nat := [5, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4035638 : Nat := 118140960795 + 4035638 * 2 ^ 59
def prefixEnd_4035638 : Nat := 4983230072969 + 3 ^ 40 * 4035638 * 2
def baseEnd_4035638 : Nat := 2072222041549386781465445

theorem tailTrace_4035638 : CollatzResearch.WordTrace tailWord_4035638 prefixEnd_4035638 2072222041549386781465445 := by
  unfold tailWord_4035638
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199488134598764558933723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98127873435720155295293045 9199488134598764558933723)
  ·
    refine ⟨13799232201898146838400585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9199488134598764558933723 13799232201898146838400585)
    ·
      refine ⟨10349424151423610128800439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13799232201898146838400585 10349424151423610128800439)
      ·
        refine ⟨15524136227135415193200659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10349424151423610128800439 15524136227135415193200659)
        ·
          refine ⟨23286204340703122789800989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15524136227135415193200659 23286204340703122789800989)
          ·
            refine ⟨8732326627763671046175371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23286204340703122789800989 8732326627763671046175371)
            ·
              refine ⟨13098489941645506569263057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732326627763671046175371 13098489941645506569263057)
              ·
                refine ⟨9823867456234129926947293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13098489941645506569263057 9823867456234129926947293)
                ·
                  refine ⟨3683950296087798722605235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9823867456234129926947293 3683950296087798722605235)
                  ·
                    refine ⟨5525925444131698083907853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3683950296087798722605235 5525925444131698083907853)
                    ·
                      refine ⟨2072222041549386781465445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5525925444131698083907853 2072222041549386781465445)
                      ·
                        rfl

theorem cell23_4035638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4035638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035638 prefixEnd_4035638 := by exact prefixLift 4035638
  have htrace : WordTrace (prefixWord ++ tailWord_4035638) baseStart_4035638 baseEnd_4035638 := by
    simpa [prefixWord, tailWord_4035638, baseEnd_4035638] using wordTrace_append hprefix tailTrace_4035638
  have hstable : (prefixWord ++ tailWord_4035638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035638).length < 2 ^ (prefixWord ++ tailWord_4035638).sum := by decide
  have hdescent : baseEnd_4035638 < baseStart_4035638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035644 : List Nat := [2, 2, 2, 2, 2, 2, 2, 1, 3, 1, 4]
def baseStart_4035644 : Nat := 118140960795 + 4035644 * 2 ^ 59
def prefixEnd_4035644 : Nat := 4983230072969 + 3 ^ 40 * 4035644 * 2
def baseEnd_4035644 : Nat := 2072225122433313757990417

theorem tailTrace_4035644 : CollatzResearch.WordTrace tailWord_4035644 prefixEnd_4035644 2072225122433313757990417 := by
  unfold tailWord_4035644
  simp only [CollatzResearch.WordTrace]
  refine ⟨73596014495779247983828993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98128019327705663978438657 73596014495779247983828993)
  ·
    refine ⟨55197010871834435987871745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73596014495779247983828993 55197010871834435987871745)
    ·
      refine ⟨41397758153875826990903809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55197010871834435987871745 41397758153875826990903809)
      ·
        refine ⟨31048318615406870243177857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41397758153875826990903809 31048318615406870243177857)
        ·
          refine ⟨23286238961555152682383393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31048318615406870243177857 23286238961555152682383393)
          ·
            refine ⟨17464679221166364511787545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23286238961555152682383393 17464679221166364511787545)
            ·
              refine ⟨13098509415874773383840659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17464679221166364511787545 13098509415874773383840659)
              ·
                refine ⟨19647764123812160075760989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13098509415874773383840659 19647764123812160075760989)
                ·
                  refine ⟨7367911546429560028410371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19647764123812160075760989 7367911546429560028410371)
                  ·
                    refine ⟨11051867319644340042615557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7367911546429560028410371 11051867319644340042615557)
                    ·
                      refine ⟨2072225122433313757990417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11051867319644340042615557 2072225122433313757990417)
                      ·
                        rfl

theorem cell23_4035644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_4035644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035644 prefixEnd_4035644 := by exact prefixLift 4035644
  have htrace : WordTrace (prefixWord ++ tailWord_4035644) baseStart_4035644 baseEnd_4035644 := by
    simpa [prefixWord, tailWord_4035644, baseEnd_4035644] using wordTrace_append hprefix tailTrace_4035644
  have hstable : (prefixWord ++ tailWord_4035644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035644).length < 2 ^ (prefixWord ++ tailWord_4035644).sum := by decide
  have hdescent : baseEnd_4035644 < baseStart_4035644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035657 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 4]
def baseStart_4035657 : Nat := 118140960795 + 4035657 * 2 ^ 59
def prefixEnd_4035657 : Nat := 4983230072969 + 3 ^ 40 * 4035657 * 2
def baseEnd_4035657 : Nat := 2072231797681822207127857

theorem tailTrace_4035657 : CollatzResearch.WordTrace tailWord_4035657 prefixEnd_4035657 2072231797681822207127857 := by
  unfold tailWord_4035657
  simp only [CollatzResearch.WordTrace]
  refine ⟨147192503140511399187881225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98128335427007599458587483 147192503140511399187881225)
  ·
    refine ⟨110394377355383549390910919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147192503140511399187881225 110394377355383549390910919)
    ·
      refine ⟨165591566033075324086366379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110394377355383549390910919 165591566033075324086366379)
      ·
        refine ⟨248387349049612986129549569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165591566033075324086366379 248387349049612986129549569)
        ·
          refine ⟨186290511787209739597162177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248387349049612986129549569 186290511787209739597162177)
          ·
            refine ⟨139717883840407304697871633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186290511787209739597162177 139717883840407304697871633)
            ·
              refine ⟨104788412880305478523403725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139717883840407304697871633 104788412880305478523403725)
              ·
                refine ⟨39295654830114554446276397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104788412880305478523403725 39295654830114554446276397)
                ·
                  refine ⟨14735870561292957917353649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39295654830114554446276397 14735870561292957917353649)
                  ·
                    refine ⟨11051902920969718438015237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14735870561292957917353649 11051902920969718438015237)
                    ·
                      refine ⟨2072231797681822207127857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11051902920969718438015237 2072231797681822207127857)
                      ·
                        rfl

theorem cell23_4035657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 2, 4].length) (baseStart_4035657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035657 prefixEnd_4035657 := by exact prefixLift 4035657
  have htrace : WordTrace (prefixWord ++ tailWord_4035657) baseStart_4035657 baseEnd_4035657 := by
    simpa [prefixWord, tailWord_4035657, baseEnd_4035657] using wordTrace_append hprefix tailTrace_4035657
  have hstable : (prefixWord ++ tailWord_4035657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035657).length < 2 ^ (prefixWord ++ tailWord_4035657).sum := by decide
  have hdescent : baseEnd_4035657 < baseStart_4035657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035688 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 1, 6]
def baseStart_4035688 : Nat := 118140960795 + 4035688 * 2 ^ 59
def prefixEnd_4035688 : Nat := 4983230072969 + 3 ^ 40 * 4035688 * 2
def baseEnd_4035688 : Nat := 690749238527370528613405

theorem tailTrace_4035688 : CollatzResearch.WordTrace tailWord_4035688 prefixEnd_4035688 690749238527370528613405 := by
  unfold tailWord_4035688
  simp only [CollatzResearch.WordTrace]
  refine ⟨73596816901699545741129859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98129089202266060988173145 73596816901699545741129859)
  ·
    refine ⟨110395225352549318611694789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73596816901699545741129859 110395225352549318611694789)
    ·
      refine ⟨20699104753602997239692773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110395225352549318611694789 20699104753602997239692773)
      ·
        refine ⟨3881082141300561982442395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20699104753602997239692773 3881082141300561982442395)
        ·
          refine ⟨5821623211950842973663593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881082141300561982442395 5821623211950842973663593)
          ·
            refine ⟨4366217408963132230247695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5821623211950842973663593 4366217408963132230247695)
            ·
              refine ⟨6549326113444698345371543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366217408963132230247695 6549326113444698345371543)
              ·
                refine ⟨9823989170167047518057315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549326113444698345371543 9823989170167047518057315)
                ·
                  refine ⟨14735983755250571277085973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9823989170167047518057315 14735983755250571277085973)
                  ·
                    refine ⟨690749238527370528613405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14735983755250571277085973 690749238527370528613405)
                    ·
                      rfl

theorem cell23_4035688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_4035688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035688 prefixEnd_4035688 := by exact prefixLift 4035688
  have htrace : WordTrace (prefixWord ++ tailWord_4035688) baseStart_4035688 baseEnd_4035688 := by
    simpa [prefixWord, tailWord_4035688, baseEnd_4035688] using wordTrace_append hprefix tailTrace_4035688
  have hstable : (prefixWord ++ tailWord_4035688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035688).length < 2 ^ (prefixWord ++ tailWord_4035688).sum := by decide
  have hdescent : baseEnd_4035688 < baseStart_4035688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035701 : List Nat := [1, 3, 4, 3, 1, 1, 1, 9]
def baseStart_4035701 : Nat := 118140960795 + 4035701 * 2 ^ 59
def prefixEnd_4035701 : Nat := 4983230072969 + 3 ^ 40 * 4035701 * 2
def baseEnd_4035701 : Nat := 76750162623356297591765

theorem tailTrace_4035701 : CollatzResearch.WordTrace tailWord_4035701 prefixEnd_4035701 76750162623356297591765 := by
  unfold tailWord_4035701
  simp only [CollatzResearch.WordTrace]
  refine ⟨147194107952351994702482957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98129405301567996468321971 147194107952351994702482957)
  ·
    refine ⟨55197790482131998013431109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147194107952351994702482957 55197790482131998013431109)
    ·
      refine ⟨10349585715399749627518333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55197790482131998013431109 10349585715399749627518333)
      ·
        refine ⟨3881094643274906110319375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10349585715399749627518333 3881094643274906110319375)
        ·
          refine ⟨5821641964912359165479063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3881094643274906110319375 5821641964912359165479063)
          ·
            refine ⟨8732462947368538748218595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5821641964912359165479063 8732462947368538748218595)
            ·
              refine ⟨13098694421052808122327893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732462947368538748218595 13098694421052808122327893)
              ·
                refine ⟨76750162623356297591765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13098694421052808122327893 76750162623356297591765)
                ·
                  rfl

theorem cell23_4035701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 9].length) (baseStart_4035701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035701 prefixEnd_4035701 := by exact prefixLift 4035701
  have htrace : WordTrace (prefixWord ++ tailWord_4035701) baseStart_4035701 baseEnd_4035701 := by
    simpa [prefixWord, tailWord_4035701, baseEnd_4035701] using wordTrace_append hprefix tailTrace_4035701
  have hstable : (prefixWord ++ tailWord_4035701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035701).length < 2 ^ (prefixWord ++ tailWord_4035701).sum := by decide
  have hdescent : baseEnd_4035701 < baseStart_4035701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035747 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_4035747 : Nat := 118140960795 + 4035747 * 2 ^ 59
def prefixEnd_4035747 : Nat := 4983230072969 + 3 ^ 40 * 4035747 * 2
def baseEnd_4035747 : Nat := 2072278010940726855002443

theorem tailTrace_4035747 : CollatzResearch.WordTrace tailWord_4035747 prefixEnd_4035747 2072278010940726855002443 := by
  unfold tailWord_4035747
  simp only [CollatzResearch.WordTrace]
  refine ⟨147195785710185344558657495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98130523806790229705771663 147195785710185344558657495)
  ·
    refine ⟨220793678565278016837986243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147195785710185344558657495 220793678565278016837986243)
    ·
      refine ⟨331190517847917025256979365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220793678565278016837986243 331190517847917025256979365)
      ·
        refine ⟨62098222096484442235683631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331190517847917025256979365 62098222096484442235683631)
        ·
          refine ⟨93147333144726663353525447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62098222096484442235683631 93147333144726663353525447)
          ·
            refine ⟨139720999717089995030288171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93147333144726663353525447 139720999717089995030288171)
            ·
              refine ⟨209581499575634992545432257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139720999717089995030288171 209581499575634992545432257)
              ·
                refine ⟨157186124681726244409074193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209581499575634992545432257 157186124681726244409074193)
                ·
                  refine ⟨117889593511294683306805645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157186124681726244409074193 117889593511294683306805645)
                  ·
                    refine ⟨44208597566735506240052117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117889593511294683306805645 44208597566735506240052117)
                    ·
                      refine ⟨2072278010940726855002443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44208597566735506240052117 2072278010940726855002443)
                      ·
                        rfl

theorem cell23_4035747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_4035747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035747 prefixEnd_4035747 := by exact prefixLift 4035747
  have htrace : WordTrace (prefixWord ++ tailWord_4035747) baseStart_4035747 baseEnd_4035747 := by
    simpa [prefixWord, tailWord_4035747, baseEnd_4035747] using wordTrace_append hprefix tailTrace_4035747
  have hstable : (prefixWord ++ tailWord_4035747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035747).length < 2 ^ (prefixWord ++ tailWord_4035747).sum := by decide
  have hdescent : baseEnd_4035747 < baseStart_4035747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035821 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4035821 : Nat := 118140960795 + 4035821 * 2 ^ 59
def prefixEnd_4035821 : Nat := 4983230072969 + 3 ^ 40 * 4035821 * 2
def baseEnd_4035821 : Nat := 690772002836386521825701

theorem tailTrace_4035821 : CollatzResearch.WordTrace tailWord_4035821 prefixEnd_4035821 690772002836386521825701 := by
  unfold tailWord_4035821
  simp only [CollatzResearch.WordTrace]
  refine ⟨147198484711917255196851317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98132323141278170131234211 147198484711917255196851317)
  ·
    refine ⟨13799857941742242674704811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147198484711917255196851317 13799857941742242674704811)
    ·
      refine ⟨20699786912613364012057217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799857941742242674704811 20699786912613364012057217)
      ·
        refine ⟨15524840184460023009042913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20699786912613364012057217 15524840184460023009042913)
        ·
          refine ⟨11643630138345017256782185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15524840184460023009042913 11643630138345017256782185)
          ·
            refine ⟨8732722603758762942586639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11643630138345017256782185 8732722603758762942586639)
            ·
              refine ⟨13099083905638144413879959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8732722603758762942586639 13099083905638144413879959)
              ·
                refine ⟨19648625858457216620819939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13099083905638144413879959 19648625858457216620819939)
                ·
                  refine ⟨29472938787685824931229909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19648625858457216620819939 29472938787685824931229909)
                  ·
                    refine ⟨690772002836386521825701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29472938787685824931229909 690772002836386521825701)
                    ·
                      rfl

theorem cell23_4035821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4035821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035821 prefixEnd_4035821 := by exact prefixLift 4035821
  have htrace : WordTrace (prefixWord ++ tailWord_4035821) baseStart_4035821 baseEnd_4035821 := by
    simpa [prefixWord, tailWord_4035821, baseEnd_4035821] using wordTrace_append hprefix tailTrace_4035821
  have hstable : (prefixWord ++ tailWord_4035821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035821).length < 2 ^ (prefixWord ++ tailWord_4035821).sum := by decide
  have hdescent : baseEnd_4035821 < baseStart_4035821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035851 : List Nat := [1, 1, 1, 1, 5, 3, 1, 3, 3, 4]
def baseStart_4035851 : Nat := 118140960795 + 4035851 * 2 ^ 59
def prefixEnd_4035851 : Nat := 4983230072969 + 3 ^ 40 * 4035851 * 2
def baseEnd_4035851 : Nat := 690777137642931482700655

theorem tailTrace_4035851 : CollatzResearch.WordTrace tailWord_4035851 prefixEnd_4035851 690777137642931482700655 := by
  unfold tailWord_4035851
  simp only [CollatzResearch.WordTrace]
  refine ⟨147199578901808570320443407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98133052601205713546962271 147199578901808570320443407)
  ·
    refine ⟨220799368352712855480665111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147199578901808570320443407 220799368352712855480665111)
    ·
      refine ⟨331199052529069283220997667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220799368352712855480665111 331199052529069283220997667)
      ·
        refine ⟨496798578793603924831496501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331199052529069283220997667 496798578793603924831496501)
        ·
          refine ⟨46574866761900367952952797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 496798578793603924831496501 46574866761900367952952797)
          ·
            refine ⟨17465575035712637982357299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46574866761900367952952797 17465575035712637982357299)
            ·
              refine ⟨26198362553568956973535949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17465575035712637982357299 26198362553568956973535949)
              ·
                refine ⟨9824385957588358865075981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26198362553568956973535949 9824385957588358865075981)
                ·
                  refine ⟨3684144734095634574403493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9824385957588358865075981 3684144734095634574403493)
                  ·
                    refine ⟨690777137642931482700655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684144734095634574403493 690777137642931482700655)
                    ·
                      rfl

theorem cell23_4035851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 3, 4].length) (baseStart_4035851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035851 prefixEnd_4035851 := by exact prefixLift 4035851
  have htrace : WordTrace (prefixWord ++ tailWord_4035851) baseStart_4035851 baseEnd_4035851 := by
    simpa [prefixWord, tailWord_4035851, baseEnd_4035851] using wordTrace_append hprefix tailTrace_4035851
  have hstable : (prefixWord ++ tailWord_4035851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035851).length < 2 ^ (prefixWord ++ tailWord_4035851).sum := by decide
  have hdescent : baseEnd_4035851 < baseStart_4035851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035902 : List Nat := [4, 2, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_4035902 : Nat := 118140960795 + 4035902 * 2 ^ 59
def prefixEnd_4035902 : Nat := 4983230072969 + 3 ^ 40 * 4035902 * 2
def baseEnd_4035902 : Nat := 690785866814057916188077

theorem tailTrace_4035902 : CollatzResearch.WordTrace tailWord_4035902 prefixEnd_4035902 690785866814057916188077 := by
  unfold tailWord_4035902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400179878077975753818745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98134292683082537353699973 18400179878077975753818745)
  ·
    refine ⟨13800134908558481815364059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18400179878077975753818745 13800134908558481815364059)
    ·
      refine ⟨20700202362837722723046089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13800134908558481815364059 20700202362837722723046089)
      ·
        refine ⟨15525151772128292042284567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20700202362837722723046089 15525151772128292042284567)
        ·
          refine ⟨23287727658192438063426851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525151772128292042284567 23287727658192438063426851)
          ·
            refine ⟨34931591487288657095140277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23287727658192438063426851 34931591487288657095140277)
            ·
              refine ⟨3274836701933311602669401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34931591487288657095140277 3274836701933311602669401)
              ·
                refine ⟨2456127526449983702002051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274836701933311602669401 2456127526449983702002051)
                ·
                  refine ⟨3684191289674975553003077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456127526449983702002051 3684191289674975553003077)
                  ·
                    refine ⟨690785866814057916188077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684191289674975553003077 690785866814057916188077)
                    ·
                      rfl

theorem cell23_4035902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_4035902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035902 prefixEnd_4035902 := by exact prefixLift 4035902
  have htrace : WordTrace (prefixWord ++ tailWord_4035902) baseStart_4035902 baseEnd_4035902 := by
    simpa [prefixWord, tailWord_4035902, baseEnd_4035902] using wordTrace_append hprefix tailTrace_4035902
  have hstable : (prefixWord ++ tailWord_4035902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035902).length < 2 ^ (prefixWord ++ tailWord_4035902).sum := by decide
  have hdescent : baseEnd_4035902 < baseStart_4035902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035918 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2]
def baseStart_4035918 : Nat := 118140960795 + 4035918 * 2 ^ 59
def prefixEnd_4035918 : Nat := 4983230072969 + 3 ^ 40 * 4035918 * 2
def baseEnd_4035918 : Nat := 2072365816132645685964157

theorem tailTrace_4035918 : CollatzResearch.WordTrace tailWord_4035918 prefixEnd_4035918 2072365816132645685964157 := by
  unfold tailWord_4035918
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400252824070730095391551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98134681728377227175421605 18400252824070730095391551)
  ·
    refine ⟨27600379236106095143087327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18400252824070730095391551 27600379236106095143087327)
    ·
      refine ⟨41400568854159142714630991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27600379236106095143087327 41400568854159142714630991)
      ·
        refine ⟨62100853281238714071946487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41400568854159142714630991 62100853281238714071946487)
        ·
          refine ⟨93151279921858071107919731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62100853281238714071946487 93151279921858071107919731)
          ·
            refine ⟨139726919882787106661879597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93151279921858071107919731 139726919882787106661879597)
            ·
              refine ⟨52397594956045164998204849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139726919882787106661879597 52397594956045164998204849)
              ·
                refine ⟨39298196217033873748653637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52397594956045164998204849 39298196217033873748653637)
                ·
                  refine ⟨7368411790693851327872557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39298196217033873748653637 7368411790693851327872557)
                  ·
                    refine ⟨2763154421510194247952209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7368411790693851327872557 2763154421510194247952209)
                    ·
                      refine ⟨2072365816132645685964157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763154421510194247952209 2072365816132645685964157)
                      ·
                        rfl

theorem cell23_4035918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_4035918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035918 prefixEnd_4035918 := by exact prefixLift 4035918
  have htrace : WordTrace (prefixWord ++ tailWord_4035918) baseStart_4035918 baseEnd_4035918 := by
    simpa [prefixWord, tailWord_4035918, baseEnd_4035918] using wordTrace_append hprefix tailTrace_4035918
  have hstable : (prefixWord ++ tailWord_4035918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035918).length < 2 ^ (prefixWord ++ tailWord_4035918).sum := by decide
  have hdescent : baseEnd_4035918 < baseStart_4035918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035941 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 1, 6]
def baseStart_4035941 : Nat := 118140960795 + 4035941 * 2 ^ 59
def prefixEnd_4035941 : Nat := 4983230072969 + 3 ^ 40 * 4035941 * 2
def baseEnd_4035941 : Nat := 690792542062566365325517

theorem tailTrace_4035941 : CollatzResearch.WordTrace tailWord_4035941 prefixEnd_4035941 690792542062566365325517 := by
  unfold tailWord_4035941
  simp only [CollatzResearch.WordTrace]
  refine ⟨147202861471482515691219677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98135240980988343794146451 147202861471482515691219677)
  ·
    refine ⟨55201073051805943384207379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147202861471482515691219677 55201073051805943384207379)
    ·
      refine ⟨82801609577708915076311069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55201073051805943384207379 82801609577708915076311069)
      ·
        refine ⟨31050603591640843153616651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82801609577708915076311069 31050603591640843153616651)
        ·
          refine ⟨46575905387461264730424977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31050603591640843153616651 46575905387461264730424977)
          ·
            refine ⟨34931929040595948547818733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46575905387461264730424977 34931929040595948547818733)
            ·
              refine ⟨13099473390223480705432025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34931929040595948547818733 13099473390223480705432025)
              ·
                refine ⟨9824605042667610529074019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13099473390223480705432025 9824605042667610529074019)
                ·
                  refine ⟨14736907564001415793611029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9824605042667610529074019 14736907564001415793611029)
                  ·
                    refine ⟨690792542062566365325517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14736907564001415793611029 690792542062566365325517)
                    ·
                      rfl

theorem cell23_4035941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 1, 6].length) (baseStart_4035941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035941 prefixEnd_4035941 := by exact prefixLift 4035941
  have htrace : WordTrace (prefixWord ++ tailWord_4035941) baseStart_4035941 baseEnd_4035941 := by
    simpa [prefixWord, tailWord_4035941, baseEnd_4035941] using wordTrace_append hprefix tailTrace_4035941
  have hstable : (prefixWord ++ tailWord_4035941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035941).length < 2 ^ (prefixWord ++ tailWord_4035941).sum := by decide
  have hdescent : baseEnd_4035941 < baseStart_4035941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035965 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_4035965 : Nat := 118140960795 + 4035965 * 2 ^ 59
def prefixEnd_4035965 : Nat := 4983230072969 + 3 ^ 40 * 4035965 * 2
def baseEnd_4035965 : Nat := 2072389949723407002076441

theorem tailTrace_4035965 : CollatzResearch.WordTrace tailWord_4035965 prefixEnd_4035965 2072389949723407002076441 := by
  unfold tailWord_4035965
  simp only [CollatzResearch.WordTrace]
  refine ⟨147203736823395567790093349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98135824548930378526728899 147203736823395567790093349)
  ·
    refine ⟨27600700654386668960642503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147203736823395567790093349 27600700654386668960642503)
    ·
      refine ⟨41401050981580003440963755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27600700654386668960642503 41401050981580003440963755)
      ·
        refine ⟨62101576472370005161445633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41401050981580003440963755 62101576472370005161445633)
        ·
          refine ⟨46576182354277503871084225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62101576472370005161445633 46576182354277503871084225)
          ·
            refine ⟨34932136765708127903313169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46576182354277503871084225 34932136765708127903313169)
            ·
              refine ⟨26199102574281095927484877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34932136765708127903313169 26199102574281095927484877)
              ·
                refine ⟨9824663465355410972806829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26199102574281095927484877 9824663465355410972806829)
                ·
                  refine ⟨3684248799508279114802561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9824663465355410972806829 3684248799508279114802561)
                  ·
                    refine ⟨2763186599631209336101921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684248799508279114802561 2763186599631209336101921)
                    ·
                      refine ⟨2072389949723407002076441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763186599631209336101921 2072389949723407002076441)
                      ·
                        rfl

theorem cell23_4035965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_4035965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035965 prefixEnd_4035965 := by exact prefixLift 4035965
  have htrace : WordTrace (prefixWord ++ tailWord_4035965) baseStart_4035965 baseEnd_4035965 := by
    simpa [prefixWord, tailWord_4035965, baseEnd_4035965] using wordTrace_append hprefix tailTrace_4035965
  have hstable : (prefixWord ++ tailWord_4035965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035965).length < 2 ^ (prefixWord ++ tailWord_4035965).sum := by decide
  have hdescent : baseEnd_4035965 < baseStart_4035965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035971 : List Nat := [1, 1, 1, 3, 5, 1, 3, 8]
def baseStart_4035971 : Nat := 118140960795 + 4035971 * 2 ^ 59
def prefixEnd_4035971 : Nat := 4983230072969 + 3 ^ 40 * 4035971 * 2
def baseEnd_4035971 : Nat := 76755297429901258466719

theorem tailTrace_4035971 : CollatzResearch.WordTrace tailWord_4035971 prefixEnd_4035971 76755297429901258466719 := by
  unfold tailWord_4035971
  simp only [CollatzResearch.WordTrace]
  refine ⟨147203955661373830814811767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98135970440915887209874511 147203955661373830814811767)
  ·
    refine ⟨220805933492060746222217651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147203955661373830814811767 220805933492060746222217651)
    ·
      refine ⟨331208900238091119333326477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220805933492060746222217651 331208900238091119333326477)
      ·
        refine ⟨124203337589284169749997429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331208900238091119333326477 124203337589284169749997429)
        ·
          refine ⟨11644062898995390914062259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124203337589284169749997429 11644062898995390914062259)
          ·
            refine ⟨17466094348493086371093389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644062898995390914062259 17466094348493086371093389)
            ·
              refine ⟨6549785380684907389160021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17466094348493086371093389 6549785380684907389160021)
              ·
                refine ⟨76755297429901258466719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6549785380684907389160021 76755297429901258466719)
                ·
                  rfl

theorem cell23_4035971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 8].length) (baseStart_4035971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035971 prefixEnd_4035971 := by exact prefixLift 4035971
  have htrace : WordTrace (prefixWord ++ tailWord_4035971) baseStart_4035971 baseEnd_4035971 := by
    simpa [prefixWord, tailWord_4035971, baseEnd_4035971] using wordTrace_append hprefix tailTrace_4035971
  have hstable : (prefixWord ++ tailWord_4035971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035971).length < 2 ^ (prefixWord ++ tailWord_4035971).sum := by decide
  have hdescent : baseEnd_4035971 < baseStart_4035971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035986 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4035986 : Nat := 118140960795 + 4035986 * 2 ^ 59
def prefixEnd_4035986 : Nat := 4983230072969 + 3 ^ 40 * 4035986 * 2
def baseEnd_4035986 : Nat := 2072400732817151419913845

theorem tailTrace_4035986 : CollatzResearch.WordTrace tailWord_4035986 prefixEnd_4035986 2072400732817151419913845 := by
  unfold tailWord_4035986
  simp only [CollatzResearch.WordTrace]
  refine ⟨36801125689079872094151953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98136335170879658917738541 36801125689079872094151953)
  ·
    refine ⟨27600844266809904070613965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36801125689079872094151953 27600844266809904070613965)
    ·
      refine ⟨10350316600053714026480237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27600844266809904070613965 10350316600053714026480237)
      ·
        refine ⟨3881368725020142759930089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10350316600053714026480237 3881368725020142759930089)
        ·
          refine ⟨2911026543765107069947567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881368725020142759930089 2911026543765107069947567)
          ·
            refine ⟨4366539815647660604921351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911026543765107069947567 4366539815647660604921351)
            ·
              refine ⟨6549809723471490907382027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366539815647660604921351 6549809723471490907382027)
              ·
                refine ⟨9824714585207236361073041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549809723471490907382027 9824714585207236361073041)
                ·
                  refine ⟨7368535938905427270804781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9824714585207236361073041 7368535938905427270804781)
                  ·
                    refine ⟨2763200977089535226551793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7368535938905427270804781 2763200977089535226551793)
                    ·
                      refine ⟨2072400732817151419913845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763200977089535226551793 2072400732817151419913845)
                      ·
                        rfl

theorem cell23_4035986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4035986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035986 prefixEnd_4035986 := by exact prefixLift 4035986
  have htrace : WordTrace (prefixWord ++ tailWord_4035986) baseStart_4035986 baseEnd_4035986 := by
    simpa [prefixWord, tailWord_4035986, baseEnd_4035986] using wordTrace_append hprefix tailTrace_4035986
  have hstable : (prefixWord ++ tailWord_4035986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035986).length < 2 ^ (prefixWord ++ tailWord_4035986).sum := by decide
  have hdescent : baseEnd_4035986 < baseStart_4035986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4035999 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 1, 2, 2]
def baseStart_4035999 : Nat := 118140960795 + 4035999 * 2 ^ 59
def prefixEnd_4035999 : Nat := 4983230072969 + 3 ^ 40 * 4035999 * 2
def baseEnd_4035999 : Nat := 2072407408065659869051285

theorem tailTrace_4035999 : CollatzResearch.WordTrace tailWord_4035999 prefixEnd_4035999 2072407408065659869051285 := by
  unfold tailWord_4035999
  simp only [CollatzResearch.WordTrace]
  refine ⟨147204976905272391596831051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98136651270181594397887367 147204976905272391596831051)
  ·
    refine ⟨220807465357908587395246577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147204976905272391596831051 220807465357908587395246577)
    ·
      refine ⟨165605599018431440546434933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220807465357908587395246577 165605599018431440546434933)
      ·
        refine ⟨15525524907977947551228275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165605599018431440546434933 15525524907977947551228275)
        ·
          refine ⟨23288287361966921326842413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525524907977947551228275 23288287361966921326842413)
          ·
            refine ⟨8733107760737595497565905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23288287361966921326842413 8733107760737595497565905)
            ·
              refine ⟨6549830820553196623174429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8733107760737595497565905 6549830820553196623174429)
              ·
                refine ⟨2456186557707448733690411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6549830820553196623174429 2456186557707448733690411)
                ·
                  refine ⟨3684279836561173100535617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456186557707448733690411 3684279836561173100535617)
                  ·
                    refine ⟨2763209877420879825401713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684279836561173100535617 2763209877420879825401713)
                    ·
                      refine ⟨2072407408065659869051285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763209877420879825401713 2072407408065659869051285)
                      ·
                        rfl

theorem cell23_4035999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_4035999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4035999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4035999 prefixEnd_4035999 := by exact prefixLift 4035999
  have htrace : WordTrace (prefixWord ++ tailWord_4035999) baseStart_4035999 baseEnd_4035999 := by
    simpa [prefixWord, tailWord_4035999, baseEnd_4035999] using wordTrace_append hprefix tailTrace_4035999
  have hstable : (prefixWord ++ tailWord_4035999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4035999).length < 2 ^ (prefixWord ++ tailWord_4035999).sum := by decide
  have hdescent : baseEnd_4035999 < baseStart_4035999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4035999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036002 : List Nat := [3, 3, 1, 2, 1, 2, 4, 1, 1, 2, 3]
def baseStart_4036002 : Nat := 118140960795 + 4036002 * 2 ^ 59
def prefixEnd_4036002 : Nat := 4983230072969 + 3 ^ 40 * 4036002 * 2
def baseEnd_4036002 : Nat := 2072408948507623357313771

theorem tailTrace_4036002 : CollatzResearch.WordTrace tailWord_4036002 prefixEnd_4036002 2072408948507623357313771 := by
  unfold tailWord_4036002
  simp only [CollatzResearch.WordTrace]
  refine ⟨36801271581065380777297565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98136724216174348739460173 36801271581065380777297565)
  ·
    refine ⟨13800476842899517791486587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36801271581065380777297565 13800476842899517791486587)
    ·
      refine ⟨20700715264349276687229881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13800476842899517791486587 20700715264349276687229881)
      ·
        refine ⟨15525536448261957515422411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20700715264349276687229881 15525536448261957515422411)
        ·
          refine ⟨23288304672392936273133617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525536448261957515422411 23288304672392936273133617)
          ·
            refine ⟨17466228504294702204850213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23288304672392936273133617 17466228504294702204850213)
            ·
              refine ⟨3274917844555256663409415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17466228504294702204850213 3274917844555256663409415)
              ·
                refine ⟨4912376766832884995114123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274917844555256663409415 4912376766832884995114123)
                ·
                  refine ⟨7368565150249327492671185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912376766832884995114123 7368565150249327492671185)
                  ·
                    refine ⟨5526423862686995619503389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368565150249327492671185 5526423862686995619503389)
                    ·
                      refine ⟨2072408948507623357313771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5526423862686995619503389 2072408948507623357313771)
                      ·
                        rfl

theorem cell23_4036002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_4036002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036002 prefixEnd_4036002 := by exact prefixLift 4036002
  have htrace : WordTrace (prefixWord ++ tailWord_4036002) baseStart_4036002 baseEnd_4036002 := by
    simpa [prefixWord, tailWord_4036002, baseEnd_4036002] using wordTrace_append hprefix tailTrace_4036002
  have hstable : (prefixWord ++ tailWord_4036002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036002).length < 2 ^ (prefixWord ++ tailWord_4036002).sum := by decide
  have hdescent : baseEnd_4036002 < baseStart_4036002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036041 : List Nat := [1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 5]
def baseStart_4036041 : Nat := 118140960795 + 4036041 * 2 ^ 59
def prefixEnd_4036041 : Nat := 4983230072969 + 3 ^ 40 * 4036041 * 2
def baseEnd_4036041 : Nat := 2072428974253148704726091

theorem tailTrace_4036041 : CollatzResearch.WordTrace tailWord_4036041 prefixEnd_4036041 2072428974253148704726091 := by
  unfold tailWord_4036041
  simp only [CollatzResearch.WordTrace]
  refine ⟨147206508771120232769859977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98137672514080155179906651 147206508771120232769859977)
  ·
    refine ⟨110404881578340174577394983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147206508771120232769859977 110404881578340174577394983)
    ·
      refine ⟨165607322367510261866092475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110404881578340174577394983 165607322367510261866092475)
      ·
        refine ⟨248410983551265392799138713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165607322367510261866092475 248410983551265392799138713)
        ·
          refine ⟨186308237663449044599354035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248410983551265392799138713 186308237663449044599354035)
          ·
            refine ⟨279462356495173566899031053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186308237663449044599354035 279462356495173566899031053)
            ·
              refine ⟨104798383685690087587136645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279462356495173566899031053 104798383685690087587136645)
              ·
                refine ⟨19649696941066891422588121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104798383685690087587136645 19649696941066891422588121)
                ·
                  refine ⟨14737272705800168566941091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19649696941066891422588121 14737272705800168566941091)
                  ·
                    refine ⟨22105909058700252850411637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14737272705800168566941091 22105909058700252850411637)
                    ·
                      refine ⟨2072428974253148704726091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22105909058700252850411637 2072428974253148704726091)
                      ·
                        rfl

theorem cell23_4036041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 4, 2, 1, 5].length) (baseStart_4036041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036041 prefixEnd_4036041 := by exact prefixLift 4036041
  have htrace : WordTrace (prefixWord ++ tailWord_4036041) baseStart_4036041 baseEnd_4036041 := by
    simpa [prefixWord, tailWord_4036041, baseEnd_4036041] using wordTrace_append hprefix tailTrace_4036041
  have hstable : (prefixWord ++ tailWord_4036041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036041).length < 2 ^ (prefixWord ++ tailWord_4036041).sum := by decide
  have hdescent : baseEnd_4036041 < baseStart_4036041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036042 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2]
def baseStart_4036042 : Nat := 118140960795 + 4036042 * 2 ^ 59
def prefixEnd_4036042 : Nat := 4983230072969 + 3 ^ 40 * 4036042 * 2
def baseEnd_4036042 : Nat := 2072429487733803200813587

theorem tailTrace_4036042 : CollatzResearch.WordTrace tailWord_4036042 prefixEnd_4036042 2072429487733803200813587 := by
  unfold tailWord_4036042
  simp only [CollatzResearch.WordTrace]
  refine ⟨36801636311029152485161595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98137696829411073293764253 36801636311029152485161595)
  ·
    refine ⟨55202454466543728727742393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36801636311029152485161595 55202454466543728727742393)
    ·
      refine ⟨41401840849907796545806795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55202454466543728727742393 41401840849907796545806795)
      ·
        refine ⟨62102761274861694818710193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41401840849907796545806795 62102761274861694818710193)
        ·
          refine ⟨46577070956146271114032645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62102761274861694818710193 46577070956146271114032645)
          ·
            refine ⟨8733200804277425833881121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46577070956146271114032645 8733200804277425833881121)
            ·
              refine ⟨6549900603208069375410841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8733200804277425833881121 6549900603208069375410841)
              ·
                refine ⟨4912425452406052031558131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6549900603208069375410841 4912425452406052031558131)
                ·
                  refine ⟨7368638178609078047337197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912425452406052031558131 7368638178609078047337197)
                  ·
                    refine ⟨2763239316978404267751449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7368638178609078047337197 2763239316978404267751449)
                    ·
                      refine ⟨2072429487733803200813587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763239316978404267751449 2072429487733803200813587)
                      ·
                        rfl

theorem cell23_4036042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_4036042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036042 prefixEnd_4036042 := by exact prefixLift 4036042
  have htrace : WordTrace (prefixWord ++ tailWord_4036042) baseStart_4036042 baseEnd_4036042 := by
    simpa [prefixWord, tailWord_4036042, baseEnd_4036042] using wordTrace_append hprefix tailTrace_4036042
  have hstable : (prefixWord ++ tailWord_4036042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036042).length < 2 ^ (prefixWord ++ tailWord_4036042).sum := by decide
  have hdescent : baseEnd_4036042 < baseStart_4036042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036058 : List Nat := [3, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_4036058 : Nat := 118140960795 + 4036058 * 2 ^ 59
def prefixEnd_4036058 : Nat := 4983230072969 + 3 ^ 40 * 4036058 * 2
def baseEnd_4036058 : Nat := 2072437703424275138213513

theorem tailTrace_4036058 : CollatzResearch.WordTrace tailWord_4036058 prefixEnd_4036058 2072437703424275138213513 := by
  unfold tailWord_4036058
  simp only [CollatzResearch.WordTrace]
  refine ⟨36801782203014661168307207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98138085874705763115485885 36801782203014661168307207)
  ·
    refine ⟨55202673304521991752460811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36801782203014661168307207 55202673304521991752460811)
    ·
      refine ⟨82804009956782987628691217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55202673304521991752460811 82804009956782987628691217)
      ·
        refine ⟨62103007467587240721518413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82804009956782987628691217 62103007467587240721518413)
        ·
          refine ⟨23288627800345215270569405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62103007467587240721518413 23288627800345215270569405)
          ·
            refine ⟨8733235425129455726463527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23288627800345215270569405 8733235425129455726463527)
            ·
              refine ⟨13099853137694183589695291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733235425129455726463527 13099853137694183589695291)
              ·
                refine ⟨19649779706541275384542937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13099853137694183589695291 19649779706541275384542937)
                ·
                  refine ⟨14737334779905956538407203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19649779706541275384542937 14737334779905956538407203)
                  ·
                    refine ⟨22106002169858934807610805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14737334779905956538407203 22106002169858934807610805)
                    ·
                      refine ⟨2072437703424275138213513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22106002169858934807610805 2072437703424275138213513)
                      ·
                        rfl

theorem cell23_4036058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_4036058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036058 prefixEnd_4036058 := by exact prefixLift 4036058
  have htrace : WordTrace (prefixWord ++ tailWord_4036058) baseStart_4036058 baseEnd_4036058 := by
    simpa [prefixWord, tailWord_4036058, baseEnd_4036058] using wordTrace_append hprefix tailTrace_4036058
  have hstable : (prefixWord ++ tailWord_4036058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036058).length < 2 ^ (prefixWord ++ tailWord_4036058).sum := by decide
  have hdescent : baseEnd_4036058 < baseStart_4036058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036072 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_4036072 : Nat := 118140960795 + 4036072 * 2 ^ 59
def prefixEnd_4036072 : Nat := 4983230072969 + 3 ^ 40 * 4036072 * 2
def baseEnd_4036072 : Nat := 2072444892153438083438449

theorem tailTrace_4036072 : CollatzResearch.WordTrace tailWord_4036072 prefixEnd_4036072 2072444892153438083438449 := by
  unfold tailWord_4036072
  simp only [CollatzResearch.WordTrace]
  refine ⟨73603819717003962532119235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98138426289338616709492313 73603819717003962532119235)
  ·
    refine ⟨110405729575505943798178853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73603819717003962532119235 110405729575505943798178853)
    ·
      refine ⟨20701074295407364462158535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110405729575505943798178853 20701074295407364462158535)
      ·
        refine ⟨31051611443111046693237803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20701074295407364462158535 31051611443111046693237803)
        ·
          refine ⟨46577417164666570039856705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31051611443111046693237803 46577417164666570039856705)
          ·
            refine ⟨34933062873499927529892529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46577417164666570039856705 34933062873499927529892529)
            ·
              refine ⟨26199797155124945647419397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34933062873499927529892529 26199797155124945647419397)
              ·
                refine ⟨4912461966585927308891137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26199797155124945647419397 4912461966585927308891137)
                ·
                  refine ⟨3684346474939445481668353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4912461966585927308891137 3684346474939445481668353)
                  ·
                    refine ⟨2763259856204584111251265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684346474939445481668353 2763259856204584111251265)
                    ·
                      refine ⟨2072444892153438083438449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763259856204584111251265 2072444892153438083438449)
                      ·
                        rfl

theorem cell23_4036072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_4036072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036072 prefixEnd_4036072 := by exact prefixLift 4036072
  have htrace : WordTrace (prefixWord ++ tailWord_4036072) baseStart_4036072 baseEnd_4036072 := by
    simpa [prefixWord, tailWord_4036072, baseEnd_4036072] using wordTrace_append hprefix tailTrace_4036072
  have hstable : (prefixWord ++ tailWord_4036072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036072).length < 2 ^ (prefixWord ++ tailWord_4036072).sum := by decide
  have hdescent : baseEnd_4036072 < baseStart_4036072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036101 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7]
def baseStart_4036101 : Nat := 118140960795 + 4036101 * 2 ^ 59
def prefixEnd_4036101 : Nat := 4983230072969 + 3 ^ 40 * 4036101 * 2
def baseEnd_4036101 : Nat := 2072459783092418469975815

theorem tailTrace_4036101 : CollatzResearch.WordTrace tailWord_4036101 prefixEnd_4036101 2072459783092418469975815 := by
  unfold tailWord_4036101
  simp only [CollatzResearch.WordTrace]
  refine ⟨147208697150902863017044157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98139131433935242011362771 147208697150902863017044157)
  ·
    refine ⟨55203261431588573631391559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147208697150902863017044157 55203261431588573631391559)
    ·
      refine ⟨82804892147382860447087339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55203261431588573631391559 82804892147382860447087339)
      ·
        refine ⟨124207338221074290670631009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82804892147382860447087339 124207338221074290670631009)
        ·
          refine ⟨93155503665805718002973257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124207338221074290670631009 93155503665805718002973257)
          ·
            refine ⟨69866627749354288502229943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93155503665805718002973257 69866627749354288502229943)
            ·
              refine ⟨104799941624031432753344915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69866627749354288502229943 104799941624031432753344915)
              ·
                refine ⟨157199912436047149130017373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104799941624031432753344915 157199912436047149130017373)
                ·
                  refine ⟨58949967163517680923756515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157199912436047149130017373 58949967163517680923756515)
                  ·
                    refine ⟨88424950745276521385634773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58949967163517680923756515 88424950745276521385634773)
                    ·
                      refine ⟨2072459783092418469975815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 88424950745276521385634773 2072459783092418469975815)
                      ·
                        rfl

theorem cell23_4036101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_4036101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036101 prefixEnd_4036101 := by exact prefixLift 4036101
  have htrace : WordTrace (prefixWord ++ tailWord_4036101) baseStart_4036101 baseEnd_4036101 := by
    simpa [prefixWord, tailWord_4036101, baseEnd_4036101] using wordTrace_append hprefix tailTrace_4036101
  have hstable : (prefixWord ++ tailWord_4036101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036101).length < 2 ^ (prefixWord ++ tailWord_4036101).sum := by decide
  have hdescent : baseEnd_4036101 < baseStart_4036101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036172 : List Nat := [2, 2, 1, 3, 1, 3, 1, 5, 1, 4]
def baseStart_4036172 : Nat := 118140960795 + 4036172 * 2 ^ 59
def prefixEnd_4036172 : Nat := 4983230072969 + 3 ^ 40 * 4036172 * 2
def baseEnd_4036172 : Nat := 690832080072962564062663

theorem tailTrace_4036172 : CollatzResearch.WordTrace tailWord_4036172 prefixEnd_4036172 690832080072962564062663 := by
  unfold tailWord_4036172
  simp only [CollatzResearch.WordTrace]
  refine ⟨73605643366822821071439385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98140857822430428095252513 73605643366822821071439385)
  ·
    refine ⟨55204232525117115803579539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73605643366822821071439385 55204232525117115803579539)
    ·
      refine ⟨82806348787675673705369309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55204232525117115803579539 82806348787675673705369309)
      ·
        refine ⟨31052380795378377639513491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82806348787675673705369309 31052380795378377639513491)
        ·
          refine ⟨46578571193067566459270237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31052380795378377639513491 46578571193067566459270237)
          ·
            refine ⟨17466964197400337422226339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46578571193067566459270237 17466964197400337422226339)
            ·
              refine ⟨26200446296100506133339509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17466964197400337422226339 26200446296100506133339509)
              ·
                refine ⟨2456291840259422450000579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26200446296100506133339509 2456291840259422450000579)
                ·
                  refine ⟨3684437760389133675000869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456291840259422450000579 3684437760389133675000869)
                  ·
                    refine ⟨690832080072962564062663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684437760389133675000869 690832080072962564062663)
                    ·
                      rfl

theorem cell23_4036172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 1, 4].length) (baseStart_4036172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036172 prefixEnd_4036172 := by exact prefixLift 4036172
  have htrace : WordTrace (prefixWord ++ tailWord_4036172) baseStart_4036172 baseEnd_4036172 := by
    simpa [prefixWord, tailWord_4036172, baseEnd_4036172] using wordTrace_append hprefix tailTrace_4036172
  have hstable : (prefixWord ++ tailWord_4036172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036172).length < 2 ^ (prefixWord ++ tailWord_4036172).sum := by decide
  have hdescent : baseEnd_4036172 < baseStart_4036172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036202 : List Nat := [3, 1, 3, 2, 1, 3, 3, 1, 6]
def baseStart_4036202 : Nat := 118140960795 + 4036202 * 2 ^ 59
def prefixEnd_4036202 : Nat := 4983230072969 + 3 ^ 40 * 4036202 * 2
def baseEnd_4036202 : Nat := 230279071626502508312539

theorem tailTrace_4036202 : CollatzResearch.WordTrace tailWord_4036202 prefixEnd_4036202 230279071626502508312539 := by
  unfold tailWord_4036202
  simp only [CollatzResearch.WordTrace]
  refine ⟨36803095230884239316617715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98141587282357971510980573 36803095230884239316617715)
  ·
    refine ⟨55204642846326358974926573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36803095230884239316617715 55204642846326358974926573)
    ·
      refine ⟨20701741067372384615597465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55204642846326358974926573 20701741067372384615597465)
      ·
        refine ⟨15526305800529288461698099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20701741067372384615597465 15526305800529288461698099)
        ·
          refine ⟨23289458700793932692547149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526305800529288461698099 23289458700793932692547149)
          ·
            refine ⟨8733547012797724759705181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23289458700793932692547149 8733547012797724759705181)
            ·
              refine ⟨3275080129799146784889443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8733547012797724759705181 3275080129799146784889443)
              ·
                refine ⟨4912620194698720177334165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275080129799146784889443 4912620194698720177334165)
                ·
                  refine ⟨230279071626502508312539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4912620194698720177334165 230279071626502508312539)
                  ·
                    rfl

theorem cell23_4036202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 6].length) (baseStart_4036202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036202 prefixEnd_4036202 := by exact prefixLift 4036202
  have htrace : WordTrace (prefixWord ++ tailWord_4036202) baseStart_4036202 baseEnd_4036202 := by
    simpa [prefixWord, tailWord_4036202, baseEnd_4036202] using wordTrace_append hprefix tailTrace_4036202
  have hstable : (prefixWord ++ tailWord_4036202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036202).length < 2 ^ (prefixWord ++ tailWord_4036202).sum := by decide
  have hdescent : baseEnd_4036202 < baseStart_4036202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036235 : List Nat := [1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 4]
def baseStart_4036235 : Nat := 118140960795 + 4036235 * 2 ^ 59
def prefixEnd_4036235 : Nat := 4983230072969 + 3 ^ 40 * 4036235 * 2
def baseEnd_4036235 : Nat := 2072528589500120945700199

theorem tailTrace_4036235 : CollatzResearch.WordTrace tailWord_4036235 prefixEnd_4036235 2072528589500120945700199 := by
  unfold tailWord_4036235
  simp only [CollatzResearch.WordTrace]
  refine ⟨147213584532417403902422159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98142389688278269268281439 147213584532417403902422159)
  ·
    refine ⟨220820376798626105853633239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147213584532417403902422159 220820376798626105853633239)
    ·
      refine ⟨331230565197939158780449859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220820376798626105853633239 331230565197939158780449859)
      ·
        refine ⟨496845847796908738170674789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331230565197939158780449859 496845847796908738170674789)
        ·
          refine ⟨93158596461920388407001523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496845847796908738170674789 93158596461920388407001523)
          ·
            refine ⟨139737894692880582610502285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93158596461920388407001523 139737894692880582610502285)
            ·
              refine ⟨52401710509830218478938357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139737894692880582610502285 52401710509830218478938357)
              ·
                refine ⟨4912660360296582982400471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52401710509830218478938357 4912660360296582982400471)
                ·
                  refine ⟨7368990540444874473600707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912660360296582982400471 7368990540444874473600707)
                  ·
                    refine ⟨11053485810667311710401061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7368990540444874473600707 11053485810667311710401061)
                    ·
                      refine ⟨2072528589500120945700199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11053485810667311710401061 2072528589500120945700199)
                      ·
                        rfl

theorem cell23_4036235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 5, 1, 1, 4].length) (baseStart_4036235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036235 prefixEnd_4036235 := by exact prefixLift 4036235
  have htrace : WordTrace (prefixWord ++ tailWord_4036235) baseStart_4036235 baseEnd_4036235 := by
    simpa [prefixWord, tailWord_4036235, baseEnd_4036235] using wordTrace_append hprefix tailTrace_4036235
  have hstable : (prefixWord ++ tailWord_4036235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036235).length < 2 ^ (prefixWord ++ tailWord_4036235).sum := by decide
  have hdescent : baseEnd_4036235 < baseStart_4036235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036269 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4036269 : Nat := 118140960795 + 4036269 * 2 ^ 59
def prefixEnd_4036269 : Nat := 4983230072969 + 3 ^ 40 * 4036269 * 2
def baseEnd_4036269 : Nat := 2072546047842373812675043

theorem tailTrace_4036269 : CollatzResearch.WordTrace tailWord_4036269 prefixEnd_4036269 2072546047842373812675043 := by
  unfold tailWord_4036269
  simp only [CollatzResearch.WordTrace]
  refine ⟨147214824614294227709159861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98143216409529485139439907 147214824614294227709159861)
  ·
    refine ⟨13801389807590083847733737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147214824614294227709159861 13801389807590083847733737)
    ·
      refine ⟨10351042355692562885800303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13801389807590083847733737 10351042355692562885800303)
      ·
        refine ⟨15526563533538844328700455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351042355692562885800303 15526563533538844328700455)
        ·
          refine ⟨23289845300308266493050683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526563533538844328700455 23289845300308266493050683)
          ·
            refine ⟨34934767950462399739576025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23289845300308266493050683 34934767950462399739576025)
            ·
              refine ⟨26201075962846799804682019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34934767950462399739576025 26201075962846799804682019)
              ·
                refine ⟨39301613944270199707023029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26201075962846799804682019 39301613944270199707023029)
                ·
                  refine ⟨3684526307275331222533409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39301613944270199707023029 3684526307275331222533409)
                  ·
                    refine ⟨2763394730456498416900057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684526307275331222533409 2763394730456498416900057)
                    ·
                      refine ⟨2072546047842373812675043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763394730456498416900057 2072546047842373812675043)
                      ·
                        rfl

theorem cell23_4036269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4036269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036269 prefixEnd_4036269 := by exact prefixLift 4036269
  have htrace : WordTrace (prefixWord ++ tailWord_4036269) baseStart_4036269 baseEnd_4036269 := by
    simpa [prefixWord, tailWord_4036269, baseEnd_4036269] using wordTrace_append hprefix tailTrace_4036269
  have hstable : (prefixWord ++ tailWord_4036269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036269).length < 2 ^ (prefixWord ++ tailWord_4036269).sum := by decide
  have hdescent : baseEnd_4036269 < baseStart_4036269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036272 : List Nat := [2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_4036272 : Nat := 118140960795 + 4036272 * 2 ^ 59
def prefixEnd_4036272 : Nat := 4983230072969 + 3 ^ 40 * 4036272 * 2
def baseEnd_4036272 : Nat := 2072547588284337300937529

theorem tailTrace_4036272 : CollatzResearch.WordTrace tailWord_4036272 prefixEnd_4036272 2072547588284337300937529 := by
  unfold tailWord_4036272
  simp only [CollatzResearch.WordTrace]
  refine ⟨73607467016641679610759535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98143289355522239481012713 73607467016641679610759535)
  ·
    refine ⟨110411200524962519416139303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73607467016641679610759535 110411200524962519416139303)
    ·
      refine ⟨165616800787443779124208955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110411200524962519416139303 165616800787443779124208955)
      ·
        refine ⟨248425201181165668686313433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165616800787443779124208955 248425201181165668686313433)
        ·
          refine ⟨186318900885874251514735075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248425201181165668686313433 186318900885874251514735075)
          ·
            refine ⟨279478351328811377272102613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186318900885874251514735075 279478351328811377272102613)
            ·
              refine ⟨6550273859269016654814905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 279478351328811377272102613 6550273859269016654814905)
              ·
                refine ⟨4912705394451762491111179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550273859269016654814905 4912705394451762491111179)
                ·
                  refine ⟨7369058091677643736666769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912705394451762491111179 7369058091677643736666769)
                  ·
                    refine ⟨5526793568758232802500077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369058091677643736666769 5526793568758232802500077)
                    ·
                      refine ⟨2072547588284337300937529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5526793568758232802500077 2072547588284337300937529)
                      ·
                        rfl

theorem cell23_4036272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_4036272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036272 prefixEnd_4036272 := by exact prefixLift 4036272
  have htrace : WordTrace (prefixWord ++ tailWord_4036272) baseStart_4036272 baseEnd_4036272 := by
    simpa [prefixWord, tailWord_4036272, baseEnd_4036272] using wordTrace_append hprefix tailTrace_4036272
  have hstable : (prefixWord ++ tailWord_4036272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036272).length < 2 ^ (prefixWord ++ tailWord_4036272).sum := by decide
  have hdescent : baseEnd_4036272 < baseStart_4036272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036312 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_4036312 : Nat := 118140960795 + 4036312 * 2 ^ 59
def prefixEnd_4036312 : Nat := 4983230072969 + 3 ^ 40 * 4036312 * 2
def baseEnd_4036312 : Nat := 2072568127510517144437345

theorem tailTrace_4036312 : CollatzResearch.WordTrace tailWord_4036312 prefixEnd_4036312 2072568127510517144437345 := by
  unfold tailWord_4036312
  simp only [CollatzResearch.WordTrace]
  refine ⟨73608196476569223026487595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98144261968758964035316793 73608196476569223026487595)
  ·
    refine ⟨110412294714853834539731393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73608196476569223026487595 110412294714853834539731393)
    ·
      refine ⟨82809221036140375904798545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110412294714853834539731393 82809221036140375904798545)
      ·
        refine ⟨62106915777105281928598909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82809221036140375904798545 62106915777105281928598909)
        ·
          refine ⟨23290093416414480723224591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62106915777105281928598909 23290093416414480723224591)
          ·
            refine ⟨34935140124621721084836887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23290093416414480723224591 34935140124621721084836887)
            ·
              refine ⟨52402710186932581627255331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34935140124621721084836887 52402710186932581627255331)
              ·
                refine ⟨78604065280398872440882997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52402710186932581627255331 78604065280398872440882997)
                ·
                  refine ⟨7369131120037394291332781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78604065280398872440882997 7369131120037394291332781)
                  ·
                    refine ⟨2763424170014022859249793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7369131120037394291332781 2763424170014022859249793)
                    ·
                      refine ⟨2072568127510517144437345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763424170014022859249793 2072568127510517144437345)
                      ·
                        rfl

theorem cell23_4036312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_4036312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036312 prefixEnd_4036312 := by exact prefixLift 4036312
  have htrace : WordTrace (prefixWord ++ tailWord_4036312) baseStart_4036312 baseEnd_4036312 := by
    simpa [prefixWord, tailWord_4036312, baseEnd_4036312] using wordTrace_append hprefix tailTrace_4036312
  have hstable : (prefixWord ++ tailWord_4036312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036312).length < 2 ^ (prefixWord ++ tailWord_4036312).sum := by decide
  have hdescent : baseEnd_4036312 < baseStart_4036312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036325 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4036325 : Nat := 118140960795 + 4036325 * 2 ^ 59
def prefixEnd_4036325 : Nat := 4983230072969 + 3 ^ 40 * 4036325 * 2
def baseEnd_4036325 : Nat := 2072574802759025593574785

theorem tailTrace_4036325 : CollatzResearch.WordTrace tailWord_4036325 prefixEnd_4036325 2072574802759025593574785 := by
  unfold tailWord_4036325
  simp only [CollatzResearch.WordTrace]
  refine ⟨147216867102091349273198429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98144578068060899515465619 147216867102091349273198429)
  ·
    refine ⟨55206325163284255977449411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147216867102091349273198429 55206325163284255977449411)
    ·
      refine ⟨82809487744926383966174117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55206325163284255977449411 82809487744926383966174117)
      ·
        refine ⟨15526778952173696993657647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82809487744926383966174117 15526778952173696993657647)
        ·
          refine ⟨23290168428260545490486471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526778952173696993657647 23290168428260545490486471)
          ·
            refine ⟨34935252642390818235729707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23290168428260545490486471 34935252642390818235729707)
            ·
              refine ⟨52402878963586227353594561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34935252642390818235729707 52402878963586227353594561)
              ·
                refine ⟨39302159222689670515195921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52402878963586227353594561 39302159222689670515195921)
                ·
                  refine ⟨29476619417017252886396941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39302159222689670515195921 29476619417017252886396941)
                  ·
                    refine ⟨11053732281381469832398853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29476619417017252886396941 11053732281381469832398853)
                    ·
                      refine ⟨2072574802759025593574785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11053732281381469832398853 2072574802759025593574785)
                      ·
                        rfl

theorem cell23_4036325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4036325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036325 prefixEnd_4036325 := by exact prefixLift 4036325
  have htrace : WordTrace (prefixWord ++ tailWord_4036325) baseStart_4036325 baseEnd_4036325 := by
    simpa [prefixWord, tailWord_4036325, baseEnd_4036325] using wordTrace_append hprefix tailTrace_4036325
  have hstable : (prefixWord ++ tailWord_4036325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036325).length < 2 ^ (prefixWord ++ tailWord_4036325).sum := by decide
  have hdescent : baseEnd_4036325 < baseStart_4036325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036340 : List Nat := [2, 6, 1, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4036340 : Nat := 118140960795 + 4036340 * 2 ^ 59
def prefixEnd_4036340 : Nat := 4983230072969 + 3 ^ 40 * 4036340 * 2
def baseEnd_4036340 : Nat := 2072582504968843034887217

theorem tailTrace_4036340 : CollatzResearch.WordTrace tailWord_4036340 prefixEnd_4036340 2072582504968843034887217 := by
  unfold tailWord_4036340
  simp only [CollatzResearch.WordTrace]
  refine ⟨73608707098518503417497237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98144942798024671223329649 73608707098518503417497237)
  ·
    refine ⟨3450408145243054847695183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 73608707098518503417497237 3450408145243054847695183)
    ·
      refine ⟨5175612217864582271542775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3450408145243054847695183 5175612217864582271542775)
      ·
        refine ⟨7763418326796873407314163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5175612217864582271542775 7763418326796873407314163)
        ·
          refine ⟨11645127490195310110971245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7763418326796873407314163 11645127490195310110971245)
          ·
            refine ⟨4366922808823241291614217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11645127490195310110971245 4366922808823241291614217)
            ·
              refine ⟨3275192106617430968710663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366922808823241291614217 3275192106617430968710663)
              ·
                refine ⟨4912788159926146453065995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275192106617430968710663 4912788159926146453065995)
                ·
                  refine ⟨7369182239889219679598993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912788159926146453065995 7369182239889219679598993)
                  ·
                    refine ⟨5526886679916914759699245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369182239889219679598993 5526886679916914759699245)
                    ·
                      refine ⟨2072582504968843034887217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5526886679916914759699245 2072582504968843034887217)
                      ·
                        rfl

theorem cell23_4036340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4036340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036340 prefixEnd_4036340 := by exact prefixLift 4036340
  have htrace : WordTrace (prefixWord ++ tailWord_4036340) baseStart_4036340 baseEnd_4036340 := by
    simpa [prefixWord, tailWord_4036340, baseEnd_4036340] using wordTrace_append hprefix tailTrace_4036340
  have hstable : (prefixWord ++ tailWord_4036340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036340).length < 2 ^ (prefixWord ++ tailWord_4036340).sum := by decide
  have hdescent : baseEnd_4036340 < baseStart_4036340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036355 : List Nat := [1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_4036355 : Nat := 118140960795 + 4036355 * 2 ^ 59
def prefixEnd_4036355 : Nat := 4983230072969 + 3 ^ 40 * 4036355 * 2
def baseEnd_4036355 : Nat := 2072590207178660476199647

theorem tailTrace_4036355 : CollatzResearch.WordTrace tailWord_4036355 prefixEnd_4036355 2072590207178660476199647 := by
  unfold tailWord_4036355
  simp only [CollatzResearch.WordTrace]
  refine ⟨147217961291982664396790519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98145307527988442931193679 147217961291982664396790519)
  ·
    refine ⟨220826941937973996595185779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147217961291982664396790519 220826941937973996595185779)
    ·
      refine ⟨331240412906960994892778669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220826941937973996595185779 331240412906960994892778669)
      ·
        refine ⟨124215154840110373084792001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331240412906960994892778669 124215154840110373084792001)
        ·
          refine ⟨93161366130082779813594001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124215154840110373084792001 93161366130082779813594001)
          ·
            refine ⟨69871024597562084860195501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93161366130082779813594001 69871024597562084860195501)
            ·
              refine ⟨26201634224085781822573313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69871024597562084860195501 26201634224085781822573313)
              ·
                refine ⟨19651225668064336366929985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26201634224085781822573313 19651225668064336366929985)
                ·
                  refine ⟨14738419251048252275197489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19651225668064336366929985 14738419251048252275197489)
                  ·
                    refine ⟨11053814438286189206398117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14738419251048252275197489 11053814438286189206398117)
                    ·
                      refine ⟨2072590207178660476199647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11053814438286189206398117 2072590207178660476199647)
                      ·
                        rfl

theorem cell23_4036355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_4036355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036355 prefixEnd_4036355 := by exact prefixLift 4036355
  have htrace : WordTrace (prefixWord ++ tailWord_4036355) baseStart_4036355 baseEnd_4036355 := by
    simpa [prefixWord, tailWord_4036355, baseEnd_4036355] using wordTrace_append hprefix tailTrace_4036355
  have hstable : (prefixWord ++ tailWord_4036355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036355).length < 2 ^ (prefixWord ++ tailWord_4036355).sum := by decide
  have hdescent : baseEnd_4036355 < baseStart_4036355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036432 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2]
def baseStart_4036432 : Nat := 118140960795 + 4036432 * 2 ^ 59
def prefixEnd_4036432 : Nat := 4983230072969 + 3 ^ 40 * 4036432 * 2
def baseEnd_4036432 : Nat := 2072629745189056674936793

theorem tailTrace_4036432 : CollatzResearch.WordTrace tailWord_4036432 prefixEnd_4036432 2072629745189056674936793 := by
  unfold tailWord_4036432
  simp only [CollatzResearch.WordTrace]
  refine ⟨73610384856351853273671775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98147179808469137698229033 73610384856351853273671775)
  ·
    refine ⟨110415577284527779910507663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73610384856351853273671775 110415577284527779910507663)
    ·
      refine ⟨165623365926791669865761495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110415577284527779910507663 165623365926791669865761495)
      ·
        refine ⟨248435048890187504798642243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165623365926791669865761495 248435048890187504798642243)
        ·
          refine ⟨372652573335281257197963365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248435048890187504798642243 372652573335281257197963365)
          ·
            refine ⟨69872357500365235724618131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372652573335281257197963365 69872357500365235724618131)
            ·
              refine ⟨104808536250547853586927197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69872357500365235724618131 104808536250547853586927197)
              ·
                refine ⟨39303201093955445095097699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104808536250547853586927197 39303201093955445095097699)
                ·
                  refine ⟨58954801640933167642646549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39303201093955445095097699 58954801640933167642646549)
                  ·
                    refine ⟨2763506326918742233249057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58954801640933167642646549 2763506326918742233249057)
                    ·
                      refine ⟨2072629745189056674936793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763506326918742233249057 2072629745189056674936793)
                      ·
                        rfl

theorem cell23_4036432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 6, 2].length) (baseStart_4036432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036432 prefixEnd_4036432 := by exact prefixLift 4036432
  have htrace : WordTrace (prefixWord ++ tailWord_4036432) baseStart_4036432 baseEnd_4036432 := by
    simpa [prefixWord, tailWord_4036432, baseEnd_4036432] using wordTrace_append hprefix tailTrace_4036432
  have hstable : (prefixWord ++ tailWord_4036432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036432).length < 2 ^ (prefixWord ++ tailWord_4036432).sum := by decide
  have hdescent : baseEnd_4036432 < baseStart_4036432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036442 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 5, 4]
def baseStart_4036442 : Nat := 118140960795 + 4036442 * 2 ^ 59
def prefixEnd_4036442 : Nat := 4983230072969 + 3 ^ 40 * 4036442 * 2
def baseEnd_4036442 : Nat := 690878293331867211937249

theorem tailTrace_4036442 : CollatzResearch.WordTrace tailWord_4036442 prefixEnd_4036442 690878293331867211937249 := by
  unfold tailWord_4036442
  simp only [CollatzResearch.WordTrace]
  refine ⟨36805283610666869563801895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98147422961778318836805053 36805283610666869563801895)
  ·
    refine ⟨55207925416000304345702843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36805283610666869563801895 55207925416000304345702843)
    ·
      refine ⟨82811888124000456518554265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55207925416000304345702843 82811888124000456518554265)
      ·
        refine ⟨62108916093000342388915699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82811888124000456518554265 62108916093000342388915699)
        ·
          refine ⟨93163374139500513583373549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62108916093000342388915699 93163374139500513583373549)
          ·
            refine ⟨34936265302312692593765081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93163374139500513583373549 34936265302312692593765081)
            ·
              refine ⟨26202198976734519445323811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34936265302312692593765081 26202198976734519445323811)
              ·
                refine ⟨39303298465101779167985717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26202198976734519445323811 39303298465101779167985717)
                ·
                  refine ⟨3684684231103291796998661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39303298465101779167985717 3684684231103291796998661)
                  ·
                    refine ⟨690878293331867211937249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684684231103291796998661 690878293331867211937249)
                    ·
                      rfl

theorem cell23_4036442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_4036442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036442 prefixEnd_4036442 := by exact prefixLift 4036442
  have htrace : WordTrace (prefixWord ++ tailWord_4036442) baseStart_4036442 baseEnd_4036442 := by
    simpa [prefixWord, tailWord_4036442, baseEnd_4036442] using wordTrace_append hprefix tailTrace_4036442
  have hstable : (prefixWord ++ tailWord_4036442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036442).length < 2 ^ (prefixWord ++ tailWord_4036442).sum := by decide
  have hdescent : baseEnd_4036442 < baseStart_4036442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036459 : List Nat := [1, 1, 1, 1, 2, 2, 3, 7, 1, 4]
def baseStart_4036459 : Nat := 118140960795 + 4036459 * 2 ^ 59
def prefixEnd_4036459 : Nat := 4983230072969 + 3 ^ 40 * 4036459 * 2
def baseEnd_4036459 : Nat := 690881203055576023099723

theorem tailTrace_4036459 : CollatzResearch.WordTrace tailWord_4036459 prefixEnd_4036459 690881203055576023099723 := by
  unfold tailWord_4036459
  simp only [CollatzResearch.WordTrace]
  refine ⟨147221754483605890158576431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98147836322403926772384287 147221754483605890158576431)
  ·
    refine ⟨220832631725408835237864647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147221754483605890158576431 220832631725408835237864647)
    ·
      refine ⟨331248947588113252856796971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220832631725408835237864647 331248947588113252856796971)
      ·
        refine ⟨496873421382169879285195457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331248947588113252856796971 496873421382169879285195457)
        ·
          refine ⟨372655066036627409463896593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496873421382169879285195457 372655066036627409463896593)
          ·
            refine ⟨279491299527470557097922445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372655066036627409463896593 279491299527470557097922445)
            ·
              refine ⟨104809237322801458911720917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279491299527470557097922445 104809237322801458911720917)
              ·
                refine ⟨2456466499753159193243459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104809237322801458911720917 2456466499753159193243459)
                ·
                  refine ⟨3684699749629738789865189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456466499753159193243459 3684699749629738789865189)
                  ·
                    refine ⟨690881203055576023099723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3684699749629738789865189 690881203055576023099723)
                    ·
                      rfl

theorem cell23_4036459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 1, 4].length) (baseStart_4036459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036459 prefixEnd_4036459 := by exact prefixLift 4036459
  have htrace : WordTrace (prefixWord ++ tailWord_4036459) baseStart_4036459 baseEnd_4036459 := by
    simpa [prefixWord, tailWord_4036459, baseEnd_4036459] using wordTrace_append hprefix tailTrace_4036459
  have hstable : (prefixWord ++ tailWord_4036459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036459).length < 2 ^ (prefixWord ++ tailWord_4036459).sum := by decide
  have hdescent : baseEnd_4036459 < baseStart_4036459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036469 : List Nat := [1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4036469 : Nat := 118140960795 + 4036469 * 2 ^ 59
def prefixEnd_4036469 : Nat := 4983230072969 + 3 ^ 40 * 4036469 * 2
def baseEnd_4036469 : Nat := 2072648743973273030174123

theorem tailTrace_4036469 : CollatzResearch.WordTrace tailWord_4036469 prefixEnd_4036469 2072648743973273030174123 := by
  unfold tailWord_4036469
  simp only [CollatzResearch.WordTrace]
  refine ⟨147222119213569661866440461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98148079475713107910960307 147222119213569661866440461)
  ·
    refine ⟨55208294705088623199915173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147222119213569661866440461 55208294705088623199915173)
    ·
      refine ⟨10351555257204116849984095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55208294705088623199915173 10351555257204116849984095)
      ·
        refine ⟨15527332885806175274976143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351555257204116849984095 15527332885806175274976143)
        ·
          refine ⟨23290999328709262912464215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15527332885806175274976143 23290999328709262912464215)
          ·
            refine ⟨34936498993063894368696323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23290999328709262912464215 34936498993063894368696323)
            ·
              refine ⟨52404748489595841553044485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34936498993063894368696323 52404748489595841553044485)
              ·
                refine ⟨9825890341799220291195841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52404748489595841553044485 9825890341799220291195841)
                ·
                  refine ⟨7369417756349415218396881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9825890341799220291195841 7369417756349415218396881)
                  ·
                    refine ⟨5527063317262061413797661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369417756349415218396881 5527063317262061413797661)
                    ·
                      refine ⟨2072648743973273030174123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5527063317262061413797661 2072648743973273030174123)
                      ·
                        rfl

theorem cell23_4036469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4036469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036469 prefixEnd_4036469 := by exact prefixLift 4036469
  have htrace : WordTrace (prefixWord ++ tailWord_4036469) baseStart_4036469 baseEnd_4036469 := by
    simpa [prefixWord, tailWord_4036469, baseEnd_4036469] using wordTrace_append hprefix tailTrace_4036469
  have hstable : (prefixWord ++ tailWord_4036469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036469).length < 2 ^ (prefixWord ++ tailWord_4036469).sum := by decide
  have hdescent : baseEnd_4036469 < baseStart_4036469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036475 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_4036475 : Nat := 118140960795 + 4036475 * 2 ^ 59
def prefixEnd_4036475 : Nat := 4983230072969 + 3 ^ 40 * 4036475 * 2
def baseEnd_4036475 : Nat := 2072651824857200006699095

theorem tailTrace_4036475 : CollatzResearch.WordTrace tailWord_4036475 prefixEnd_4036475 2072651824857200006699095 := by
  unfold tailWord_4036475
  simp only [CollatzResearch.WordTrace]
  refine ⟨147222338051547924891158879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98148225367698616594105919 147222338051547924891158879)
  ·
    refine ⟨220833507077321887336738319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147222338051547924891158879 220833507077321887336738319)
    ·
      refine ⟨331250260615982831005107479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220833507077321887336738319 331250260615982831005107479)
      ·
        refine ⟨496875390923974246507661219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331250260615982831005107479 496875390923974246507661219)
        ·
          refine ⟨745313086385961369761491829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496875390923974246507661219 745313086385961369761491829)
          ·
            refine ⟨69873101848683878415139859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 745313086385961369761491829 69873101848683878415139859)
            ·
              refine ⟨104809652773025817622709789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69873101848683878415139859 104809652773025817622709789)
              ·
                refine ⟨39303619789884681608516171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104809652773025817622709789 39303619789884681608516171)
                ·
                  refine ⟨58955429684827022412774257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39303619789884681608516171 58955429684827022412774257)
                  ·
                    refine ⟨44216572263620266809580693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58955429684827022412774257 44216572263620266809580693)
                    ·
                      refine ⟨2072651824857200006699095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44216572263620266809580693 2072651824857200006699095)
                      ·
                        rfl

theorem cell23_4036475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_4036475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036475 prefixEnd_4036475 := by exact prefixLift 4036475
  have htrace : WordTrace (prefixWord ++ tailWord_4036475) baseStart_4036475 baseEnd_4036475 := by
    simpa [prefixWord, tailWord_4036475, baseEnd_4036475] using wordTrace_append hprefix tailTrace_4036475
  have hstable : (prefixWord ++ tailWord_4036475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036475).length < 2 ^ (prefixWord ++ tailWord_4036475).sum := by decide
  have hdescent : baseEnd_4036475 < baseStart_4036475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036495 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_4036495 : Nat := 118140960795 + 4036495 * 2 ^ 59
def prefixEnd_4036495 : Nat := 4983230072969 + 3 ^ 40 * 4036495 * 2
def baseEnd_4036495 : Nat := 2072662094470289928449003

theorem tailTrace_4036495 : CollatzResearch.WordTrace tailWord_4036495 prefixEnd_4036495 2072662094470289928449003 := by
  unfold tailWord_4036495
  simp only [CollatzResearch.WordTrace]
  refine ⟨147223067511475468306886939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98148711674316978871257959 147223067511475468306886939)
  ·
    refine ⟨220834601267213202460330409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147223067511475468306886939 220834601267213202460330409)
    ·
      refine ⟨165625950950409901845247807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220834601267213202460330409 165625950950409901845247807)
      ·
        refine ⟨248438926425614852767871711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165625950950409901845247807 248438926425614852767871711)
        ·
          refine ⟨372658389638422279151807567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248438926425614852767871711 372658389638422279151807567)
          ·
            refine ⟨558987584457633418727711351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372658389638422279151807567 558987584457633418727711351)
            ·
              refine ⟨838481376686450128091567027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558987584457633418727711351 838481376686450128091567027)
              ·
                refine ⟨1257722065029675192137350541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838481376686450128091567027 1257722065029675192137350541)
                ·
                  refine ⟨471645774386128197051506453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257722065029675192137350541 471645774386128197051506453)
                  ·
                    refine ⟨22108395674349759236789365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 471645774386128197051506453 22108395674349759236789365)
                    ·
                      refine ⟨2072662094470289928449003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22108395674349759236789365 2072662094470289928449003)
                      ·
                        rfl

theorem cell23_4036495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_4036495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036495 prefixEnd_4036495 := by exact prefixLift 4036495
  have htrace : WordTrace (prefixWord ++ tailWord_4036495) baseStart_4036495 baseEnd_4036495 := by
    simpa [prefixWord, tailWord_4036495, baseEnd_4036495] using wordTrace_append hprefix tailTrace_4036495
  have hstable : (prefixWord ++ tailWord_4036495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036495).length < 2 ^ (prefixWord ++ tailWord_4036495).sum := by decide
  have hdescent : baseEnd_4036495 < baseStart_4036495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036533 : List Nat := [1, 3, 3, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_4036533 : Nat := 118140960795 + 4036533 * 2 ^ 59
def prefixEnd_4036533 : Nat := 4983230072969 + 3 ^ 40 * 4036533 * 2
def baseEnd_4036533 : Nat := 2072681606735160779773829

theorem tailTrace_4036533 : CollatzResearch.WordTrace tailWord_4036533 prefixEnd_4036533 2072681606735160779773829 := by
  unfold tailWord_4036533
  simp only [CollatzResearch.WordTrace]
  refine ⟨147224453485337800796770253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98149635656891867197846835 147224453485337800796770253)
  ·
    refine ⟨55209170057001675298788845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147224453485337800796770253 55209170057001675298788845)
    ·
      refine ⟨20703438771375628237045817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55209170057001675298788845 20703438771375628237045817)
      ·
        refine ⟨15527579078531721177784363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20703438771375628237045817 15527579078531721177784363)
        ·
          refine ⟨23291368617797581766676545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15527579078531721177784363 23291368617797581766676545)
          ·
            refine ⟨17468526463348186325007409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23291368617797581766676545 17468526463348186325007409)
            ·
              refine ⟨13101394847511139743755557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17468526463348186325007409 13101394847511139743755557)
              ·
                refine ⟨2456511533908338701954167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13101394847511139743755557 2456511533908338701954167)
                ·
                  refine ⟨3684767300862508052931251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456511533908338701954167 3684767300862508052931251)
                  ·
                    refine ⟨5527150951293762079396877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3684767300862508052931251 5527150951293762079396877)
                    ·
                      refine ⟨2072681606735160779773829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5527150951293762079396877 2072681606735160779773829)
                      ·
                        rfl

theorem cell23_4036533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_4036533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036533 prefixEnd_4036533 := by exact prefixLift 4036533
  have htrace : WordTrace (prefixWord ++ tailWord_4036533) baseStart_4036533 baseEnd_4036533 := by
    simpa [prefixWord, tailWord_4036533, baseEnd_4036533] using wordTrace_append hprefix tailTrace_4036533
  have hstable : (prefixWord ++ tailWord_4036533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036533).length < 2 ^ (prefixWord ++ tailWord_4036533).sum := by decide
  have hdescent : baseEnd_4036533 < baseStart_4036533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036556 : List Nat := [2, 2, 1, 4, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4036556 : Nat := 118140960795 + 4036556 * 2 ^ 59
def prefixEnd_4036556 : Nat := 4983230072969 + 3 ^ 40 * 4036556 * 2
def baseEnd_4036556 : Nat := 2072693416790214189786223

theorem tailTrace_4036556 : CollatzResearch.WordTrace tailWord_4036556 prefixEnd_4036556 2072693416790214189786223 := by
  unfold tailWord_4036556
  simp only [CollatzResearch.WordTrace]
  refine ⟨73612646182127237862428761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98150194909502983816571681 73612646182127237862428761)
  ·
    refine ⟨55209484636595428396821571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73612646182127237862428761 55209484636595428396821571)
    ·
      refine ⟨82814226954893142595232357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55209484636595428396821571 82814226954893142595232357)
      ·
        refine ⟨15527667554042464236606067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82814226954893142595232357 15527667554042464236606067)
        ·
          refine ⟨23291501331063696354909101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15527667554042464236606067 23291501331063696354909101)
          ·
            refine ⟨8734312999148886133090913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23291501331063696354909101 8734312999148886133090913)
            ·
              refine ⟨6550734749361664599818185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8734312999148886133090913 6550734749361664599818185)
              ·
                refine ⟨4913051062021248449863639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550734749361664599818185 4913051062021248449863639)
                ·
                  refine ⟨7369576593031872674795459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913051062021248449863639 7369576593031872674795459)
                  ·
                    refine ⟨11054364889547809012193189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7369576593031872674795459 11054364889547809012193189)
                    ·
                      refine ⟨2072693416790214189786223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11054364889547809012193189 2072693416790214189786223)
                      ·
                        rfl

theorem cell23_4036556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4036556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036556 prefixEnd_4036556 := by exact prefixLift 4036556
  have htrace : WordTrace (prefixWord ++ tailWord_4036556) baseStart_4036556 baseEnd_4036556 := by
    simpa [prefixWord, tailWord_4036556, baseEnd_4036556] using wordTrace_append hprefix tailTrace_4036556
  have hstable : (prefixWord ++ tailWord_4036556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036556).length < 2 ^ (prefixWord ++ tailWord_4036556).sum := by decide
  have hdescent : baseEnd_4036556 < baseStart_4036556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036590 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_4036590 : Nat := 118140960795 + 4036590 * 2 ^ 59
def prefixEnd_4036590 : Nat := 4983230072969 + 3 ^ 40 * 4036590 * 2
def baseEnd_4036590 : Nat := 2072710875132467056761067

theorem tailTrace_4036590 : CollatzResearch.WordTrace tailWord_4036590 prefixEnd_4036590 2072710875132467056761067 := by
  unfold tailWord_4036590
  simp only [CollatzResearch.WordTrace]
  refine ⟨18403316555766412441449403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98151021630754199687730149 18403316555766412441449403)
  ·
    refine ⟨27604974833649618662174105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18403316555766412441449403 27604974833649618662174105)
    ·
      refine ⟨20703731125237213996630579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27604974833649618662174105 20703731125237213996630579)
      ·
        refine ⟨31055596687855820994945869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20703731125237213996630579 31055596687855820994945869)
        ·
          refine ⟨11645848757945932873104701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31055596687855820994945869 11645848757945932873104701)
          ·
            refine ⟨4367193284229724827414263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11645848757945932873104701 4367193284229724827414263)
            ·
              refine ⟨6550789926344587241121395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367193284229724827414263 6550789926344587241121395)
              ·
                refine ⟨9826184889516880861682093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6550789926344587241121395 9826184889516880861682093)
                ·
                  refine ⟨3684819333568830323130785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9826184889516880861682093 3684819333568830323130785)
                  ·
                    refine ⟨2763614500176622742348089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684819333568830323130785 2763614500176622742348089)
                    ·
                      refine ⟨2072710875132467056761067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763614500176622742348089 2072710875132467056761067)
                      ·
                        rfl

theorem cell23_4036590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_4036590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036590 prefixEnd_4036590 := by exact prefixLift 4036590
  have htrace : WordTrace (prefixWord ++ tailWord_4036590) baseStart_4036590 baseEnd_4036590 := by
    simpa [prefixWord, tailWord_4036590, baseEnd_4036590] using wordTrace_append hprefix tailTrace_4036590
  have hstable : (prefixWord ++ tailWord_4036590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036590).length < 2 ^ (prefixWord ++ tailWord_4036590).sum := by decide
  have hdescent : baseEnd_4036590 < baseStart_4036590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036616 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_4036616 : Nat := 118140960795 + 4036616 * 2 ^ 59
def prefixEnd_4036616 : Nat := 4983230072969 + 3 ^ 40 * 4036616 * 2
def baseEnd_4036616 : Nat := 2072724225629483955035947

theorem tailTrace_4036616 : CollatzResearch.WordTrace tailWord_4036616 prefixEnd_4036616 2072724225629483955035947 := by
  unfold tailWord_4036616
  simp only [CollatzResearch.WordTrace]
  refine ⟨73613740372018552986020851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98151653829358070648027801 73613740372018552986020851)
  ·
    refine ⟨110420610558027829479031277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73613740372018552986020851 110420610558027829479031277)
    ·
      refine ⟨41407728959260436054636729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110420610558027829479031277 41407728959260436054636729)
      ·
        refine ⟨31055796719445327040977547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41407728959260436054636729 31055796719445327040977547)
        ·
          refine ⟨46583695079167990561466321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31055796719445327040977547 46583695079167990561466321)
          ·
            refine ⟨34937771309375992921099741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46583695079167990561466321 34937771309375992921099741)
            ·
              refine ⟨13101664241015997345412403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34937771309375992921099741 13101664241015997345412403)
              ·
                refine ⟨19652496361523996018118605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101664241015997345412403 19652496361523996018118605)
                ·
                  refine ⟨7369686135571498506794477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19652496361523996018118605 7369686135571498506794477)
                  ·
                    refine ⟨2763632300839311940047929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7369686135571498506794477 2763632300839311940047929)
                    ·
                      refine ⟨2072724225629483955035947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763632300839311940047929 2072724225629483955035947)
                      ·
                        rfl

theorem cell23_4036616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_4036616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036616 prefixEnd_4036616 := by exact prefixLift 4036616
  have htrace : WordTrace (prefixWord ++ tailWord_4036616) baseStart_4036616 baseEnd_4036616 := by
    simpa [prefixWord, tailWord_4036616, baseEnd_4036616] using wordTrace_append hprefix tailTrace_4036616
  have hstable : (prefixWord ++ tailWord_4036616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036616).length < 2 ^ (prefixWord ++ tailWord_4036616).sum := by decide
  have hdescent : baseEnd_4036616 < baseStart_4036616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036663 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_4036663 : Nat := 118140960795 + 4036663 * 2 ^ 59
def prefixEnd_4036663 : Nat := 4983230072969 + 3 ^ 40 * 4036663 * 2
def baseEnd_4036663 : Nat := 2072748359220245271148231

theorem tailTrace_4036663 : CollatzResearch.WordTrace tailWord_4036663 prefixEnd_4036663 2072748359220245271148231 := by
  unfold tailWord_4036663
  simp only [CollatzResearch.WordTrace]
  refine ⟨147229194974866832999002643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98152796649911221999335095 147229194974866832999002643)
  ·
    refine ⟨220843792462300249498503965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147229194974866832999002643 220843792462300249498503965)
    ·
      refine ⟨82816422173362593561938987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220843792462300249498503965 82816422173362593561938987)
      ·
        refine ⟨124224633260043890342908481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82816422173362593561938987 124224633260043890342908481)
        ·
          refine ⟨93168474945032917757181361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124224633260043890342908481 93168474945032917757181361)
          ·
            refine ⟨69876356208774688317886021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93168474945032917757181361 69876356208774688317886021)
            ·
              refine ⟨13101816789145254059603629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69876356208774688317886021 13101816789145254059603629)
              ·
                refine ⟨4913181295929470272351361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13101816789145254059603629 4913181295929470272351361)
                ·
                  refine ⟨3684885971947102704263521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4913181295929470272351361 3684885971947102704263521)
                  ·
                    refine ⟨2763664478960327028197641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3684885971947102704263521 2763664478960327028197641)
                    ·
                      refine ⟨2072748359220245271148231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763664478960327028197641 2072748359220245271148231)
                      ·
                        rfl

theorem cell23_4036663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_4036663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036663 prefixEnd_4036663 := by exact prefixLift 4036663
  have htrace : WordTrace (prefixWord ++ tailWord_4036663) baseStart_4036663 baseEnd_4036663 := by
    simpa [prefixWord, tailWord_4036663, baseEnd_4036663] using wordTrace_append hprefix tailTrace_4036663
  have hstable : (prefixWord ++ tailWord_4036663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036663).length < 2 ^ (prefixWord ++ tailWord_4036663).sum := by decide
  have hdescent : baseEnd_4036663 < baseStart_4036663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036669 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 7]
def baseStart_4036669 : Nat := 118140960795 + 4036669 * 2 ^ 59
def prefixEnd_4036669 : Nat := 4983230072969 + 3 ^ 40 * 4036669 * 2
def baseEnd_4036669 : Nat := 230305715567130249741467

theorem tailTrace_4036669 : CollatzResearch.WordTrace tailWord_4036669 prefixEnd_4036669 230305715567130249741467 := by
  unfold tailWord_4036669
  simp only [CollatzResearch.WordTrace]
  refine ⟨147229413812845096023721061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98152942541896730682480707 147229413812845096023721061)
  ·
    refine ⟨27605515089908455504447699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147229413812845096023721061 27605515089908455504447699)
    ·
      refine ⟨41408272634862683256671549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27605515089908455504447699 41408272634862683256671549)
      ·
        refine ⟨15528102238073506221251831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41408272634862683256671549 15528102238073506221251831)
        ·
          refine ⟨23292153357110259331877747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528102238073506221251831 23292153357110259331877747)
          ·
            refine ⟨34938230035665388997816621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23292153357110259331877747 34938230035665388997816621)
            ·
              refine ⟨13101836263374520874181233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34938230035665388997816621 13101836263374520874181233)
              ·
                refine ⟨9826377197530890655635925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13101836263374520874181233 9826377197530890655635925)
                ·
                  refine ⟨230305715567130249741467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9826377197530890655635925 230305715567130249741467)
                  ·
                    rfl

theorem cell23_4036669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_4036669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036669 prefixEnd_4036669 := by exact prefixLift 4036669
  have htrace : WordTrace (prefixWord ++ tailWord_4036669) baseStart_4036669 baseEnd_4036669 := by
    simpa [prefixWord, tailWord_4036669, baseEnd_4036669] using wordTrace_append hprefix tailTrace_4036669
  have hstable : (prefixWord ++ tailWord_4036669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036669).length < 2 ^ (prefixWord ++ tailWord_4036669).sum := by decide
  have hdescent : baseEnd_4036669 < baseStart_4036669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036679 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_4036679 : Nat := 118140960795 + 4036679 * 2 ^ 59
def prefixEnd_4036679 : Nat := 4983230072969 + 3 ^ 40 * 4036679 * 2
def baseEnd_4036679 : Nat := 2072756574910717208548157

theorem tailTrace_4036679 : CollatzResearch.WordTrace tailWord_4036679 prefixEnd_4036679 2072756574910717208548157 := by
  unfold tailWord_4036679
  simp only [CollatzResearch.WordTrace]
  refine ⟨147229778542808867731585091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98153185695205911821056727 147229778542808867731585091)
  ·
    refine ⟨220844667814213301597377637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147229778542808867731585091 220844667814213301597377637)
    ·
      refine ⟨41408375215164994049508307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220844667814213301597377637 41408375215164994049508307)
      ·
        refine ⟨62112562822747491074262461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41408375215164994049508307 62112562822747491074262461)
        ·
          refine ⟨23292211058530309152848423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62112562822747491074262461 23292211058530309152848423)
          ·
            refine ⟨34938316587795463729272635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23292211058530309152848423 34938316587795463729272635)
            ·
              refine ⟨52407474881693195593908953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34938316587795463729272635 52407474881693195593908953)
              ·
                refine ⟨39305606161269896695431715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52407474881693195593908953 39305606161269896695431715)
                ·
                  refine ⟨58958409241904845043147573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39305606161269896695431715 58958409241904845043147573)
                  ·
                    refine ⟨5527350866428579222795085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58958409241904845043147573 5527350866428579222795085)
                    ·
                      refine ⟨2072756574910717208548157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5527350866428579222795085 2072756574910717208548157)
                      ·
                        rfl

theorem cell23_4036679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_4036679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036679 prefixEnd_4036679 := by exact prefixLift 4036679
  have htrace : WordTrace (prefixWord ++ tailWord_4036679) baseStart_4036679 baseEnd_4036679 := by
    simpa [prefixWord, tailWord_4036679, baseEnd_4036679] using wordTrace_append hprefix tailTrace_4036679
  have hstable : (prefixWord ++ tailWord_4036679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036679).length < 2 ^ (prefixWord ++ tailWord_4036679).sum := by decide
  have hdescent : baseEnd_4036679 < baseStart_4036679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036686 : List Nat := [4, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_4036686 : Nat := 118140960795 + 4036686 * 2 ^ 59
def prefixEnd_4036686 : Nat := 4983230072969 + 3 ^ 40 * 4036686 * 2
def baseEnd_4036686 : Nat := 230306685475033186795625

theorem tailTrace_4036686 : CollatzResearch.WordTrace tailWord_4036686 prefixEnd_4036686 230306685475033186795625 := by
  unfold tailWord_4036686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18403754231722938490886239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98153355902522338618059941 18403754231722938490886239)
  ·
    refine ⟨27605631347584407736329359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18403754231722938490886239 27605631347584407736329359)
    ·
      refine ⟨41408447021376611604494039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27605631347584407736329359 41408447021376611604494039)
      ·
        refine ⟨62112670532064917406741059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41408447021376611604494039 62112670532064917406741059)
        ·
          refine ⟨93169005798097376110111589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62112670532064917406741059 93169005798097376110111589)
          ·
            refine ⟨17469188587143258020645923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93169005798097376110111589 17469188587143258020645923)
            ·
              refine ⟨26203782880714887030968885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17469188587143258020645923 26203782880714887030968885)
              ·
                refine ⟨2456604645067020659153333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26203782880714887030968885 2456604645067020659153333)
                ·
                  refine ⟨230306685475033186795625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2456604645067020659153333 230306685475033186795625)
                  ·
                    rfl

theorem cell23_4036686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_4036686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036686 prefixEnd_4036686 := by exact prefixLift 4036686
  have htrace : WordTrace (prefixWord ++ tailWord_4036686) baseStart_4036686 baseEnd_4036686 := by
    simpa [prefixWord, tailWord_4036686, baseEnd_4036686] using wordTrace_append hprefix tailTrace_4036686
  have hstable : (prefixWord ++ tailWord_4036686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036686).length < 2 ^ (prefixWord ++ tailWord_4036686).sum := by decide
  have hdescent : baseEnd_4036686 < baseStart_4036686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036719 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_4036719 : Nat := 118140960795 + 4036719 * 2 ^ 59
def prefixEnd_4036719 : Nat := 4983230072969 + 3 ^ 40 * 4036719 * 2
def baseEnd_4036719 : Nat := 2072777114136897052047973

theorem tailTrace_4036719 : CollatzResearch.WordTrace tailWord_4036719 prefixEnd_4036719 2072777114136897052047973 := by
  unfold tailWord_4036719
  simp only [CollatzResearch.WordTrace]
  refine ⟨147231237462663954563041211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98154158308442636375360807 147231237462663954563041211)
  ·
    refine ⟨220846856193995931844561817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147231237462663954563041211 220846856193995931844561817)
    ·
      refine ⟨165635142145496948883421363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220846856193995931844561817 165635142145496948883421363)
      ·
        refine ⟨248452713218245423325132045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165635142145496948883421363 248452713218245423325132045)
        ·
          refine ⟨93169767456842033746924517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248452713218245423325132045 93169767456842033746924517)
          ·
            refine ⟨17469331398157881327548347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93169767456842033746924517 17469331398157881327548347)
            ·
              refine ⟨26203997097236821991322521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17469331398157881327548347 26203997097236821991322521)
              ·
                refine ⟨19652997822927616493491891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26203997097236821991322521 19652997822927616493491891)
                ·
                  refine ⟨29479496734391424740237837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19652997822927616493491891 29479496734391424740237837)
                  ·
                    refine ⟨11054811275396784277589189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29479496734391424740237837 11054811275396784277589189)
                    ·
                      refine ⟨2072777114136897052047973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11054811275396784277589189 2072777114136897052047973)
                      ·
                        rfl

theorem cell23_4036719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_4036719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036719 prefixEnd_4036719 := by exact prefixLift 4036719
  have htrace : WordTrace (prefixWord ++ tailWord_4036719) baseStart_4036719 baseEnd_4036719 := by
    simpa [prefixWord, tailWord_4036719, baseEnd_4036719] using wordTrace_append hprefix tailTrace_4036719
  have hstable : (prefixWord ++ tailWord_4036719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036719).length < 2 ^ (prefixWord ++ tailWord_4036719).sum := by decide
  have hdescent : baseEnd_4036719 < baseStart_4036719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036826 : List Nat := [3, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4]
def baseStart_4036826 : Nat := 118140960795 + 4036826 * 2 ^ 59
def prefixEnd_4036826 : Nat := 4983230072969 + 3 ^ 40 * 4036826 * 2
def baseEnd_4036826 : Nat := 2072832056566928133409981

theorem tailTrace_4036826 : CollatzResearch.WordTrace tailWord_4036826 prefixEnd_4036826 2072832056566928133409981 := by
  unfold tailWord_4036826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36808785018319077959296583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98156760048850874558124221 36808785018319077959296583)
  ·
    refine ⟨55213177527478616938944875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36808785018319077959296583 55213177527478616938944875)
    ·
      refine ⟨82819766291217925408417313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55213177527478616938944875 82819766291217925408417313)
      ·
        refine ⟨62114824718413444056312985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82819766291217925408417313 62114824718413444056312985)
        ·
          refine ⟨46586118538810083042234739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62114824718413444056312985 46586118538810083042234739)
          ·
            refine ⟨69879177808215124563352109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46586118538810083042234739 69879177808215124563352109)
            ·
              refine ⟨26204691678080671711257041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69879177808215124563352109 26204691678080671711257041)
              ·
                refine ⟨19653518758560503783442781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26204691678080671711257041 19653518758560503783442781)
                ·
                  refine ⟨7370069534460188918791043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19653518758560503783442781 7370069534460188918791043)
                  ·
                    refine ⟨11055104301690283378186565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7370069534460188918791043 11055104301690283378186565)
                    ·
                      refine ⟨2072832056566928133409981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11055104301690283378186565 2072832056566928133409981)
                      ·
                        rfl

theorem cell23_4036826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_4036826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036826 prefixEnd_4036826 := by exact prefixLift 4036826
  have htrace : WordTrace (prefixWord ++ tailWord_4036826) baseStart_4036826 baseEnd_4036826 := by
    simpa [prefixWord, tailWord_4036826, baseEnd_4036826] using wordTrace_append hprefix tailTrace_4036826
  have hstable : (prefixWord ++ tailWord_4036826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036826).length < 2 ^ (prefixWord ++ tailWord_4036826).sum := by decide
  have hdescent : baseEnd_4036826 < baseStart_4036826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036836 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_4036836 : Nat := 118140960795 + 4036836 * 2 ^ 59
def prefixEnd_4036836 : Nat := 4983230072969 + 3 ^ 40 * 4036836 * 2
def baseEnd_4036836 : Nat := 690945730457824364761645

theorem tailTrace_4036836 : CollatzResearch.WordTrace tailWord_4036836 prefixEnd_4036836 690945730457824364761645 := by
  unfold tailWord_4036836
  simp only [CollatzResearch.WordTrace]
  refine ⟨73617752401620041772525181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98157003202160055696700241 73617752401620041772525181)
  ·
    refine ⟨27606657150607515664696943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73617752401620041772525181 27606657150607515664696943)
    ·
      refine ⟨41409985725911273497045415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27606657150607515664696943 41409985725911273497045415)
      ·
        refine ⟨62114978588866910245568123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41409985725911273497045415 62114978588866910245568123)
        ·
          refine ⟨93172467883300365368352185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62114978588866910245568123 93172467883300365368352185)
          ·
            refine ⟨69879350912475274026264139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93172467883300365368352185 69879350912475274026264139)
            ·
              refine ⟨104819026368712911039396209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69879350912475274026264139 104819026368712911039396209)
              ·
                refine ⟨78614269776534683279547157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104819026368712911039396209 78614269776534683279547157)
                ·
                  refine ⟨3685043895775063278728773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 78614269776534683279547157 3685043895775063278728773)
                  ·
                    refine ⟨690945730457824364761645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685043895775063278728773 690945730457824364761645)
                    ·
                      rfl

theorem cell23_4036836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_4036836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036836 prefixEnd_4036836 := by exact prefixLift 4036836
  have htrace : WordTrace (prefixWord ++ tailWord_4036836) baseStart_4036836 baseEnd_4036836 := by
    simpa [prefixWord, tailWord_4036836, baseEnd_4036836] using wordTrace_append hprefix tailTrace_4036836
  have hstable : (prefixWord ++ tailWord_4036836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036836).length < 2 ^ (prefixWord ++ tailWord_4036836).sum := by decide
  have hdescent : baseEnd_4036836 < baseStart_4036836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036849 : List Nat := [1, 2, 2, 2, 2, 1, 2, 11]
def baseStart_4036849 : Nat := 118140960795 + 4036849 * 2 ^ 59
def prefixEnd_4036849 : Nat := 4983230072969 + 3 ^ 40 * 4036849 * 2
def baseEnd_4036849 : Nat := 76771995060073390497125

theorem tailTrace_4036849 : CollatzResearch.WordTrace tailWord_4036849 prefixEnd_4036849 76771995060073390497125 := by
  unfold tailWord_4036849
  simp only [CollatzResearch.WordTrace]
  refine ⟨147235978952192986765273601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98157319301461991176849067 147235978952192986765273601)
  ·
    refine ⟨110426984214144740073955201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147235978952192986765273601 110426984214144740073955201)
    ·
      refine ⟨82820238160608555055466401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110426984214144740073955201 82820238160608555055466401)
      ·
        refine ⟨62115178620456416291599801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82820238160608555055466401 62115178620456416291599801)
        ·
          refine ⟨46586383965342312218699851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62115178620456416291599801 46586383965342312218699851)
          ·
            refine ⟨69879575948013468328049777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46586383965342312218699851 69879575948013468328049777)
            ·
              refine ⟨52409681961010101246037333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69879575948013468328049777 52409681961010101246037333)
              ·
                refine ⟨76771995060073390497125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 52409681961010101246037333 76771995060073390497125)
                ·
                  rfl

theorem cell23_4036849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 11].length) (baseStart_4036849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036849 prefixEnd_4036849 := by exact prefixLift 4036849
  have htrace : WordTrace (prefixWord ++ tailWord_4036849) baseStart_4036849 baseEnd_4036849 := by
    simpa [prefixWord, tailWord_4036849, baseEnd_4036849] using wordTrace_append hprefix tailTrace_4036849
  have hstable : (prefixWord ++ tailWord_4036849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036849).length < 2 ^ (prefixWord ++ tailWord_4036849).sum := by decide
  have hdescent : baseEnd_4036849 < baseStart_4036849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036860 : List Nat := [2, 2, 2, 1, 4, 1, 4, 1, 1, 1, 4]
def baseStart_4036860 : Nat := 118140960795 + 4036860 * 2 ^ 59
def prefixEnd_4036860 : Nat := 4983230072969 + 3 ^ 40 * 4036860 * 2
def baseEnd_4036860 : Nat := 2072849514909181000384825

theorem tailTrace_4036860 : CollatzResearch.WordTrace tailWord_4036860 prefixEnd_4036860 2072849514909181000384825 := by
  unfold tailWord_4036860
  simp only [CollatzResearch.WordTrace]
  refine ⟨73618190077576567821962017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98157586770102090429282689 73618190077576567821962017)
  ·
    refine ⟨55213642558182425866471513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73618190077576567821962017 55213642558182425866471513)
    ·
      refine ⟨41410231918636819399853635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55213642558182425866471513 41410231918636819399853635)
      ·
        refine ⟨62115347877955229099780453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41410231918636819399853635 62115347877955229099780453)
        ·
          refine ⟨11646627727116605456208835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62115347877955229099780453 11646627727116605456208835)
          ·
            refine ⟨17469941590674908184313253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11646627727116605456208835 17469941590674908184313253)
            ·
              refine ⟨3275614048251545284558735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17469941590674908184313253 3275614048251545284558735)
              ·
                refine ⟨4913421072377317926838103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275614048251545284558735 4913421072377317926838103)
                ·
                  refine ⟨7370131608565976890257155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913421072377317926838103 7370131608565976890257155)
                  ·
                    refine ⟨11055197412848965335385733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7370131608565976890257155 11055197412848965335385733)
                    ·
                      refine ⟨2072849514909181000384825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11055197412848965335385733 2072849514909181000384825)
                      ·
                        rfl

theorem cell23_4036860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 1, 1, 1, 4].length) (baseStart_4036860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036860 prefixEnd_4036860 := by exact prefixLift 4036860
  have htrace : WordTrace (prefixWord ++ tailWord_4036860) baseStart_4036860 baseEnd_4036860 := by
    simpa [prefixWord, tailWord_4036860, baseEnd_4036860] using wordTrace_append hprefix tailTrace_4036860
  have hstable : (prefixWord ++ tailWord_4036860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036860).length < 2 ^ (prefixWord ++ tailWord_4036860).sum := by decide
  have hdescent : baseEnd_4036860 < baseStart_4036860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036863 : List Nat := [1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 3]
def baseStart_4036863 : Nat := 118140960795 + 4036863 * 2 ^ 59
def prefixEnd_4036863 : Nat := 4983230072969 + 3 ^ 40 * 4036863 * 2
def baseEnd_4036863 : Nat := 2072851055351144488647311

theorem tailTrace_4036863 : CollatzResearch.WordTrace tailWord_4036863 prefixEnd_4036863 2072851055351144488647311 := by
  unfold tailWord_4036863
  simp only [CollatzResearch.WordTrace]
  refine ⟨147236489574142267156283243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98157659716094844770855495 147236489574142267156283243)
  ·
    refine ⟨220854734361213400734424865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147236489574142267156283243 220854734361213400734424865)
    ·
      refine ⟨165641050770910050550818649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220854734361213400734424865 165641050770910050550818649)
      ·
        refine ⟨124230788078182537913113987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165641050770910050550818649 124230788078182537913113987)
        ·
          refine ⟨186346182117273806869670981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124230788078182537913113987 186346182117273806869670981)
          ·
            refine ⟨34939909146988838788063309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186346182117273806869670981 34939909146988838788063309)
            ·
              refine ⟨13102465930120814545523741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34939909146988838788063309 13102465930120814545523741)
              ·
                refine ⟨4913424723795305454571403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13102465930120814545523741 4913424723795305454571403)
                ·
                  refine ⟨7370137085692958181857105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913424723795305454571403 7370137085692958181857105)
                  ·
                    refine ⟨5527602814269718636392829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7370137085692958181857105 5527602814269718636392829)
                    ·
                      refine ⟨2072851055351144488647311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5527602814269718636392829 2072851055351144488647311)
                      ·
                        rfl

theorem cell23_4036863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_4036863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036863 prefixEnd_4036863 := by exact prefixLift 4036863
  have htrace : WordTrace (prefixWord ++ tailWord_4036863) baseStart_4036863 baseEnd_4036863 := by
    simpa [prefixWord, tailWord_4036863, baseEnd_4036863] using wordTrace_append hprefix tailTrace_4036863
  have hstable : (prefixWord ++ tailWord_4036863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036863).length < 2 ^ (prefixWord ++ tailWord_4036863).sum := by decide
  have hdescent : baseEnd_4036863 < baseStart_4036863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036879 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 1, 9]
def baseStart_4036879 : Nat := 118140960795 + 4036879 * 2 ^ 59
def prefixEnd_4036879 : Nat := 4983230072969 + 3 ^ 40 * 4036879 * 2
def baseEnd_4036879 : Nat := 690953090347205475349079

theorem tailTrace_4036879 : CollatzResearch.WordTrace tailWord_4036879 prefixEnd_4036879 690953090347205475349079 := by
  unfold tailWord_4036879
  simp only [CollatzResearch.WordTrace]
  refine ⟨147237073142084301888865691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98158048761389534592577127 147237073142084301888865691)
  ·
    refine ⟨220855609713126452833298537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147237073142084301888865691 220855609713126452833298537)
    ·
      refine ⟨165641707284844839624973903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220855609713126452833298537 165641707284844839624973903)
      ·
        refine ⟨248462560927267259437460855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165641707284844839624973903 248462560927267259437460855)
        ·
          refine ⟨372693841390900889156191283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248462560927267259437460855 372693841390900889156191283)
          ·
            refine ⟨559040762086351333734286925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372693841390900889156191283 559040762086351333734286925)
            ·
              refine ⟨209640285782381750150357597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559040762086351333734286925 209640285782381750150357597)
              ·
                refine ⟨78615107168393156306384099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209640285782381750150357597 78615107168393156306384099)
                ·
                  refine ⟨117922660752589734459576149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78615107168393156306384099 117922660752589734459576149)
                  ·
                    refine ⟨690953090347205475349079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 117922660752589734459576149 690953090347205475349079)
                    ·
                      rfl

theorem cell23_4036879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_4036879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036879 prefixEnd_4036879 := by exact prefixLift 4036879
  have htrace : WordTrace (prefixWord ++ tailWord_4036879) baseStart_4036879 baseEnd_4036879 := by
    simpa [prefixWord, tailWord_4036879, baseEnd_4036879] using wordTrace_append hprefix tailTrace_4036879
  have hstable : (prefixWord ++ tailWord_4036879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036879).length < 2 ^ (prefixWord ++ tailWord_4036879).sum := by decide
  have hdescent : baseEnd_4036879 < baseStart_4036879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036890 : List Nat := [3, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4]
def baseStart_4036890 : Nat := 118140960795 + 4036890 * 2 ^ 59
def prefixEnd_4036890 : Nat := 4983230072969 + 3 ^ 40 * 4036890 * 2
def baseEnd_4036890 : Nat := 2072864919328815883009687

theorem tailTrace_4036890 : CollatzResearch.WordTrace tailWord_4036890 prefixEnd_4036890 2072864919328815883009687 := by
  unfold tailWord_4036890
  simp only [CollatzResearch.WordTrace]
  refine ⟨36809368586261112691879031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98158316230029633845010749 36809368586261112691879031)
  ·
    refine ⟨55214052879391669037818547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36809368586261112691879031 55214052879391669037818547)
    ·
      refine ⟨82821079319087503556727821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55214052879391669037818547 82821079319087503556727821)
      ·
        refine ⟨31057904744657813833772933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82821079319087503556727821 31057904744657813833772933)
        ·
          refine ⟨5823357139623340093832425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31057904744657813833772933 5823357139623340093832425)
          ·
            refine ⟨4367517854717505070374319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5823357139623340093832425 4367517854717505070374319)
            ·
              refine ⟨6551276782076257605561479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4367517854717505070374319 6551276782076257605561479)
              ·
                refine ⟨9826915173114386408342219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551276782076257605561479 9826915173114386408342219)
                ·
                  refine ⟨14740372759671579612513329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9826915173114386408342219 14740372759671579612513329)
                  ·
                    refine ⟨11055279569753684709384997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14740372759671579612513329 11055279569753684709384997)
                    ·
                      refine ⟨2072864919328815883009687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11055279569753684709384997 2072864919328815883009687)
                      ·
                        rfl

theorem cell23_4036890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_4036890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036890 prefixEnd_4036890 := by exact prefixLift 4036890
  have htrace : WordTrace (prefixWord ++ tailWord_4036890) baseStart_4036890 baseEnd_4036890 := by
    simpa [prefixWord, tailWord_4036890, baseEnd_4036890] using wordTrace_append hprefix tailTrace_4036890
  have hstable : (prefixWord ++ tailWord_4036890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036890).length < 2 ^ (prefixWord ++ tailWord_4036890).sum := by decide
  have hdescent : baseEnd_4036890 < baseStart_4036890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036894 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4036894 : Nat := 118140960795 + 4036894 * 2 ^ 59
def prefixEnd_4036894 : Nat := 4983230072969 + 3 ^ 40 * 4036894 * 2
def baseEnd_4036894 : Nat := 2072866973251433867359669

theorem tailTrace_4036894 : CollatzResearch.WordTrace tailWord_4036894 prefixEnd_4036894 2072866973251433867359669 := by
  unfold tailWord_4036894
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404702529628744931332717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98158413491353306300441157 18404702529628744931332717)
  ·
    refine ⟨6901763448610779349249769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18404702529628744931332717 6901763448610779349249769)
    ·
      refine ⟨5176322586458084511937327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6901763448610779349249769 5176322586458084511937327)
      ·
        refine ⟨7764483879687126767905991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5176322586458084511937327 7764483879687126767905991)
        ·
          refine ⟨11646725819530690151858987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764483879687126767905991 11646725819530690151858987)
          ·
            refine ⟨17470088729296035227788481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11646725819530690151858987 17470088729296035227788481)
            ·
              refine ⟨13102566546972026420841361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17470088729296035227788481 13102566546972026420841361)
              ·
                refine ⟨9826924910229019815631021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13102566546972026420841361 9826924910229019815631021)
                ·
                  refine ⟨3685096841335882430861633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9826924910229019815631021 3685096841335882430861633)
                  ·
                    refine ⟨2763822631001911823146225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3685096841335882430861633 2763822631001911823146225)
                    ·
                      refine ⟨2072866973251433867359669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763822631001911823146225 2072866973251433867359669)
                      ·
                        rfl

theorem cell23_4036894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4036894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036894 prefixEnd_4036894 := by exact prefixLift 4036894
  have htrace : WordTrace (prefixWord ++ tailWord_4036894) baseStart_4036894 baseEnd_4036894 := by
    simpa [prefixWord, tailWord_4036894, baseEnd_4036894] using wordTrace_append hprefix tailTrace_4036894
  have hstable : (prefixWord ++ tailWord_4036894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036894).length < 2 ^ (prefixWord ++ tailWord_4036894).sum := by decide
  have hdescent : baseEnd_4036894 < baseStart_4036894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4036920 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_4036920 : Nat := 118140960795 + 4036920 * 2 ^ 59
def prefixEnd_4036920 : Nat := 4983230072969 + 3 ^ 40 * 4036920 * 2
def baseEnd_4036920 : Nat := 2072880323748450765634549

theorem tailTrace_4036920 : CollatzResearch.WordTrace tailWord_4036920 prefixEnd_4036920 2072880323748450765634549 := by
  unfold tailWord_4036920
  simp only [CollatzResearch.WordTrace]
  refine ⟨73619284267467882945554107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98159045689957177260738809 73619284267467882945554107)
  ·
    refine ⟨110428926401201824418331161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73619284267467882945554107 110428926401201824418331161)
    ·
      refine ⟨82821694800901368313748371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110428926401201824418331161 82821694800901368313748371)
      ·
        refine ⟨124232542201352052470622557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82821694800901368313748371 124232542201352052470622557)
        ·
          refine ⟨46587203325507019676483459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124232542201352052470622557 46587203325507019676483459)
          ·
            refine ⟨69880804988260529514725189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46587203325507019676483459 69880804988260529514725189)
            ·
              refine ⟨13102650935298849284010973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69880804988260529514725189 13102650935298849284010973)
              ·
                refine ⟨4913494100737068481504115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13102650935298849284010973 4913494100737068481504115)
                ·
                  refine ⟨7370241151105602722256173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913494100737068481504115 7370241151105602722256173)
                  ·
                    refine ⟨2763840431664601020846065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7370241151105602722256173 2763840431664601020846065)
                    ·
                      refine ⟨2072880323748450765634549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763840431664601020846065 2072880323748450765634549)
                      ·
                        rfl

theorem cell23_4036920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_4036920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4036920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4036920 prefixEnd_4036920 := by exact prefixLift 4036920
  have htrace : WordTrace (prefixWord ++ tailWord_4036920) baseStart_4036920 baseEnd_4036920 := by
    simpa [prefixWord, tailWord_4036920, baseEnd_4036920] using wordTrace_append hprefix tailTrace_4036920
  have hstable : (prefixWord ++ tailWord_4036920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4036920).length < 2 ^ (prefixWord ++ tailWord_4036920).sum := by decide
  have hdescent : baseEnd_4036920 < baseStart_4036920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4036920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037023 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4037023 : Nat := 118140960795 + 4037023 * 2 ^ 59
def prefixEnd_4037023 : Nat := 4983230072969 + 3 ^ 40 * 4037023 * 2
def baseEnd_4037023 : Nat := 2072933212255863862646575

theorem tailTrace_4037023 : CollatzResearch.WordTrace tailWord_4037023 prefixEnd_4037023 2072933212255863862646575 := by
  unfold tailWord_4037023
  simp only [CollatzResearch.WordTrace]
  refine ⟨147242325253562614482107723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98161550169041742988071815 147242325253562614482107723)
  ·
    refine ⟨220863487880343921723161585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147242325253562614482107723 220863487880343921723161585)
    ·
      refine ⟨165647615910257941292371189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220863487880343921723161585 165647615910257941292371189)
      ·
        refine ⟨15529463991586681996159799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165647615910257941292371189 15529463991586681996159799)
        ·
          refine ⟨23294195987380022994239699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15529463991586681996159799 23294195987380022994239699)
          ·
            refine ⟨34941293981070034491359549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23294195987380022994239699 34941293981070034491359549)
            ·
              refine ⟨13102985242901262934259831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34941293981070034491359549 13102985242901262934259831)
              ·
                refine ⟨19654477864351894401389747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13102985242901262934259831 19654477864351894401389747)
                ·
                  refine ⟨29481716796527841602084621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19654477864351894401389747 29481716796527841602084621)
                  ·
                    refine ⟨11055643798697940600781733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29481716796527841602084621 11055643798697940600781733)
                    ·
                      refine ⟨2072933212255863862646575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11055643798697940600781733 2072933212255863862646575)
                      ·
                        rfl

theorem cell23_4037023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4037023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037023 prefixEnd_4037023 := by exact prefixLift 4037023
  have htrace : WordTrace (prefixWord ++ tailWord_4037023) baseStart_4037023 baseEnd_4037023 := by
    simpa [prefixWord, tailWord_4037023, baseEnd_4037023] using wordTrace_append hprefix tailTrace_4037023
  have hstable : (prefixWord ++ tailWord_4037023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037023).length < 2 ^ (prefixWord ++ tailWord_4037023).sum := by decide
  have hdescent : baseEnd_4037023 < baseStart_4037023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037101 : List Nat := [1, 5, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_4037101 : Nat := 118140960795 + 4037101 * 2 ^ 59
def prefixEnd_4037101 : Nat := 4983230072969 + 3 ^ 40 * 4037101 * 2
def baseEnd_4037101 : Nat := 690991087915638185823739

theorem tailTrace_4037101 : CollatzResearch.WordTrace tailWord_4037101 prefixEnd_4037101 690991087915638185823739 := by
  unfold tailWord_4037101
  simp only [CollatzResearch.WordTrace]
  refine ⟨147245170147280033803447157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98163446764853355868964771 147245170147280033803447157)
  ·
    refine ⟨13804234701307503169073171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147245170147280033803447157 13804234701307503169073171)
    ·
      refine ⟨20706352051961254753609757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13804234701307503169073171 20706352051961254753609757)
      ·
        refine ⟨7764882019485470532603659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20706352051961254753609757 7764882019485470532603659)
        ·
          refine ⟨11647323029228205798905489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764882019485470532603659 11647323029228205798905489)
          ·
            refine ⟨8735492271921154349179117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11647323029228205798905489 8735492271921154349179117)
            ·
              refine ⟨3275809601970432880942169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8735492271921154349179117 3275809601970432880942169)
              ·
                refine ⟨2456857201477824660706627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3275809601970432880942169 2456857201477824660706627)
                ·
                  refine ⟨3685285802216736991059941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2456857201477824660706627 3685285802216736991059941)
                  ·
                    refine ⟨690991087915638185823739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685285802216736991059941 690991087915638185823739)
                    ·
                      rfl

theorem cell23_4037101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_4037101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037101 prefixEnd_4037101 := by exact prefixLift 4037101
  have htrace : WordTrace (prefixWord ++ tailWord_4037101) baseStart_4037101 baseEnd_4037101 := by
    simpa [prefixWord, tailWord_4037101, baseEnd_4037101] using wordTrace_append hprefix tailTrace_4037101
  have hstable : (prefixWord ++ tailWord_4037101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037101).length < 2 ^ (prefixWord ++ tailWord_4037101).sum := by decide
  have hdescent : baseEnd_4037101 < baseStart_4037101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037110 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_4037110 : Nat := 118140960795 + 4037110 * 2 ^ 59
def prefixEnd_4037110 : Nat := 4983230072969 + 3 ^ 40 * 4037110 * 2
def baseEnd_4037110 : Nat := 690992628357601674086225

theorem tailTrace_4037110 : CollatzResearch.WordTrace tailWord_4037110 prefixEnd_4037110 690992628357601674086225 := by
  unfold tailWord_4037110
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202843650265464271282799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98163665602831618893683189 9202843650265464271282799)
  ·
    refine ⟨13804265475398196406924199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9202843650265464271282799 13804265475398196406924199)
    ·
      refine ⟨20706398213097294610386299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13804265475398196406924199 20706398213097294610386299)
      ·
        refine ⟨31059597319645941915579449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20706398213097294610386299 31059597319645941915579449)
        ·
          refine ⟨23294697989734456436684587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31059597319645941915579449 23294697989734456436684587)
          ·
            refine ⟨34942046984601684655026881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23294697989734456436684587 34942046984601684655026881)
            ·
              refine ⟨26206535238451263491270161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34942046984601684655026881 26206535238451263491270161)
              ·
                refine ⟨19654901428838447618452621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26206535238451263491270161 19654901428838447618452621)
                ·
                  refine ⟨7370588035814417856919733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19654901428838447618452621 7370588035814417856919733)
                  ·
                    refine ⟨690992628357601674086225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7370588035814417856919733 690992628357601674086225)
                    ·
                      rfl

theorem cell23_4037110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_4037110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037110 prefixEnd_4037110 := by exact prefixLift 4037110
  have htrace : WordTrace (prefixWord ++ tailWord_4037110) baseStart_4037110 baseEnd_4037110 := by
    simpa [prefixWord, tailWord_4037110, baseEnd_4037110] using wordTrace_append hprefix tailTrace_4037110
  have hstable : (prefixWord ++ tailWord_4037110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037110).length < 2 ^ (prefixWord ++ tailWord_4037110).sum := by decide
  have hdescent : baseEnd_4037110 < baseStart_4037110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037123 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 1, 6]
def baseStart_4037123 : Nat := 118140960795 + 4037123 * 2 ^ 59
def prefixEnd_4037123 : Nat := 4983230072969 + 3 ^ 40 * 4037123 * 2
def baseEnd_4037123 : Nat := 690994853440437823798705

theorem tailTrace_4037123 : CollatzResearch.WordTrace tailWord_4037123 prefixEnd_4037123 690994853440437823798705 := by
  unfold tailWord_4037123
  simp only [CollatzResearch.WordTrace]
  refine ⟨147245972553200331560748023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98163981702133554373832015 147245972553200331560748023)
  ·
    refine ⟨220868958829800497341122035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147245972553200331560748023 220868958829800497341122035)
    ·
      refine ⟨331303438244700746011683053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220868958829800497341122035 331303438244700746011683053)
      ·
        refine ⟨124238789341762779754381145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331303438244700746011683053 124238789341762779754381145)
        ·
          refine ⟨93179092006322084815785859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124238789341762779754381145 93179092006322084815785859)
          ·
            refine ⟨139768638009483127223678789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93179092006322084815785859 139768638009483127223678789)
            ·
              refine ⟨26206619626778086354439773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139768638009483127223678789 26206619626778086354439773)
              ·
                refine ⟨9827482360041782382914915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26206619626778086354439773 9827482360041782382914915)
                ·
                  refine ⟨14741223540062673574372373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827482360041782382914915 14741223540062673574372373)
                  ·
                    refine ⟨690994853440437823798705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14741223540062673574372373 690994853440437823798705)
                    ·
                      rfl

theorem cell23_4037123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 6].length) (baseStart_4037123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037123 prefixEnd_4037123 := by exact prefixLift 4037123
  have htrace : WordTrace (prefixWord ++ tailWord_4037123) baseStart_4037123 baseEnd_4037123 := by
    simpa [prefixWord, tailWord_4037123, baseEnd_4037123] using wordTrace_append hprefix tailTrace_4037123
  have hstable : (prefixWord ++ tailWord_4037123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037123).length < 2 ^ (prefixWord ++ tailWord_4037123).sum := by decide
  have hdescent : baseEnd_4037123 < baseStart_4037123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037130 : List Nat := [3, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4037130 : Nat := 118140960795 + 4037130 * 2 ^ 59
def prefixEnd_4037130 : Nat := 4983230072969 + 3 ^ 40 * 4037130 * 2
def baseEnd_4037130 : Nat := 2072988154685894944008583

theorem tailTrace_4037130 : CollatzResearch.WordTrace tailWord_4037130 prefixEnd_4037130 2072988154685894944008583 := by
  unfold tailWord_4037130
  simp only [CollatzResearch.WordTrace]
  refine ⟨36811556966043742939063211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98164151909449981170835229 36811556966043742939063211)
  ·
    refine ⟨55217335449065614408594817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36811556966043742939063211 55217335449065614408594817)
    ·
      refine ⟨41413001586799210806446113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55217335449065614408594817 41413001586799210806446113)
      ·
        refine ⟨31059751190099408104834585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41413001586799210806446113 31059751190099408104834585)
        ·
          refine ⟨23294813392574556078625939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31059751190099408104834585 23294813392574556078625939)
          ·
            refine ⟨34942220088861834117938909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23294813392574556078625939 34942220088861834117938909)
            ·
              refine ⟨13103332533323187794227091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34942220088861834117938909 13103332533323187794227091)
              ·
                refine ⟨19654998799984781691340637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13103332533323187794227091 19654998799984781691340637)
                ·
                  refine ⟨7370624549994293134252739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19654998799984781691340637 7370624549994293134252739)
                  ·
                    refine ⟨11055936824991439701379109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7370624549994293134252739 11055936824991439701379109)
                    ·
                      refine ⟨2072988154685894944008583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11055936824991439701379109 2072988154685894944008583)
                      ·
                        rfl

theorem cell23_4037130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4037130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037130 prefixEnd_4037130 := by exact prefixLift 4037130
  have htrace : WordTrace (prefixWord ++ tailWord_4037130) baseStart_4037130 baseEnd_4037130 := by
    simpa [prefixWord, tailWord_4037130, baseEnd_4037130] using wordTrace_append hprefix tailTrace_4037130
  have hstable : (prefixWord ++ tailWord_4037130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037130).length < 2 ^ (prefixWord ++ tailWord_4037130).sum := by decide
  have hdescent : baseEnd_4037130 < baseStart_4037130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037134 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2]
def baseStart_4037134 : Nat := 118140960795 + 4037134 * 2 ^ 59
def prefixEnd_4037134 : Nat := 4983230072969 + 3 ^ 40 * 4037134 * 2
def baseEnd_4037134 : Nat := 2072990208608512928358565

theorem tailTrace_4037134 : CollatzResearch.WordTrace tailWord_4037134 prefixEnd_4037134 2072990208608512928358565 := by
  unfold tailWord_4037134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405796719520060054924807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98164249170773653626265637 18405796719520060054924807)
  ·
    refine ⟨27608695079280090082387211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18405796719520060054924807 27608695079280090082387211)
    ·
      refine ⟨41413042618920135123580817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27608695079280090082387211 41413042618920135123580817)
      ·
        refine ⟨31059781964190101342685613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41413042618920135123580817 31059781964190101342685613)
        ·
          refine ⟨11647418236571288003507105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31059781964190101342685613 11647418236571288003507105)
          ·
            refine ⟨8735563677428466002630329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11647418236571288003507105 8735563677428466002630329)
            ·
              refine ⟨6551672758071349501972747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735563677428466002630329 6551672758071349501972747)
              ·
                refine ⟨9827509137107024252959121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551672758071349501972747 9827509137107024252959121)
                ·
                  refine ⟨7370631852830268189719341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827509137107024252959121 7370631852830268189719341)
                  ·
                    refine ⟨2763986944811350571144753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7370631852830268189719341 2763986944811350571144753)
                    ·
                      refine ⟨2072990208608512928358565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2763986944811350571144753 2072990208608512928358565)
                      ·
                        rfl

theorem cell23_4037134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_4037134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037134 prefixEnd_4037134 := by exact prefixLift 4037134
  have htrace : WordTrace (prefixWord ++ tailWord_4037134) baseStart_4037134 baseEnd_4037134 := by
    simpa [prefixWord, tailWord_4037134, baseEnd_4037134] using wordTrace_append hprefix tailTrace_4037134
  have hstable : (prefixWord ++ tailWord_4037134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037134).length < 2 ^ (prefixWord ++ tailWord_4037134).sum := by decide
  have hdescent : baseEnd_4037134 < baseStart_4037134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037174 : List Nat := [5, 1, 2, 1, 2, 1, 2, 3, 2, 4]
def baseStart_4037174 : Nat := 118140960795 + 4037174 * 2 ^ 59
def prefixEnd_4037174 : Nat := 4983230072969 + 3 ^ 40 * 4037174 * 2
def baseEnd_4037174 : Nat := 691003582611564257286127

theorem tailTrace_4037174 : CollatzResearch.WordTrace tailWord_4037174 prefixEnd_4037174 691003582611564257286127 := by
  unfold tailWord_4037174
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202989542250972954428411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98165221784010378180569717 9202989542250972954428411)
  ·
    refine ⟨13804484313376459431642617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9202989542250972954428411 13804484313376459431642617)
    ·
      refine ⟨10353363235032344573731963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13804484313376459431642617 10353363235032344573731963)
      ·
        refine ⟨15530044852548516860597945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10353363235032344573731963 15530044852548516860597945)
        ·
          refine ⟨11647533639411387645448459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15530044852548516860597945 11647533639411387645448459)
          ·
            refine ⟨17471300459117081468172689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647533639411387645448459 17471300459117081468172689)
            ·
              refine ⟨13103475344337811101129517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17471300459117081468172689 13103475344337811101129517)
              ·
                refine ⟨4913803254126679162923569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13103475344337811101129517 4913803254126679162923569)
                ·
                  refine ⟨3685352440595009372192677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4913803254126679162923569 3685352440595009372192677)
                  ·
                    refine ⟨691003582611564257286127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685352440595009372192677 691003582611564257286127)
                    ·
                      rfl

theorem cell23_4037174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 2, 4].length) (baseStart_4037174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037174 prefixEnd_4037174 := by exact prefixLift 4037174
  have htrace : WordTrace (prefixWord ++ tailWord_4037174) baseStart_4037174 baseEnd_4037174 := by
    simpa [prefixWord, tailWord_4037174, baseEnd_4037174] using wordTrace_append hprefix tailTrace_4037174
  have hstable : (prefixWord ++ tailWord_4037174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037174).length < 2 ^ (prefixWord ++ tailWord_4037174).sum := by decide
  have hdescent : baseEnd_4037174 < baseStart_4037174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037183 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 2, 7]
def baseStart_4037183 : Nat := 118140960795 + 4037183 * 2 ^ 59
def prefixEnd_4037183 : Nat := 4983230072969 + 3 ^ 40 * 4037183 * 2
def baseEnd_4037183 : Nat := 691005123053527745548613

theorem tailTrace_4037183 : CollatzResearch.WordTrace tailWord_4037183 prefixEnd_4037183 691005123053527745548613 := by
  unfold tailWord_4037183
  simp only [CollatzResearch.WordTrace]
  refine ⟨147248160932982961807932203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98165440621988641205288135 147248160932982961807932203)
  ·
    refine ⟨220872241399474442711898305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147248160932982961807932203 220872241399474442711898305)
    ·
      refine ⟨165654181049605832033923729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220872241399474442711898305 165654181049605832033923729)
      ·
        refine ⟨124240635787204374025442797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165654181049605832033923729 124240635787204374025442797)
        ·
          refine ⟨46590238420201640259541049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124240635787204374025442797 46590238420201640259541049)
          ·
            refine ⟨34942678815151230194655787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46590238420201640259541049 34942678815151230194655787)
            ·
              refine ⟨52414018222726845291983681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34942678815151230194655787 52414018222726845291983681)
              ·
                refine ⟨39310513667045133968987761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52414018222726845291983681 39310513667045133968987761)
                ·
                  refine ⟨29482885250283850476740821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39310513667045133968987761 29482885250283850476740821)
                  ·
                    refine ⟨691005123053527745548613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29482885250283850476740821 691005123053527745548613)
                    ·
                      rfl

theorem cell23_4037183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_4037183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037183 prefixEnd_4037183 := by exact prefixLift 4037183
  have htrace : WordTrace (prefixWord ++ tailWord_4037183) baseStart_4037183 baseEnd_4037183 := by
    simpa [prefixWord, tailWord_4037183, baseEnd_4037183] using wordTrace_append hprefix tailTrace_4037183
  have hstable : (prefixWord ++ tailWord_4037183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037183).length < 2 ^ (prefixWord ++ tailWord_4037183).sum := by decide
  have hdescent : baseEnd_4037183 < baseStart_4037183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037243 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 9]
def baseStart_4037243 : Nat := 118140960795 + 4037243 * 2 ^ 59
def prefixEnd_4037243 : Nat := 4983230072969 + 3 ^ 40 * 4037243 * 2
def baseEnd_4037243 : Nat := 230338464222205889099507

theorem tailTrace_4037243 : CollatzResearch.WordTrace tailWord_4037243 prefixEnd_4037243 230338464222205889099507 := by
  unfold tailWord_4037243
  simp only [CollatzResearch.WordTrace]
  refine ⟨147250349312765592055116383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98166899541843728036744255 147250349312765592055116383)
  ·
    refine ⟨220875523969148388082674575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147250349312765592055116383 220875523969148388082674575)
    ·
      refine ⟨331313285953722582124011863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220875523969148388082674575 331313285953722582124011863)
      ·
        refine ⟨496969928930583873186017795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331313285953722582124011863 496969928930583873186017795)
        ·
          refine ⟨745454893395875809779026693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496969928930583873186017795 745454893395875809779026693)
          ·
            refine ⟨139772792511726714333567505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 745454893395875809779026693 139772792511726714333567505)
            ·
              refine ⟨104829594383795035750175629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139772792511726714333567505 104829594383795035750175629)
              ·
                refine ⟨39311097893923138406315861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104829594383795035750175629 39311097893923138406315861)
                ·
                  refine ⟨230338464222205889099507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39311097893923138406315861 230338464222205889099507)
                  ·
                    rfl

theorem cell23_4037243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 9].length) (baseStart_4037243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037243 prefixEnd_4037243 := by exact prefixLift 4037243
  have htrace : WordTrace (prefixWord ++ tailWord_4037243) baseStart_4037243 baseEnd_4037243 := by
    simpa [prefixWord, tailWord_4037243, baseEnd_4037243] using wordTrace_append hprefix tailTrace_4037243
  have hstable : (prefixWord ++ tailWord_4037243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037243).length < 2 ^ (prefixWord ++ tailWord_4037243).sum := by decide
  have hdescent : baseEnd_4037243 < baseStart_4037243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037277 : List Nat := [1, 4, 2, 1, 1, 1, 2, 6, 5]
def baseStart_4037277 : Nat := 118140960795 + 4037277 * 2 ^ 59
def prefixEnd_4037277 : Nat := 4983230072969 + 3 ^ 40 * 4037277 * 2
def baseEnd_4037277 : Nat := 230340404038011763207823

theorem tailTrace_4037277 : CollatzResearch.WordTrace tailWord_4037277 prefixEnd_4037277 230340404038011763207823 := by
  unfold tailWord_4037277
  simp only [CollatzResearch.WordTrace]
  refine ⟨147251589394642415861854085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98167726263094943907902723 147251589394642415861854085)
  ·
    refine ⟨27609673011495452974097641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147251589394642415861854085 27609673011495452974097641)
    ·
      refine ⟨20707254758621589730573231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27609673011495452974097641 20707254758621589730573231)
      ·
        refine ⟨31060882137932384595859847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20707254758621589730573231 31060882137932384595859847)
        ·
          refine ⟨46591323206898576893789771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31060882137932384595859847 46591323206898576893789771)
          ·
            refine ⟨69886984810347865340684657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46591323206898576893789771 69886984810347865340684657)
            ·
              refine ⟨52415238607760899005513493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69886984810347865340684657 52415238607760899005513493)
              ·
                refine ⟨2456964309738792140883445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52415238607760899005513493 2456964309738792140883445)
                ·
                  refine ⟨230340404038011763207823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2456964309738792140883445 230340404038011763207823)
                  ·
                    rfl

theorem cell23_4037277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 6, 5].length) (baseStart_4037277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037277 prefixEnd_4037277 := by exact prefixLift 4037277
  have htrace : WordTrace (prefixWord ++ tailWord_4037277) baseStart_4037277 baseEnd_4037277 := by
    simpa [prefixWord, tailWord_4037277, baseEnd_4037277] using wordTrace_append hprefix tailTrace_4037277
  have hstable : (prefixWord ++ tailWord_4037277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037277).length < 2 ^ (prefixWord ++ tailWord_4037277).sum := by decide
  have hdescent : baseEnd_4037277 < baseStart_4037277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037337 : List Nat := [1, 2, 1, 2, 3, 2, 2, 3, 3, 4]
def baseStart_4037337 : Nat := 118140960795 + 4037337 * 2 ^ 59
def prefixEnd_4037337 : Nat := 4983230072969 + 3 ^ 40 * 4037337 * 2
def baseEnd_4037337 : Nat := 691031481727125211373377

theorem tailTrace_4037337 : CollatzResearch.WordTrace tailWord_4037337 prefixEnd_4037337 691031481727125211373377 := by
  unfold tailWord_4037337
  simp only [CollatzResearch.WordTrace]
  refine ⟨147253777774425046109038265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98169185182950030739358843 147253777774425046109038265)
  ·
    refine ⟨110440333330818784581778699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147253777774425046109038265 110440333330818784581778699)
    ·
      refine ⟨165660499996228176872668049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110440333330818784581778699 165660499996228176872668049)
      ·
        refine ⟨124245374997171132654501037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165660499996228176872668049 124245374997171132654501037)
        ·
          refine ⟨46592015623939174745437889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124245374997171132654501037 46592015623939174745437889)
          ·
            refine ⟨34944011717954381059078417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46592015623939174745437889 34944011717954381059078417)
            ·
              refine ⟨26208008788465785794308813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34944011717954381059078417 26208008788465785794308813)
              ·
                refine ⟨9828003295674669672865805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26208008788465785794308813 9828003295674669672865805)
                ·
                  refine ⟨3685501235878001127324677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9828003295674669672865805 3685501235878001127324677)
                  ·
                    refine ⟨691031481727125211373377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685501235878001127324677 691031481727125211373377)
                    ·
                      rfl

theorem cell23_4037337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 4].length) (baseStart_4037337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037337 prefixEnd_4037337 := by exact prefixLift 4037337
  have htrace : WordTrace (prefixWord ++ tailWord_4037337) baseStart_4037337 baseEnd_4037337 := by
    simpa [prefixWord, tailWord_4037337, baseEnd_4037337] using wordTrace_append hprefix tailTrace_4037337
  have hstable : (prefixWord ++ tailWord_4037337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037337).length < 2 ^ (prefixWord ++ tailWord_4037337).sum := by decide
  have hdescent : baseEnd_4037337 < baseStart_4037337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037384 : List Nat := [2, 1, 3, 2, 2, 4, 1, 2, 6]
def baseStart_4037384 : Nat := 118140960795 + 4037384 * 2 ^ 59
def prefixEnd_4037384 : Nat := 4983230072969 + 3 ^ 40 * 4037384 * 2
def baseEnd_4037384 : Nat := 230346508752459661136935

theorem tailTrace_4037384 : CollatzResearch.WordTrace tailWord_4037384 prefixEnd_4037384 230346508752459661136935 := by
  unfold tailWord_4037384
  simp only [CollatzResearch.WordTrace]
  refine ⟨73627746002627386567999603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98170328003503182090666137 73627746002627386567999603)
  ·
    refine ⟨110441619003941079851999405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73627746002627386567999603 110441619003941079851999405)
    ·
      refine ⟨41415607126477904944499777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110441619003941079851999405 41415607126477904944499777)
      ·
        refine ⟨31061705344858428708374833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41415607126477904944499777 31061705344858428708374833)
        ·
          refine ⟨23296279008643821531281125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31061705344858428708374833 23296279008643821531281125)
          ·
            refine ⟨4368052314120716537115211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23296279008643821531281125 4368052314120716537115211)
            ·
              refine ⟨6552078471181074805672817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368052314120716537115211 6552078471181074805672817)
              ·
                refine ⟨4914058853385806104254613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552078471181074805672817 4914058853385806104254613)
                ·
                  refine ⟨230346508752459661136935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4914058853385806104254613 230346508752459661136935)
                  ·
                    rfl

theorem cell23_4037384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 2, 6].length) (baseStart_4037384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037384 prefixEnd_4037384 := by exact prefixLift 4037384
  have htrace : WordTrace (prefixWord ++ tailWord_4037384) baseStart_4037384 baseEnd_4037384 := by
    simpa [prefixWord, tailWord_4037384, baseEnd_4037384] using wordTrace_append hprefix tailTrace_4037384
  have hstable : (prefixWord ++ tailWord_4037384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037384).length < 2 ^ (prefixWord ++ tailWord_4037384).sum := by decide
  have hdescent : baseEnd_4037384 < baseStart_4037384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037404 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 5, 2]
def baseStart_4037404 : Nat := 118140960795 + 4037404 * 2 ^ 59
def prefixEnd_4037404 : Nat := 4983230072969 + 3 ^ 40 * 4037404 * 2
def baseEnd_4037404 : Nat := 2073128848385226871982323

theorem tailTrace_4037404 : CollatzResearch.WordTrace tailWord_4037404 prefixEnd_4037404 2073128848385226871982323 := by
  unfold tailWord_4037404
  simp only [CollatzResearch.WordTrace]
  refine ⟨73628110732591158275863633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98170814310121544367818177 73628110732591158275863633)
  ·
    refine ⟨55221083049443368706897725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73628110732591158275863633 55221083049443368706897725)
    ·
      refine ⟨20707906143541263265086647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55221083049443368706897725 20707906143541263265086647)
      ·
        refine ⟨31061859215311894897629971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20707906143541263265086647 31061859215311894897629971)
        ·
          refine ⟨46592788822967842346444957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31061859215311894897629971 46592788822967842346444957)
          ·
            refine ⟨17472295808612940879916859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46592788822967842346444957 17472295808612940879916859)
            ·
              refine ⟨26208443712919411319875289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17472295808612940879916859 26208443712919411319875289)
              ·
                refine ⟨19656332784689558489906467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26208443712919411319875289 19656332784689558489906467)
                ·
                  refine ⟨29484499177034337734859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19656332784689558489906467 29484499177034337734859701)
                  ·
                    refine ⟨2764171797846969162643097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29484499177034337734859701 2764171797846969162643097)
                    ·
                      refine ⟨2073128848385226871982323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764171797846969162643097 2073128848385226871982323)
                      ·
                        rfl

theorem cell23_4037404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_4037404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037404 prefixEnd_4037404 := by exact prefixLift 4037404
  have htrace : WordTrace (prefixWord ++ tailWord_4037404) baseStart_4037404 baseEnd_4037404 := by
    simpa [prefixWord, tailWord_4037404, baseEnd_4037404] using wordTrace_append hprefix tailTrace_4037404
  have hstable : (prefixWord ++ tailWord_4037404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037404).length < 2 ^ (prefixWord ++ tailWord_4037404).sum := by decide
  have hdescent : baseEnd_4037404 < baseStart_4037404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037438 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 2, 3, 2]
def baseStart_4037438 : Nat := 118140960795 + 4037438 * 2 ^ 59
def prefixEnd_4037438 : Nat := 4983230072969 + 3 ^ 40 * 4037438 * 2
def baseEnd_4037438 : Nat := 2073146306727479738957167

theorem tailTrace_4037438 : CollatzResearch.WordTrace tailWord_4037438 prefixEnd_4037438 2073146306727479738957167 := by
  unfold tailWord_4037438
  simp only [CollatzResearch.WordTrace]
  refine ⟨18407182693382392544808121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98171641031372760238976645 18407182693382392544808121)
  ·
    refine ⟨13805387020036794408606091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18407182693382392544808121 13805387020036794408606091)
    ·
      refine ⟨20708080530055191612909137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805387020036794408606091 20708080530055191612909137)
      ·
        refine ⟨15531060397541393709681853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20708080530055191612909137 15531060397541393709681853)
        ·
          refine ⟨5824147649078022641130695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15531060397541393709681853 5824147649078022641130695)
          ·
            refine ⟨8736221473617033961696043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824147649078022641130695 8736221473617033961696043)
            ·
              refine ⟨13104332210425550942544065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736221473617033961696043 13104332210425550942544065)
              ·
                refine ⟨9828249157819163206908049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13104332210425550942544065 9828249157819163206908049)
                ·
                  refine ⟨7371186868364372405181037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828249157819163206908049 7371186868364372405181037)
                  ·
                    refine ⟨2764195075636639651942889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7371186868364372405181037 2764195075636639651942889)
                    ·
                      refine ⟨2073146306727479738957167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764195075636639651942889 2073146306727479738957167)
                      ·
                        rfl

theorem cell23_4037438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_4037438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037438 prefixEnd_4037438 := by exact prefixLift 4037438
  have htrace : WordTrace (prefixWord ++ tailWord_4037438) baseStart_4037438 baseEnd_4037438 := by
    simpa [prefixWord, tailWord_4037438, baseEnd_4037438] using wordTrace_append hprefix tailTrace_4037438
  have hstable : (prefixWord ++ tailWord_4037438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037438).length < 2 ^ (prefixWord ++ tailWord_4037438).sum := by decide
  have hdescent : baseEnd_4037438 < baseStart_4037438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037468 : List Nat := [2, 2, 4, 2, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4037468 : Nat := 118140960795 + 4037468 * 2 ^ 59
def prefixEnd_4037468 : Nat := 4983230072969 + 3 ^ 40 * 4037468 * 2
def baseEnd_4037468 : Nat := 2073161711147114621582029

theorem tailTrace_4037468 : CollatzResearch.WordTrace tailWord_4037468 prefixEnd_4037468 2073161711147114621582029 := by
  unfold tailWord_4037468
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629277868475227741028529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98172370491300303654704705 73629277868475227741028529)
  ·
    refine ⟨55221958401356420805771397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73629277868475227741028529 55221958401356420805771397)
    ·
      refine ⟨10354117200254328901082137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55221958401356420805771397 10354117200254328901082137)
      ·
        refine ⟨7765587900190746675811603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10354117200254328901082137 7765587900190746675811603)
        ·
          refine ⟨11648381850286120013717405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765587900190746675811603 11648381850286120013717405)
          ·
            refine ⟨4368143193857295005144027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11648381850286120013717405 4368143193857295005144027)
            ·
              refine ⟨6552214790785942507716041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368143193857295005144027 6552214790785942507716041)
              ·
                refine ⟨4914161093089456880787031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552214790785942507716041 4914161093089456880787031)
                ·
                  refine ⟨7371241639634185321180547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914161093089456880787031 7371241639634185321180547)
                  ·
                    refine ⟨11056862459451277981770821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7371241639634185321180547 11056862459451277981770821)
                    ·
                      refine ⟨2073161711147114621582029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11056862459451277981770821 2073161711147114621582029)
                      ·
                        rfl

theorem cell23_4037468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4037468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037468 prefixEnd_4037468 := by exact prefixLift 4037468
  have htrace : WordTrace (prefixWord ++ tailWord_4037468) baseStart_4037468 baseEnd_4037468 := by
    simpa [prefixWord, tailWord_4037468, baseEnd_4037468] using wordTrace_append hprefix tailTrace_4037468
  have hstable : (prefixWord ++ tailWord_4037468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037468).length < 2 ^ (prefixWord ++ tailWord_4037468).sum := by decide
  have hdescent : baseEnd_4037468 < baseStart_4037468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037484 : List Nat := [2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 3]
def baseStart_4037484 : Nat := 118140960795 + 4037484 * 2 ^ 59
def prefixEnd_4037484 : Nat := 4983230072969 + 3 ^ 40 * 4037484 * 2
def baseEnd_4037484 : Nat := 2073169926837586558981955

theorem tailTrace_4037484 : CollatzResearch.WordTrace tailWord_4037484 prefixEnd_4037484 2073169926837586558981955 := by
  unfold tailWord_4037484
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629569652446245107319753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98172759536594993476426337 73629569652446245107319753)
  ·
    refine ⟨55222177239334683830489815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73629569652446245107319753 55222177239334683830489815)
    ·
      refine ⟨82833265859002025745734723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55222177239334683830489815 82833265859002025745734723)
      ·
        refine ⟨124249898788503038618602085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82833265859002025745734723 124249898788503038618602085)
        ·
          refine ⟨23296856022844319740987891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124249898788503038618602085 23296856022844319740987891)
          ·
            refine ⟨34945284034266479611481837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296856022844319740987891 34945284034266479611481837)
            ·
              refine ⟨13104481512849929854305689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34945284034266479611481837 13104481512849929854305689)
              ·
                refine ⟨9828361134637447390729267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13104481512849929854305689 9828361134637447390729267)
                ·
                  refine ⟨14742541701956171086093901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9828361134637447390729267 14742541701956171086093901)
                  ·
                    refine ⟨5528453138233564157285213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14742541701956171086093901 5528453138233564157285213)
                    ·
                      refine ⟨2073169926837586558981955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528453138233564157285213 2073169926837586558981955)
                      ·
                        rfl

theorem cell23_4037484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_4037484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037484 prefixEnd_4037484 := by exact prefixLift 4037484
  have htrace : WordTrace (prefixWord ++ tailWord_4037484) baseStart_4037484 baseEnd_4037484 := by
    simpa [prefixWord, tailWord_4037484, baseEnd_4037484] using wordTrace_append hprefix tailTrace_4037484
  have hstable : (prefixWord ++ tailWord_4037484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037484).length < 2 ^ (prefixWord ++ tailWord_4037484).sum := by decide
  have hdescent : baseEnd_4037484 < baseStart_4037484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037501 : List Nat := [1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_4037501 : Nat := 118140960795 + 4037501 * 2 ^ 59
def prefixEnd_4037501 : Nat := 4983230072969 + 3 ^ 40 * 4037501 * 2
def baseEnd_4037501 : Nat := 2073178656008712992469377

theorem tailTrace_4037501 : CollatzResearch.WordTrace tailWord_4037501 prefixEnd_4037501 2073178656008712992469377 := by
  unfold tailWord_4037501
  simp only [CollatzResearch.WordTrace]
  refine ⟨147259759345830902118008357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98173172897220601412005571 147259759345830902118008357)
  ·
    refine ⟨27611204877343294147126567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147259759345830902118008357 27611204877343294147126567)
    ·
      refine ⟨41416807316014941220689851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27611204877343294147126567 41416807316014941220689851)
      ·
        refine ⟨62125210974022411831034777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41416807316014941220689851 62125210974022411831034777)
        ·
          refine ⟨46593908230516808873276083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62125210974022411831034777 46593908230516808873276083)
          ·
            refine ⟨69890862345775213309914125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46593908230516808873276083 69890862345775213309914125)
            ·
              refine ⟨26209073379665704991217797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69890862345775213309914125 26209073379665704991217797)
              ·
                refine ⟨4914201258687319685853337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26209073379665704991217797 4914201258687319685853337)
                ·
                  refine ⟨3685650944015489764390003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4914201258687319685853337 3685650944015489764390003)
                  ·
                    refine ⟨5528476416023234646585005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3685650944015489764390003 5528476416023234646585005)
                    ·
                      refine ⟨2073178656008712992469377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528476416023234646585005 2073178656008712992469377)
                      ·
                        rfl

theorem cell23_4037501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_4037501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037501 prefixEnd_4037501 := by exact prefixLift 4037501
  have htrace : WordTrace (prefixWord ++ tailWord_4037501) baseStart_4037501 baseEnd_4037501 := by
    simpa [prefixWord, tailWord_4037501, baseEnd_4037501] using wordTrace_append hprefix tailTrace_4037501
  have hstable : (prefixWord ++ tailWord_4037501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037501).length < 2 ^ (prefixWord ++ tailWord_4037501).sum := by decide
  have hdescent : baseEnd_4037501 < baseStart_4037501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037507 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_4037507 : Nat := 118140960795 + 4037507 * 2 ^ 59
def prefixEnd_4037507 : Nat := 4983230072969 + 3 ^ 40 * 4037507 * 2
def baseEnd_4037507 : Nat := 2073181736892639968994349

theorem tailTrace_4037507 : CollatzResearch.WordTrace tailWord_4037507 prefixEnd_4037507 2073181736892639968994349 := by
  unfold tailWord_4037507
  simp only [CollatzResearch.WordTrace]
  refine ⟨147259978183809165142726775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98173318789206110095151183 147259978183809165142726775)
  ·
    refine ⟨220889967275713747714090163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147259978183809165142726775 220889967275713747714090163)
    ·
      refine ⟨331334950913570621571135245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220889967275713747714090163 331334950913570621571135245)
      ·
        refine ⟨124250606592588983089175717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331334950913570621571135245 124250606592588983089175717)
        ·
          refine ⟨23296988736110434329220447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124250606592588983089175717 23296988736110434329220447)
          ·
            refine ⟨34945483104165651493830671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296988736110434329220447 34945483104165651493830671)
            ·
              refine ⟨52418224656248477240746007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34945483104165651493830671 52418224656248477240746007)
              ·
                refine ⟨78627336984372715861119011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52418224656248477240746007 78627336984372715861119011)
                ·
                  refine ⟨117941005476559073791678517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78627336984372715861119011 117941005476559073791678517)
                  ·
                    refine ⟨11056969263427413167969861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117941005476559073791678517 11056969263427413167969861)
                    ·
                      refine ⟨2073181736892639968994349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11056969263427413167969861 2073181736892639968994349)
                      ·
                        rfl

theorem cell23_4037507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_4037507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037507 prefixEnd_4037507 := by exact prefixLift 4037507
  have htrace : WordTrace (prefixWord ++ tailWord_4037507) baseStart_4037507 baseEnd_4037507 := by
    simpa [prefixWord, tailWord_4037507, baseEnd_4037507] using wordTrace_append hprefix tailTrace_4037507
  have hstable : (prefixWord ++ tailWord_4037507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037507).length < 2 ^ (prefixWord ++ tailWord_4037507).sum := by decide
  have hdescent : baseEnd_4037507 < baseStart_4037507 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037511 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_4037511 : Nat := 118140960795 + 4037511 * 2 ^ 59
def prefixEnd_4037511 : Nat := 4983230072969 + 3 ^ 40 * 4037511 * 2
def baseEnd_4037511 : Nat := 2073183790815257953344331

theorem tailTrace_4037511 : CollatzResearch.WordTrace tailWord_4037511 prefixEnd_4037511 2073183790815257953344331 := by
  unfold tailWord_4037511
  simp only [CollatzResearch.WordTrace]
  refine ⟨147260124075794673825872387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98173416050529782550581591 147260124075794673825872387)
  ·
    refine ⟨220890186113692010738808581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147260124075794673825872387 220890186113692010738808581)
    ·
      refine ⟨41416909896317252013526609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220890186113692010738808581 41416909896317252013526609)
      ·
        refine ⟨31062682422237939010144957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41416909896317252013526609 31062682422237939010144957)
        ·
          refine ⟨11648505908339227128804359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31062682422237939010144957 11648505908339227128804359)
          ·
            refine ⟨17472758862508840693206539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648505908339227128804359 17472758862508840693206539)
            ·
              refine ⟨26209138293763261039809809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17472758862508840693206539 26209138293763261039809809)
              ·
                refine ⟨19656853720322445779857357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26209138293763261039809809 19656853720322445779857357)
                ·
                  refine ⟨7371320145120917167446509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19656853720322445779857357 7371320145120917167446509)
                  ·
                    refine ⟨2764245054420343937792441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7371320145120917167446509 2764245054420343937792441)
                    ·
                      refine ⟨2073183790815257953344331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764245054420343937792441 2073183790815257953344331)
                      ·
                        rfl

theorem cell23_4037511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_4037511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037511 prefixEnd_4037511 := by exact prefixLift 4037511
  have htrace : WordTrace (prefixWord ++ tailWord_4037511) baseStart_4037511 baseEnd_4037511 := by
    simpa [prefixWord, tailWord_4037511, baseEnd_4037511] using wordTrace_append hprefix tailTrace_4037511
  have hstable : (prefixWord ++ tailWord_4037511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037511).length < 2 ^ (prefixWord ++ tailWord_4037511).sum := by decide
  have hdescent : baseEnd_4037511 < baseStart_4037511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037524 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4037524 : Nat := 118140960795 + 4037524 * 2 ^ 59
def prefixEnd_4037524 : Nat := 4983230072969 + 3 ^ 40 * 4037524 * 2
def baseEnd_4037524 : Nat := 2073190466063766402481771

theorem tailTrace_4037524 : CollatzResearch.WordTrace tailWord_4037524 prefixEnd_4037524 2073190466063766402481771 := by
  unfold tailWord_4037524
  simp only [CollatzResearch.WordTrace]
  refine ⟨73630299112373788523047813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98173732149831718030730417 73630299112373788523047813)
  ·
    refine ⟨13805681083570085348071465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73630299112373788523047813 13805681083570085348071465)
    ·
      refine ⟨10354260812677564011053599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13805681083570085348071465 10354260812677564011053599)
      ·
        refine ⟨15531391219016346016580399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10354260812677564011053599 15531391219016346016580399)
        ·
          refine ⟨23297086828524519024870599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15531391219016346016580399 23297086828524519024870599)
          ·
            refine ⟨34945630242786778537305899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23297086828524519024870599 34945630242786778537305899)
            ·
              refine ⟨52418445364180167805958849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34945630242786778537305899 52418445364180167805958849)
              ·
                refine ⟨39313834023135125854469137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52418445364180167805958849 39313834023135125854469137)
                ·
                  refine ⟨29485375517351344390851853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39313834023135125854469137 29485375517351344390851853)
                  ·
                    refine ⟨11057015819006754146569445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29485375517351344390851853 11057015819006754146569445)
                    ·
                      refine ⟨2073190466063766402481771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11057015819006754146569445 2073190466063766402481771)
                      ·
                        rfl

theorem cell23_4037524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4037524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037524 prefixEnd_4037524 := by exact prefixLift 4037524
  have htrace : WordTrace (prefixWord ++ tailWord_4037524) baseStart_4037524 baseEnd_4037524 := by
    simpa [prefixWord, tailWord_4037524, baseEnd_4037524] using wordTrace_append hprefix tailTrace_4037524
  have hstable : (prefixWord ++ tailWord_4037524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037524).length < 2 ^ (prefixWord ++ tailWord_4037524).sum := by decide
  have hdescent : baseEnd_4037524 < baseStart_4037524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037594 : List Nat := [3, 1, 1, 2, 4, 1, 2, 1, 1, 7]
def baseStart_4037594 : Nat := 118140960795 + 4037594 * 2 ^ 59
def prefixEnd_4037594 : Nat := 4983230072969 + 3 ^ 40 * 4037594 * 2
def baseEnd_4037594 : Nat := 691075469903193709535483

theorem tailTrace_4037594 : CollatzResearch.WordTrace tailWord_4037594 prefixEnd_4037594 691075469903193709535483 := by
  unfold tailWord_4037594
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815787833623494750285959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98175434222995986000762557 36815787833623494750285959)
  ·
    refine ⟨55223681750435242125428939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36815787833623494750285959 55223681750435242125428939)
    ·
      refine ⟨82835522625652863188143409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55223681750435242125428939 82835522625652863188143409)
      ·
        refine ⟨62126641969239647391107557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82835522625652863188143409 62126641969239647391107557)
        ·
          refine ⟨11648745369232433885832667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62126641969239647391107557 11648745369232433885832667)
          ·
            refine ⟨17473118053848650828749001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648745369232433885832667 17473118053848650828749001)
            ·
              refine ⟨13104838540386488121561751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17473118053848650828749001 13104838540386488121561751)
              ·
                refine ⟨19657257810579732182342627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104838540386488121561751 19657257810579732182342627)
                ·
                  refine ⟨29485886715869598273513941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19657257810579732182342627 29485886715869598273513941)
                  ·
                    refine ⟨691075469903193709535483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29485886715869598273513941 691075469903193709535483)
                    ·
                      rfl

theorem cell23_4037594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_4037594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037594 prefixEnd_4037594 := by exact prefixLift 4037594
  have htrace : WordTrace (prefixWord ++ tailWord_4037594) baseStart_4037594 baseEnd_4037594 := by
    simpa [prefixWord, tailWord_4037594, baseEnd_4037594] using wordTrace_append hprefix tailTrace_4037594
  have hstable : (prefixWord ++ tailWord_4037594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037594).length < 2 ^ (prefixWord ++ tailWord_4037594).sum := by decide
  have hdescent : baseEnd_4037594 < baseStart_4037594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037658 : List Nat := [3, 1, 1, 3, 1, 2, 2, 5, 1, 4]
def baseStart_4037658 : Nat := 118140960795 + 4037658 * 2 ^ 59
def prefixEnd_4037658 : Nat := 4983230072969 + 3 ^ 40 * 4037658 * 2
def baseEnd_4037658 : Nat := 691086424157156292735385

theorem tailTrace_4037658 : CollatzResearch.WordTrace tailWord_4037658 prefixEnd_4037658 691086424157156292735385 := by
  unfold tailWord_4037658
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816371401565529482868407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98176990404174745287649085 36816371401565529482868407)
  ·
    refine ⟨55224557102348294224302611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36816371401565529482868407 55224557102348294224302611)
    ·
      refine ⟨82836835653522441336453917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55224557102348294224302611 82836835653522441336453917)
      ·
        refine ⟨31063813370070915501170219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82836835653522441336453917 31063813370070915501170219)
        ·
          refine ⟨46595720055106373251755329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31063813370070915501170219 46595720055106373251755329)
          ·
            refine ⟨34946790041329779938816497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46595720055106373251755329 34946790041329779938816497)
            ·
              refine ⟨26210092530997334954112373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34946790041329779938816497 26210092530997334954112373)
              ·
                refine ⟨2457196174781000151948035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26210092530997334954112373 2457196174781000151948035)
                ·
                  refine ⟨3685794262171500227922053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457196174781000151948035 3685794262171500227922053)
                  ·
                    refine ⟨691086424157156292735385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3685794262171500227922053 691086424157156292735385)
                    ·
                      rfl

theorem cell23_4037658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_4037658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037658 prefixEnd_4037658 := by exact prefixLift 4037658
  have htrace : WordTrace (prefixWord ++ tailWord_4037658) baseStart_4037658 baseEnd_4037658 := by
    simpa [prefixWord, tailWord_4037658, baseEnd_4037658] using wordTrace_append hprefix tailTrace_4037658
  have hstable : (prefixWord ++ tailWord_4037658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037658).length < 2 ^ (prefixWord ++ tailWord_4037658).sum := by decide
  have hdescent : baseEnd_4037658 < baseStart_4037658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037668 : List Nat := [2, 3, 1, 4, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4037668 : Nat := 118140960795 + 4037668 * 2 ^ 59
def prefixEnd_4037668 : Nat := 4983230072969 + 3 ^ 40 * 4037668 * 2
def baseEnd_4037668 : Nat := 2073264407278013839081109

theorem tailTrace_4037668 : CollatzResearch.WordTrace tailWord_4037668 prefixEnd_4037668 2073264407278013839081109 := by
  unfold tailWord_4037668
  simp only [CollatzResearch.WordTrace]
  refine ⟨73632925168112944819668829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98177233557483926426225105 73632925168112944819668829)
  ·
    refine ⟨27612346938042354307375811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73632925168112944819668829 27612346938042354307375811)
    ·
      refine ⟨41418520407063531461063717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27612346938042354307375811 41418520407063531461063717)
      ·
        refine ⟨7765972576324412148949447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41418520407063531461063717 7765972576324412148949447)
        ·
          refine ⟨11648958864486618223424171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765972576324412148949447 11648958864486618223424171)
          ·
            refine ⟨17473438296729927335136257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648958864486618223424171 17473438296729927335136257)
            ·
              refine ⟨13105078722547445501352193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17473438296729927335136257 13105078722547445501352193)
              ·
                refine ⟨9828809041910584126014145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13105078722547445501352193 9828809041910584126014145)
                ·
                  refine ⟨7371606781432938094510609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828809041910584126014145 7371606781432938094510609)
                  ·
                    refine ⟨5528705086074703570882957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371606781432938094510609 5528705086074703570882957)
                    ·
                      refine ⟨2073264407278013839081109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528705086074703570882957 2073264407278013839081109)
                      ·
                        rfl

theorem cell23_4037668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4037668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037668 prefixEnd_4037668 := by exact prefixLift 4037668
  have htrace : WordTrace (prefixWord ++ tailWord_4037668) baseStart_4037668 baseEnd_4037668 := by
    simpa [prefixWord, tailWord_4037668, baseEnd_4037668] using wordTrace_append hprefix tailTrace_4037668
  have hstable : (prefixWord ++ tailWord_4037668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037668).length < 2 ^ (prefixWord ++ tailWord_4037668).sum := by decide
  have hdescent : baseEnd_4037668 < baseStart_4037668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037702 : List Nat := [6, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_4037702 : Nat := 118140960795 + 4037702 * 2 ^ 59
def prefixEnd_4037702 : Nat := 4983230072969 + 3 ^ 40 * 4037702 * 2
def baseEnd_4037702 : Nat := 2073281865620266706055953

theorem tailTrace_4037702 : CollatzResearch.WordTrace tailWord_4037702 prefixEnd_4037702 2073281865620266706055953 := by
  unfold tailWord_4037702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602096575565709795189855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98178060278735142297383573 4602096575565709795189855)
  ·
    refine ⟨6903144863348564692784783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602096575565709795189855 6903144863348564692784783)
    ·
      refine ⟨10354717295022847039177175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6903144863348564692784783 10354717295022847039177175)
      ·
        refine ⟨15532075942534270558765763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10354717295022847039177175 15532075942534270558765763)
        ·
          refine ⟨23298113913801405838148645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15532075942534270558765763 23298113913801405838148645)
          ·
            refine ⟨4368396358837763594652871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23298113913801405838148645 4368396358837763594652871)
            ·
              refine ⟨6552594538256645391979307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368396358837763594652871 6552594538256645391979307)
              ·
                refine ⟨9828891807384968087968961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552594538256645391979307 9828891807384968087968961)
                ·
                  refine ⟨7371668855538726065976721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828891807384968087968961 7371668855538726065976721)
                  ·
                    refine ⟨5528751641654044549482541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371668855538726065976721 5528751641654044549482541)
                    ·
                      refine ⟨2073281865620266706055953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528751641654044549482541 2073281865620266706055953)
                      ·
                        rfl

theorem cell23_4037702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_4037702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037702 prefixEnd_4037702 := by exact prefixLift 4037702
  have htrace : WordTrace (prefixWord ++ tailWord_4037702) baseStart_4037702 baseEnd_4037702 := by
    simpa [prefixWord, tailWord_4037702, baseEnd_4037702] using wordTrace_append hprefix tailTrace_4037702
  have hstable : (prefixWord ++ tailWord_4037702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037702).length < 2 ^ (prefixWord ++ tailWord_4037702).sum := by decide
  have hdescent : baseEnd_4037702 < baseStart_4037702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037741 : List Nat := [1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4037741 : Nat := 118140960795 + 4037741 * 2 ^ 59
def prefixEnd_4037741 : Nat := 4983230072969 + 3 ^ 40 * 4037741 * 2
def baseEnd_4037741 : Nat := 2073301891365792053468273

theorem tailTrace_4037741 : CollatzResearch.WordTrace tailWord_4037741 prefixEnd_4037741 2073301891365792053468273 := by
  unfold tailWord_4037741
  simp only [CollatzResearch.WordTrace]
  refine ⟨147268512864961423106745077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98179008576640948737830051 147268512864961423106745077)
  ·
    refine ⟨13806423081090133416257351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147268512864961423106745077 13806423081090133416257351)
    ·
      refine ⟨20709634621635200124386027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13806423081090133416257351 20709634621635200124386027)
      ·
        refine ⟨31064451932452800186579041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20709634621635200124386027 31064451932452800186579041)
        ·
          refine ⟨23298338949339600139934281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31064451932452800186579041 23298338949339600139934281)
          ·
            refine ⟨17473754212004700104950711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23298338949339600139934281 17473754212004700104950711)
            ·
              refine ⟨26210631318007050157426067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17473754212004700104950711 26210631318007050157426067)
              ·
                refine ⟨39315946977010575236139101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26210631318007050157426067 39315946977010575236139101)
                ·
                  refine ⟨14743480116378965713552163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39315946977010575236139101 14743480116378965713552163)
                  ·
                    refine ⟨22115220174568448570328245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14743480116378965713552163 22115220174568448570328245)
                    ·
                      refine ⟨2073301891365792053468273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22115220174568448570328245 2073301891365792053468273)
                      ·
                        rfl

theorem cell23_4037741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4037741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037741 prefixEnd_4037741 := by exact prefixLift 4037741
  have htrace : WordTrace (prefixWord ++ tailWord_4037741) baseStart_4037741 baseEnd_4037741 := by
    simpa [prefixWord, tailWord_4037741, baseEnd_4037741] using wordTrace_append hprefix tailTrace_4037741
  have hstable : (prefixWord ++ tailWord_4037741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037741).length < 2 ^ (prefixWord ++ tailWord_4037741).sum := by decide
  have hdescent : baseEnd_4037741 < baseStart_4037741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037744 : List Nat := [2, 1, 1, 1, 5, 1, 2, 10]
def baseStart_4037744 : Nat := 118140960795 + 4037744 * 2 ^ 59
def prefixEnd_4037744 : Nat := 4983230072969 + 3 ^ 40 * 4037744 * 2
def baseEnd_4037744 : Nat := 76789015992879834878917

theorem tailTrace_4037744 : CollatzResearch.WordTrace tailWord_4037744 prefixEnd_4037744 76789015992879834878917 := by
  unfold tailWord_4037744
  simp only [CollatzResearch.WordTrace]
  refine ⟨73634311141975277309552143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98179081522633703079402857 73634311141975277309552143)
  ·
    refine ⟨110451466712962915964328215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73634311141975277309552143 110451466712962915964328215)
    ·
      refine ⟨165677200069444373946492323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110451466712962915964328215 165677200069444373946492323)
      ·
        refine ⟨248515800104166560919738485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165677200069444373946492323 248515800104166560919738485)
        ·
          refine ⟨23298356259765615086225483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248515800104166560919738485 23298356259765615086225483)
          ·
            refine ⟨34947534389648422629338225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23298356259765615086225483 34947534389648422629338225)
            ·
              refine ⟨26210650792236316972003669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34947534389648422629338225 26210650792236316972003669)
              ·
                refine ⟨76789015992879834878917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 26210650792236316972003669 76789015992879834878917)
                ·
                  rfl

theorem cell23_4037744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 10].length) (baseStart_4037744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037744 prefixEnd_4037744 := by exact prefixLift 4037744
  have htrace : WordTrace (prefixWord ++ tailWord_4037744) baseStart_4037744 baseEnd_4037744 := by
    simpa [prefixWord, tailWord_4037744, baseEnd_4037744] using wordTrace_append hprefix tailTrace_4037744
  have hstable : (prefixWord ++ tailWord_4037744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037744).length < 2 ^ (prefixWord ++ tailWord_4037744).sum := by decide
  have hdescent : baseEnd_4037744 < baseStart_4037744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037761 : List Nat := [1, 2, 4, 2, 2, 2, 1, 9]
def baseStart_4037761 : Nat := 118140960795 + 4037761 * 2 ^ 59
def prefixEnd_4037761 : Nat := 4983230072969 + 3 ^ 40 * 4037761 * 2
def baseEnd_4037761 : Nat := 76789339295514147230303

theorem tailTrace_4037761 : CollatzResearch.WordTrace tailWord_4037761 prefixEnd_4037761 76789339295514147230303 := by
  unfold tailWord_4037761
  simp only [CollatzResearch.WordTrace]
  refine ⟨147269242324888966522473137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98179494883259311014982091 147269242324888966522473137)
  ·
    refine ⟨110451931743666724891854853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147269242324888966522473137 110451931743666724891854853)
    ·
      refine ⟨20709737201937510917222785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110451931743666724891854853 20709737201937510917222785)
      ·
        refine ⟨15532302901453133187917089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20709737201937510917222785 15532302901453133187917089)
        ·
          refine ⟨11649227176089849890937817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15532302901453133187917089 11649227176089849890937817)
          ·
            refine ⟨8736920382067387418203363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11649227176089849890937817 8736920382067387418203363)
            ·
              refine ⟨13105380573101081127305045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736920382067387418203363 13105380573101081127305045)
              ·
                refine ⟨76789339295514147230303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13105380573101081127305045 76789339295514147230303)
                ·
                  rfl

theorem cell23_4037761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 9].length) (baseStart_4037761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037761 prefixEnd_4037761 := by exact prefixLift 4037761
  have htrace : WordTrace (prefixWord ++ tailWord_4037761) baseStart_4037761 baseEnd_4037761 := by
    simpa [prefixWord, tailWord_4037761, baseEnd_4037761] using wordTrace_append hprefix tailTrace_4037761
  have hstable : (prefixWord ++ tailWord_4037761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037761).length < 2 ^ (prefixWord ++ tailWord_4037761).sum := by decide
  have hdescent : baseEnd_4037761 < baseStart_4037761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037771 : List Nat := [1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3]
def baseStart_4037771 : Nat := 118140960795 + 4037771 * 2 ^ 59
def prefixEnd_4037771 : Nat := 4983230072969 + 3 ^ 40 * 4037771 * 2
def baseEnd_4037771 : Nat := 2073317295785426936093135

theorem tailTrace_4037771 : CollatzResearch.WordTrace tailWord_4037771 prefixEnd_4037771 2073317295785426936093135 := by
  unfold tailWord_4037771
  simp only [CollatzResearch.WordTrace]
  refine ⟨147269607054852738230337167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98179738036568492153558111 147269607054852738230337167)
  ·
    refine ⟨220904410582279107345505751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147269607054852738230337167 220904410582279107345505751)
    ·
      refine ⟨331356615873418661018258627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220904410582279107345505751 331356615873418661018258627)
      ·
        refine ⟨497034923810127991527387941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331356615873418661018258627 497034923810127991527387941)
        ·
          refine ⟨93194048214398998411385239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497034923810127991527387941 93194048214398998411385239)
          ·
            refine ⟨139791072321598497617077859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93194048214398998411385239 139791072321598497617077859)
            ·
              refine ⟨209686608482397746425616789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139791072321598497617077859 209686608482397746425616789)
              ·
                refine ⟨9829059772612394363700787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209686608482397746425616789 9829059772612394363700787)
                ·
                  refine ⟨14743589658918591545551181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829059772612394363700787 14743589658918591545551181)
                  ·
                    refine ⟨5528846122094471829581693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14743589658918591545551181 5528846122094471829581693)
                    ·
                      refine ⟨2073317295785426936093135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528846122094471829581693 2073317295785426936093135)
                      ·
                        rfl

theorem cell23_4037771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3].length) (baseStart_4037771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037771 prefixEnd_4037771 := by exact prefixLift 4037771
  have htrace : WordTrace (prefixWord ++ tailWord_4037771) baseStart_4037771 baseEnd_4037771 := by
    simpa [prefixWord, tailWord_4037771, baseEnd_4037771] using wordTrace_append hprefix tailTrace_4037771
  have hstable : (prefixWord ++ tailWord_4037771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037771).length < 2 ^ (prefixWord ++ tailWord_4037771).sum := by decide
  have hdescent : baseEnd_4037771 < baseStart_4037771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037789 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_4037789 : Nat := 118140960795 + 4037789 * 2 ^ 59
def prefixEnd_4037789 : Nat := 4983230072969 + 3 ^ 40 * 4037789 * 2
def baseEnd_4037789 : Nat := 2073326538437207865668053

theorem tailTrace_4037789 : CollatzResearch.WordTrace tailWord_4037789 prefixEnd_4037789 2073326538437207865668053 := by
  unfold tailWord_4037789
  simp only [CollatzResearch.WordTrace]
  refine ⟨147270263568787527304492421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98180175712525018202994947 147270263568787527304492421)
  ·
    refine ⟨27613174419147661369592329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147270263568787527304492421 27613174419147661369592329)
    ·
      refine ⟨20709880814360746027194247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27613174419147661369592329 20709880814360746027194247)
      ·
        refine ⟨31064821221541119040791371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20709880814360746027194247 31064821221541119040791371)
        ·
          refine ⟨46597231832311678561187057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31064821221541119040791371 46597231832311678561187057)
          ·
            refine ⟨34947923874233758920890293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46597231832311678561187057 34947923874233758920890293)
            ·
              refine ⟨3276367863209414898833465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34947923874233758920890293 3276367863209414898833465)
              ·
                refine ⟨2457275897407061174125099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276367863209414898833465 2457275897407061174125099)
                ·
                  refine ⟨3685913846110591761187649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457275897407061174125099 3685913846110591761187649)
                  ·
                    refine ⟨2764435384582943820890737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3685913846110591761187649 2764435384582943820890737)
                    ·
                      refine ⟨2073326538437207865668053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764435384582943820890737 2073326538437207865668053)
                      ·
                        rfl

theorem cell23_4037789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_4037789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037789 prefixEnd_4037789 := by exact prefixLift 4037789
  have htrace : WordTrace (prefixWord ++ tailWord_4037789) baseStart_4037789 baseEnd_4037789 := by
    simpa [prefixWord, tailWord_4037789, baseEnd_4037789] using wordTrace_append hprefix tailTrace_4037789
  have hstable : (prefixWord ++ tailWord_4037789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037789).length < 2 ^ (prefixWord ++ tailWord_4037789).sum := by decide
  have hdescent : baseEnd_4037789 < baseStart_4037789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037826 : List Nat := [3, 5, 1, 1, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4037826 : Nat := 118140960795 + 4037826 * 2 ^ 59
def prefixEnd_4037826 : Nat := 4983230072969 + 3 ^ 40 * 4037826 * 2
def baseEnd_4037826 : Nat := 2073345537221424220905383

theorem tailTrace_4037826 : CollatzResearch.WordTrace tailWord_4037826 prefixEnd_4037826 2073345537221424220905383 := by
  unfold tailWord_4037826
  simp only [CollatzResearch.WordTrace]
  refine ⟨36817903267413370655897333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98181075379768988415726221 36817903267413370655897333)
  ·
    refine ⟨3451678431320003498990375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36817903267413370655897333 3451678431320003498990375)
    ·
      refine ⟨5177517646980005248485563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451678431320003498990375 5177517646980005248485563)
      ·
        refine ⟨7766276470470007872728345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177517646980005248485563 7766276470470007872728345)
        ·
          refine ⟨5824707352852505904546259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7766276470470007872728345 5824707352852505904546259)
          ·
            refine ⟨8737061029278758856819389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824707352852505904546259 8737061029278758856819389)
            ·
              refine ⟨3276397885979534571307271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8737061029278758856819389 3276397885979534571307271)
              ·
                refine ⟨4914596828969301856960907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276397885979534571307271 4914596828969301856960907)
                ·
                  refine ⟨7371895243453952785441361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914596828969301856960907 7371895243453952785441361)
                  ·
                    refine ⟨5528921432590464589081021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371895243453952785441361 5528921432590464589081021)
                    ·
                      refine ⟨2073345537221424220905383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528921432590464589081021 2073345537221424220905383)
                      ·
                        rfl

theorem cell23_4037826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4037826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037826 prefixEnd_4037826 := by exact prefixLift 4037826
  have htrace : WordTrace (prefixWord ++ tailWord_4037826) baseStart_4037826 baseEnd_4037826 := by
    simpa [prefixWord, tailWord_4037826, baseEnd_4037826] using wordTrace_append hprefix tailTrace_4037826
  have hstable : (prefixWord ++ tailWord_4037826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037826).length < 2 ^ (prefixWord ++ tailWord_4037826).sum := by decide
  have hdescent : baseEnd_4037826 < baseStart_4037826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037831 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_4037831 : Nat := 118140960795 + 4037831 * 2 ^ 59
def prefixEnd_4037831 : Nat := 4983230072969 + 3 ^ 40 * 4037831 * 2
def baseEnd_4037831 : Nat := 2073348104624696701342859

theorem tailTrace_4037831 : CollatzResearch.WordTrace tailWord_4037831 prefixEnd_4037831 2073348104624696701342859 := by
  unfold tailWord_4037831
  simp only [CollatzResearch.WordTrace]
  refine ⟨147271795434635368477521347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98181196956423578985014231 147271795434635368477521347)
  ·
    refine ⟨220907693151953052716282021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147271795434635368477521347 220907693151953052716282021)
    ·
      refine ⟨41420192465991197384302879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220907693151953052716282021 41420192465991197384302879)
      ·
        refine ⟨62130288698986796076454319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41420192465991197384302879 62130288698986796076454319)
        ·
          refine ⟨93195433048480194114681479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62130288698986796076454319 93195433048480194114681479)
          ·
            refine ⟨139793149572720291172022219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93195433048480194114681479 139793149572720291172022219)
            ·
              refine ⟨209689724359080436758033329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139793149572720291172022219 209689724359080436758033329)
              ·
                refine ⟨157267293269310327568524997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209689724359080436758033329 157267293269310327568524997)
                ·
                  refine ⟨29487617487995686419098437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157267293269310327568524997 29487617487995686419098437)
                  ·
                    refine ⟨5528928278999191203580957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29487617487995686419098437 5528928278999191203580957)
                    ·
                      refine ⟨2073348104624696701342859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528928278999191203580957 2073348104624696701342859)
                      ·
                        rfl

theorem cell23_4037831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_4037831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037831 prefixEnd_4037831 := by exact prefixLift 4037831
  have htrace : WordTrace (prefixWord ++ tailWord_4037831) baseStart_4037831 baseEnd_4037831 := by
    simpa [prefixWord, tailWord_4037831, baseEnd_4037831] using wordTrace_append hprefix tailTrace_4037831
  have hstable : (prefixWord ++ tailWord_4037831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037831).length < 2 ^ (prefixWord ++ tailWord_4037831).sum := by decide
  have hdescent : baseEnd_4037831 < baseStart_4037831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037841 : List Nat := [1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_4037841 : Nat := 118140960795 + 4037841 * 2 ^ 59
def prefixEnd_4037841 : Nat := 4983230072969 + 3 ^ 40 * 4037841 * 2
def baseEnd_4037841 : Nat := 2073353239431241662217813

theorem tailTrace_4037841 : CollatzResearch.WordTrace tailWord_4037841 prefixEnd_4037841 2073353239431241662217813 := by
  unfold tailWord_4037841
  simp only [CollatzResearch.WordTrace]
  refine ⟨147272160164599140185385377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98181440109732760123590251 147272160164599140185385377)
  ·
    refine ⟨110454120123449355139039033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147272160164599140185385377 110454120123449355139039033)
    ·
      refine ⟨82840590092587016354279275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110454120123449355139039033 82840590092587016354279275)
      ·
        refine ⟨124260885138880524531418913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82840590092587016354279275 124260885138880524531418913)
        ·
          refine ⟨93195663854160393398564185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124260885138880524531418913 93195663854160393398564185)
          ·
            refine ⟨69896747890620295048923139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93195663854160393398564185 69896747890620295048923139)
            ·
              refine ⟨104845121835930442573384709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69896747890620295048923139 104845121835930442573384709)
              ·
                refine ⟨19658460344236957982509633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104845121835930442573384709 19658460344236957982509633)
                ·
                  refine ⟨14743845258177718486882225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19658460344236957982509633 14743845258177718486882225)
                  ·
                    refine ⟨11057883943633288865161669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14743845258177718486882225 11057883943633288865161669)
                    ·
                      refine ⟨2073353239431241662217813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11057883943633288865161669 2073353239431241662217813)
                      ·
                        rfl

theorem cell23_4037841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_4037841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037841 prefixEnd_4037841 := by exact prefixLift 4037841
  have htrace : WordTrace (prefixWord ++ tailWord_4037841) baseStart_4037841 baseEnd_4037841 := by
    simpa [prefixWord, tailWord_4037841, baseEnd_4037841] using wordTrace_append hprefix tailTrace_4037841
  have hstable : (prefixWord ++ tailWord_4037841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037841).length < 2 ^ (prefixWord ++ tailWord_4037841).sum := by decide
  have hdescent : baseEnd_4037841 < baseStart_4037841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037878 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4037878 : Nat := 118140960795 + 4037878 * 2 ^ 59
def prefixEnd_4037878 : Nat := 4983230072969 + 3 ^ 40 * 4037878 * 2
def baseEnd_4037878 : Nat := 2073372238215458017455143

theorem tailTrace_4037878 : CollatzResearch.WordTrace tailWord_4037878 prefixEnd_4037878 2073372238215458017455143 := by
  unfold tailWord_4037878
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204594354091568469030143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98182339776976730336321525 9204594354091568469030143)
  ·
    refine ⟨13806891531137352703545215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9204594354091568469030143 13806891531137352703545215)
    ·
      refine ⟨20710337296706029055317823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13806891531137352703545215 20710337296706029055317823)
      ·
        refine ⟨31065505945059043582976735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20710337296706029055317823 31065505945059043582976735)
        ·
          refine ⟨46598258917588565374465103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31065505945059043582976735 46598258917588565374465103)
          ·
            refine ⟨69897388376382848061697655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46598258917588565374465103 69897388376382848061697655)
            ·
              refine ⟨104846082564574272092546483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69897388376382848061697655 104846082564574272092546483)
              ·
                refine ⟨157269123846861408138819725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104846082564574272092546483 157269123846861408138819725)
                ·
                  refine ⟨58975921442573028052057397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157269123846861408138819725 58975921442573028052057397)
                  ·
                    refine ⟨5528992635241221379880381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58975921442573028052057397 5528992635241221379880381)
                    ·
                      refine ⟨2073372238215458017455143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5528992635241221379880381 2073372238215458017455143)
                      ·
                        rfl

theorem cell23_4037878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4037878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037878 prefixEnd_4037878 := by exact prefixLift 4037878
  have htrace : WordTrace (prefixWord ++ tailWord_4037878) baseStart_4037878 baseEnd_4037878 := by
    simpa [prefixWord, tailWord_4037878, baseEnd_4037878] using wordTrace_append hprefix tailTrace_4037878
  have hstable : (prefixWord ++ tailWord_4037878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037878).length < 2 ^ (prefixWord ++ tailWord_4037878).sum := by decide
  have hdescent : baseEnd_4037878 < baseStart_4037878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037881 : List Nat := [1, 2, 1, 3, 1, 1, 5, 1, 1, 7]
def baseStart_4037881 : Nat := 118140960795 + 4037881 * 2 ^ 59
def prefixEnd_4037881 : Nat := 4983230072969 + 3 ^ 40 * 4037881 * 2
def baseEnd_4037881 : Nat := 691124592885807168572543

theorem tailTrace_4037881 : CollatzResearch.WordTrace tailWord_4037881 prefixEnd_4037881 691124592885807168572543 := by
  unfold tailWord_4037881
  simp only [CollatzResearch.WordTrace]
  refine ⟨147273619084454227016841497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98182412722969484677894331 147273619084454227016841497)
  ·
    refine ⟨110455214313340670262631123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147273619084454227016841497 110455214313340670262631123)
    ·
      refine ⟨165682821470011005393946685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110455214313340670262631123 165682821470011005393946685)
      ·
        refine ⟨62131058051254127022730007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165682821470011005393946685 62131058051254127022730007)
        ·
          refine ⟨93196587076881190534095011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62131058051254127022730007 93196587076881190534095011)
          ·
            refine ⟨139794880615321785801142517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93196587076881190534095011 139794880615321785801142517)
            ·
              refine ⟨13105770057686417418857111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139794880615321785801142517 13105770057686417418857111)
              ·
                refine ⟨19658655086529626128285667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13105770057686417418857111 19658655086529626128285667)
                ·
                  refine ⟨29487982629794439192428501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19658655086529626128285667 29487982629794439192428501)
                  ·
                    refine ⟨691124592885807168572543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29487982629794439192428501 691124592885807168572543)
                    ·
                      rfl

theorem cell23_4037881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 7].length) (baseStart_4037881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037881 prefixEnd_4037881 := by exact prefixLift 4037881
  have htrace : WordTrace (prefixWord ++ tailWord_4037881) baseStart_4037881 baseEnd_4037881 := by
    simpa [prefixWord, tailWord_4037881, baseEnd_4037881] using wordTrace_append hprefix tailTrace_4037881
  have hstable : (prefixWord ++ tailWord_4037881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037881).length < 2 ^ (prefixWord ++ tailWord_4037881).sum := by decide
  have hdescent : baseEnd_4037881 < baseStart_4037881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037896 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_4037896 : Nat := 118140960795 + 4037896 * 2 ^ 59
def prefixEnd_4037896 : Nat := 4983230072969 + 3 ^ 40 * 4037896 * 2
def baseEnd_4037896 : Nat := 2073381480867238947030061

theorem tailTrace_4037896 : CollatzResearch.WordTrace tailWord_4037896 prefixEnd_4037896 2073381480867238947030061 := by
  unfold tailWord_4037896
  simp only [CollatzResearch.WordTrace]
  refine ⟨73637083089699942289318771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98182777452933256385758361 73637083089699942289318771)
  ·
    refine ⟨110455624634549913433978157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73637083089699942289318771 110455624634549913433978157)
    ·
      refine ⟨41420859237956217537741809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110455624634549913433978157 41420859237956217537741809)
      ·
        refine ⟨31065644428467163153306357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41420859237956217537741809 31065644428467163153306357)
        ·
          refine ⟨2912404165168796545622471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31065644428467163153306357 2912404165168796545622471)
          ·
            refine ⟨4368606247753194818433707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912404165168796545622471 4368606247753194818433707)
            ·
              refine ⟨6552909371629792227650561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368606247753194818433707 6552909371629792227650561)
              ·
                refine ⟨4914682028722344170737921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552909371629792227650561 4914682028722344170737921)
                ·
                  refine ⟨3686011521541758128053441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4914682028722344170737921 3686011521541758128053441)
                  ·
                    refine ⟨2764508641156318596040081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686011521541758128053441 2764508641156318596040081)
                    ·
                      refine ⟨2073381480867238947030061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764508641156318596040081 2073381480867238947030061)
                      ·
                        rfl

theorem cell23_4037896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_4037896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037896 prefixEnd_4037896 := by exact prefixLift 4037896
  have htrace : WordTrace (prefixWord ++ tailWord_4037896) baseStart_4037896 baseEnd_4037896 := by
    simpa [prefixWord, tailWord_4037896, baseEnd_4037896] using wordTrace_append hprefix tailTrace_4037896
  have hstable : (prefixWord ++ tailWord_4037896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037896).length < 2 ^ (prefixWord ++ tailWord_4037896).sum := by decide
  have hdescent : baseEnd_4037896 < baseStart_4037896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037961 : List Nat := [1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 8]
def baseStart_4037961 : Nat := 118140960795 + 4037961 * 2 ^ 59
def prefixEnd_4037961 : Nat := 4983230072969 + 3 ^ 40 * 4037961 * 2
def baseEnd_4037961 : Nat := 2073414857109781192717261

theorem tailTrace_4037961 : CollatzResearch.WordTrace tailWord_4037961 prefixEnd_4037961 2073414857109781192717261 := by
  unfold tailWord_4037961
  simp only [CollatzResearch.WordTrace]
  refine ⟨147276536924164400679753737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98184357949442933786502491 147276536924164400679753737)
  ·
    refine ⟨110457402693123300509815303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147276536924164400679753737 110457402693123300509815303)
    ·
      refine ⟨165686104039684950764722955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110457402693123300509815303 165686104039684950764722955)
      ·
        refine ⟨248529156059527426147084433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165686104039684950764722955 248529156059527426147084433)
        ·
          refine ⟨186396867044645569610313325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248529156059527426147084433 186396867044645569610313325)
          ·
            refine ⟨69898825141742088603867497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186396867044645569610313325 69898825141742088603867497)
            ·
              refine ⟨52424118856306566452900623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69898825141742088603867497 52424118856306566452900623)
              ·
                refine ⟨78636178284459849679350935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52424118856306566452900623 78636178284459849679350935)
                ·
                  refine ⟨117954267426689774519026403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78636178284459849679350935 117954267426689774519026403)
                  ·
                    refine ⟨176931401140034661778539605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117954267426689774519026403 176931401140034661778539605)
                    ·
                      refine ⟨2073414857109781192717261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 176931401140034661778539605 2073414857109781192717261)
                      ·
                        rfl

theorem cell23_4037961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 1, 8].length) (baseStart_4037961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037961 prefixEnd_4037961 := by exact prefixLift 4037961
  have htrace : WordTrace (prefixWord ++ tailWord_4037961) baseStart_4037961 baseEnd_4037961 := by
    simpa [prefixWord, tailWord_4037961, baseEnd_4037961] using wordTrace_append hprefix tailTrace_4037961
  have hstable : (prefixWord ++ tailWord_4037961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037961).length < 2 ^ (prefixWord ++ tailWord_4037961).sum := by decide
  have hdescent : baseEnd_4037961 < baseStart_4037961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037975 : List Nat := [1, 1, 3, 2, 3, 2, 4, 1, 6]
def baseStart_4037975 : Nat := 118140960795 + 4037975 * 2 ^ 59
def prefixEnd_4037975 : Nat := 4983230072969 + 3 ^ 40 * 4037975 * 2
def baseEnd_4037975 : Nat := 230380227315438237549133

theorem tailTrace_4037975 : CollatzResearch.WordTrace tailWord_4037975 prefixEnd_4037975 230380227315438237549133 := by
  unfold tailWord_4037975
  simp only [CollatzResearch.WordTrace]
  refine ⟨147277047546113681070763379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98184698364075787380508919 147277047546113681070763379)
  ·
    refine ⟨220915571319170521606145069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147277047546113681070763379 220915571319170521606145069)
    ·
      refine ⟨82843339244688945602304401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220915571319170521606145069 82843339244688945602304401)
      ·
        refine ⟨62132504433516709201728301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82843339244688945602304401 62132504433516709201728301)
        ·
          refine ⟨23299689162568765950648113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62132504433516709201728301 23299689162568765950648113)
          ·
            refine ⟨17474766871926574462986085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23299689162568765950648113 17474766871926574462986085)
            ·
              refine ⟨3276518788486232711809891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17474766871926574462986085 3276518788486232711809891)
              ·
                refine ⟨4914778182729349067714837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276518788486232711809891 4914778182729349067714837)
                ·
                  refine ⟨230380227315438237549133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4914778182729349067714837 230380227315438237549133)
                  ·
                    rfl

theorem cell23_4037975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 6].length) (baseStart_4037975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037975 prefixEnd_4037975 := by exact prefixLift 4037975
  have htrace : WordTrace (prefixWord ++ tailWord_4037975) baseStart_4037975 baseEnd_4037975 := by
    simpa [prefixWord, tailWord_4037975, baseEnd_4037975] using wordTrace_append hprefix tailTrace_4037975
  have hstable : (prefixWord ++ tailWord_4037975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037975).length < 2 ^ (prefixWord ++ tailWord_4037975).sum := by decide
  have hdescent : baseEnd_4037975 < baseStart_4037975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4037985 : List Nat := [1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_4037985 : Nat := 118140960795 + 4037985 * 2 ^ 59
def prefixEnd_4037985 : Nat := 4983230072969 + 3 ^ 40 * 4037985 * 2
def baseEnd_4037985 : Nat := 2073427180645489098817151

theorem tailTrace_4037985 : CollatzResearch.WordTrace tailWord_4037985 prefixEnd_4037985 2073427180645489098817151 := by
  unfold tailWord_4037985
  simp only [CollatzResearch.WordTrace]
  refine ⟨147277412276077452778627409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98184941517384968519084939 147277412276077452778627409)
  ·
    refine ⟨110458059207058089583970557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147277412276077452778627409 110458059207058089583970557)
    ·
      refine ⟨41421772202646783593988959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110458059207058089583970557 41421772202646783593988959)
      ·
        refine ⟨62132658303970175390983439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41421772202646783593988959 62132658303970175390983439)
        ·
          refine ⟨93198987455955263086475159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62132658303970175390983439 93198987455955263086475159)
          ·
            refine ⟨139798481183932894629712739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93198987455955263086475159 139798481183932894629712739)
            ·
              refine ⟨209697721775899341944569109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139798481183932894629712739 209697721775899341944569109)
              ·
                refine ⟨9829580708245281653651677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 209697721775899341944569109 9829580708245281653651677)
                ·
                  refine ⟨3686092765591980620119379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9829580708245281653651677 3686092765591980620119379)
                  ·
                    refine ⟨5529139148387970930179069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3686092765591980620119379 5529139148387970930179069)
                    ·
                      refine ⟨2073427180645489098817151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5529139148387970930179069 2073427180645489098817151)
                      ·
                        rfl

theorem cell23_4037985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_4037985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4037985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4037985 prefixEnd_4037985 := by exact prefixLift 4037985
  have htrace : WordTrace (prefixWord ++ tailWord_4037985) baseStart_4037985 baseEnd_4037985 := by
    simpa [prefixWord, tailWord_4037985, baseEnd_4037985] using wordTrace_append hprefix tailTrace_4037985
  have hstable : (prefixWord ++ tailWord_4037985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4037985).length < 2 ^ (prefixWord ++ tailWord_4037985).sum := by decide
  have hdescent : baseEnd_4037985 < baseStart_4037985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4037985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038019 : List Nat := [1, 1, 1, 3, 5, 2, 1, 4, 1, 1, 3]
def baseStart_4038019 : Nat := 118140960795 + 4038019 * 2 ^ 59
def prefixEnd_4038019 : Nat := 4983230072969 + 3 ^ 40 * 4038019 * 2
def baseEnd_4038019 : Nat := 2073444638987741965791995

theorem tailTrace_4038019 : CollatzResearch.WordTrace tailWord_4038019 prefixEnd_4038019 2073444638987741965791995 := by
  unfold tailWord_4038019
  simp only [CollatzResearch.WordTrace]
  refine ⟨147278652357954276585365111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98185768238636184390243407 147278652357954276585365111)
  ·
    refine ⟨220917978536931414878047667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147278652357954276585365111 220917978536931414878047667)
    ·
      refine ⟨331376967805397122317071501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220917978536931414878047667 331376967805397122317071501)
      ·
        refine ⟨124266362927023920868901813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331376967805397122317071501 124266362927023920868901813)
        ·
          refine ⟨11649971524408492581459545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124266362927023920868901813 11649971524408492581459545)
          ·
            refine ⟨8737478643306369436094659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11649971524408492581459545 8737478643306369436094659)
            ·
              refine ⟨13106217964959554154141989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8737478643306369436094659 13106217964959554154141989)
              ·
                refine ⟨2457415868429916403901623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13106217964959554154141989 2457415868429916403901623)
                ·
                  refine ⟨3686123802644874605852435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457415868429916403901623 3686123802644874605852435)
                  ·
                    refine ⟨5529185703967311908778653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3686123802644874605852435 5529185703967311908778653)
                    ·
                      refine ⟨2073444638987741965791995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5529185703967311908778653 2073444638987741965791995)
                      ·
                        rfl

theorem cell23_4038019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 4, 1, 1, 3].length) (baseStart_4038019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038019 prefixEnd_4038019 := by exact prefixLift 4038019
  have htrace : WordTrace (prefixWord ++ tailWord_4038019) baseStart_4038019 baseEnd_4038019 := by
    simpa [prefixWord, tailWord_4038019, baseEnd_4038019] using wordTrace_append hprefix tailTrace_4038019
  have hstable : (prefixWord ++ tailWord_4038019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038019).length < 2 ^ (prefixWord ++ tailWord_4038019).sum := by decide
  have hdescent : baseEnd_4038019 < baseStart_4038019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038028 : List Nat := [2, 2, 1, 2, 1, 3, 2, 1, 3, 1, 5]
def baseStart_4038028 : Nat := 118140960795 + 4038028 * 2 ^ 59
def prefixEnd_4038028 : Nat := 4983230072969 + 3 ^ 40 * 4038028 * 2
def baseEnd_4038028 : Nat := 2073449260313632430579453

theorem tailTrace_4038028 : CollatzResearch.WordTrace tailWord_4038028 prefixEnd_4038028 2073449260313632430579453 := by
  unfold tailWord_4038028
  simp only [CollatzResearch.WordTrace]
  refine ⟨73639490307460835561221369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98185987076614447414961825 73639490307460835561221369)
  ·
    refine ⟨55229617730595626670916027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73639490307460835561221369 55229617730595626670916027)
    ·
      refine ⟨82844426595893440006374041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55229617730595626670916027 82844426595893440006374041)
      ·
        refine ⟨62133319946920080004780531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82844426595893440006374041 62133319946920080004780531)
        ·
          refine ⟨93199979920380120007170797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62133319946920080004780531 93199979920380120007170797)
          ·
            refine ⟨34949992470142545002689049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93199979920380120007170797 34949992470142545002689049)
            ·
              refine ⟨26212494352606908752016787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34949992470142545002689049 26212494352606908752016787)
              ·
                refine ⟨39318741528910363128025181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26212494352606908752016787 39318741528910363128025181)
                ·
                  refine ⟨14744528073341386173009443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39318741528910363128025181 14744528073341386173009443)
                  ·
                    refine ⟨22116792110012079259514165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14744528073341386173009443 22116792110012079259514165)
                    ·
                      refine ⟨2073449260313632430579453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22116792110012079259514165 2073449260313632430579453)
                      ·
                        rfl

theorem cell23_4038028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_4038028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038028 prefixEnd_4038028 := by exact prefixLift 4038028
  have htrace : WordTrace (prefixWord ++ tailWord_4038028) baseStart_4038028 baseEnd_4038028 := by
    simpa [prefixWord, tailWord_4038028, baseEnd_4038028] using wordTrace_append hprefix tailTrace_4038028
  have hstable : (prefixWord ++ tailWord_4038028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038028).length < 2 ^ (prefixWord ++ tailWord_4038028).sum := by decide
  have hdescent : baseEnd_4038028 < baseStart_4038028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038055 : List Nat := [1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4038055 : Nat := 118140960795 + 4038055 * 2 ^ 59
def prefixEnd_4038055 : Nat := 4983230072969 + 3 ^ 40 * 4038055 * 2
def baseEnd_4038055 : Nat := 2073463124291303824941829

theorem tailTrace_4038055 : CollatzResearch.WordTrace tailWord_4038055 prefixEnd_4038055 2073463124291303824941829 := by
  unfold tailWord_4038055
  simp only [CollatzResearch.WordTrace]
  refine ⟨147279965385823854733675619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98186643590549236489117079 147279965385823854733675619)
  ·
    refine ⟨220919948078735782100513429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147279965385823854733675619 220919948078735782100513429)
    ·
      refine ⟨10355622566190739785961567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220919948078735782100513429 10355622566190739785961567)
      ·
        refine ⟨15533433849286109678942351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10355622566190739785961567 15533433849286109678942351)
        ·
          refine ⟨23300150773929164518413527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533433849286109678942351 23300150773929164518413527)
          ·
            refine ⟨34950226160893746777620291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23300150773929164518413527 34950226160893746777620291)
            ·
              refine ⟨52425339241340620166430437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34950226160893746777620291 52425339241340620166430437)
              ·
                refine ⟨9829751107751366281205707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52425339241340620166430437 9829751107751366281205707)
                ·
                  refine ⟨14744626661627049421808561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829751107751366281205707 14744626661627049421808561)
                  ·
                    refine ⟨11058469996220287066356421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14744626661627049421808561 11058469996220287066356421)
                    ·
                      refine ⟨2073463124291303824941829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11058469996220287066356421 2073463124291303824941829)
                      ·
                        rfl

theorem cell23_4038055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4038055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038055 prefixEnd_4038055 := by exact prefixLift 4038055
  have htrace : WordTrace (prefixWord ++ tailWord_4038055) baseStart_4038055 baseEnd_4038055 := by
    simpa [prefixWord, tailWord_4038055, baseEnd_4038055] using wordTrace_append hprefix tailTrace_4038055
  have hstable : (prefixWord ++ tailWord_4038055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038055).length < 2 ^ (prefixWord ++ tailWord_4038055).sum := by decide
  have hdescent : baseEnd_4038055 < baseStart_4038055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038056 : List Nat := [2, 1, 6, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4038056 : Nat := 118140960795 + 4038056 * 2 ^ 59
def prefixEnd_4038056 : Nat := 4983230072969 + 3 ^ 40 * 4038056 * 2
def baseEnd_4038056 : Nat := 691154545923986107009775

theorem tailTrace_4038056 : CollatzResearch.WordTrace tailWord_4038056 prefixEnd_4038056 691154545923986107009775 := by
  unfold tailWord_4038056
  simp only [CollatzResearch.WordTrace]
  refine ⟨73640000929410115952231011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98186667905880154602974681 73640000929410115952231011)
  ·
    refine ⟨110460001394115173928346517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73640000929410115952231011 110460001394115173928346517)
    ·
      refine ⟨5177812565349148777891243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110460001394115173928346517 5177812565349148777891243)
      ·
        refine ⟨7766718848023723166836865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177812565349148777891243 7766718848023723166836865)
        ·
          refine ⟨5825039136017792375127649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7766718848023723166836865 5825039136017792375127649)
          ·
            refine ⟨4368779352013344281345737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825039136017792375127649 4368779352013344281345737)
            ·
              refine ⟨3276584514010008211009303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368779352013344281345737 3276584514010008211009303)
              ·
                refine ⟨4914876771015012316513955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276584514010008211009303 4914876771015012316513955)
                ·
                  refine ⟨7372315156522518474770933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914876771015012316513955 7372315156522518474770933)
                  ·
                    refine ⟨691154545923986107009775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7372315156522518474770933 691154545923986107009775)
                    ·
                      rfl

theorem cell23_4038056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4038056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038056 prefixEnd_4038056 := by exact prefixLift 4038056
  have htrace : WordTrace (prefixWord ++ tailWord_4038056) baseStart_4038056 baseEnd_4038056 := by
    simpa [prefixWord, tailWord_4038056, baseEnd_4038056] using wordTrace_append hprefix tailTrace_4038056
  have hstable : (prefixWord ++ tailWord_4038056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038056).length < 2 ^ (prefixWord ++ tailWord_4038056).sum := by decide
  have hdescent : baseEnd_4038056 < baseStart_4038056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038069 : List Nat := [1, 3, 3, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4038069 : Nat := 118140960795 + 4038069 * 2 ^ 59
def prefixEnd_4038069 : Nat := 4983230072969 + 3 ^ 40 * 4038069 * 2
def baseEnd_4038069 : Nat := 691156771006822256722255

theorem tailTrace_4038069 : CollatzResearch.WordTrace tailWord_4038069 prefixEnd_4038069 691156771006822256722255 := by
  unfold tailWord_4038069
  simp only [CollatzResearch.WordTrace]
  refine ⟨147280476007773135124685261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98186984005182090083123507 147280476007773135124685261)
  ·
    refine ⟨55230178502914925671756973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147280476007773135124685261 55230178502914925671756973)
    ·
      refine ⟨20711316938593097126908865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55230178502914925671756973 20711316938593097126908865)
      ·
        refine ⟨15533487703944822845181649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20711316938593097126908865 15533487703944822845181649)
        ·
          refine ⟨11650115777958617133886237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15533487703944822845181649 11650115777958617133886237)
          ·
            refine ⟨4368793416734481425207339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11650115777958617133886237 4368793416734481425207339)
            ·
              refine ⟨6553190125101722137811009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368793416734481425207339 6553190125101722137811009)
              ·
                refine ⟨4914892593826291603358257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553190125101722137811009 4914892593826291603358257)
                ·
                  refine ⟨3686169445369718702518693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4914892593826291603358257 3686169445369718702518693)
                  ·
                    refine ⟨691156771006822256722255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686169445369718702518693 691156771006822256722255)
                    ·
                      rfl

theorem cell23_4038069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4038069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038069 prefixEnd_4038069 := by exact prefixLift 4038069
  have htrace : WordTrace (prefixWord ++ tailWord_4038069) baseStart_4038069 baseEnd_4038069 := by
    simpa [prefixWord, tailWord_4038069, baseEnd_4038069] using wordTrace_append hprefix tailTrace_4038069
  have hstable : (prefixWord ++ tailWord_4038069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038069).length < 2 ^ (prefixWord ++ tailWord_4038069).sum := by decide
  have hdescent : baseEnd_4038069 < baseStart_4038069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038076 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 3, 2, 2]
def baseStart_4038076 : Nat := 118140960795 + 4038076 * 2 ^ 59
def prefixEnd_4038076 : Nat := 4983230072969 + 3 ^ 40 * 4038076 * 2
def baseEnd_4038076 : Nat := 2073473907385048242779233

theorem tailTrace_4038076 : CollatzResearch.WordTrace tailWord_4038076 prefixEnd_4038076 2073473907385048242779233 := by
  unfold tailWord_4038076
  simp only [CollatzResearch.WordTrace]
  refine ⟨73640365659373887660095041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98187154212498516880126721 73640365659373887660095041)
  ·
    refine ⟨55230274244530415745071281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73640365659373887660095041 55230274244530415745071281)
    ·
      refine ⟨41422705683397811808803461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55230274244530415745071281 41422705683397811808803461)
      ·
        refine ⟨7766757315637089714150649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41422705683397811808803461 7766757315637089714150649)
        ·
          refine ⟨5825067986727817285612987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7766757315637089714150649 5825067986727817285612987)
          ·
            refine ⟨8737601980091725928419481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825067986727817285612987 8737601980091725928419481)
            ·
              refine ⟨6553201485068794446314611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8737601980091725928419481 6553201485068794446314611)
              ·
                refine ⟨9829802227603191669471917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553201485068794446314611 9829802227603191669471917)
                ·
                  refine ⟨3686175835351196876051969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9829802227603191669471917 3686175835351196876051969)
                  ·
                    refine ⟨2764631876513397657038977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686175835351196876051969 2764631876513397657038977)
                    ·
                      refine ⟨2073473907385048242779233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764631876513397657038977 2073473907385048242779233)
                      ·
                        rfl

theorem cell23_4038076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_4038076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038076 prefixEnd_4038076 := by exact prefixLift 4038076
  have htrace : WordTrace (prefixWord ++ tailWord_4038076) baseStart_4038076 baseEnd_4038076 := by
    simpa [prefixWord, tailWord_4038076, baseEnd_4038076] using wordTrace_append hprefix tailTrace_4038076
  have hstable : (prefixWord ++ tailWord_4038076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038076).length < 2 ^ (prefixWord ++ tailWord_4038076).sum := by decide
  have hdescent : baseEnd_4038076 < baseStart_4038076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038092 : List Nat := [2, 2, 1, 4, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4038092 : Nat := 118140960795 + 4038092 * 2 ^ 59
def prefixEnd_4038092 : Nat := 4983230072969 + 3 ^ 40 * 4038092 * 2
def baseEnd_4038092 : Nat := 2073482123075520180179159

theorem tailTrace_4038092 : CollatzResearch.WordTrace tailWord_4038092 prefixEnd_4038092 2073482123075520180179159 := by
  unfold tailWord_4038092
  simp only [CollatzResearch.WordTrace]
  refine ⟨73640657443344905026386265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98187543257793206701848353 73640657443344905026386265)
  ·
    refine ⟨55230493082508678769789699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73640657443344905026386265 55230493082508678769789699)
    ·
      refine ⟨82845739623763018154684549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55230493082508678769789699 82845739623763018154684549)
      ·
        refine ⟨15533576179455565904003353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82845739623763018154684549 15533576179455565904003353)
        ·
          refine ⟨11650182134591674428002515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15533576179455565904003353 11650182134591674428002515)
          ·
            refine ⟨17475273201887511642003773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650182134591674428002515 17475273201887511642003773)
            ·
              refine ⟨6553227450707816865751415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17475273201887511642003773 6553227450707816865751415)
              ·
                refine ⟨9829841176061725298627123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553227450707816865751415 9829841176061725298627123)
                ·
                  refine ⟨14744761764092587947940685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829841176061725298627123 14744761764092587947940685)
                  ·
                    refine ⟨5529285661534720480477757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14744761764092587947940685 5529285661534720480477757)
                    ·
                      refine ⟨2073482123075520180179159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5529285661534720480477757 2073482123075520180179159)
                      ·
                        rfl

theorem cell23_4038092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4038092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038092 prefixEnd_4038092 := by exact prefixLift 4038092
  have htrace : WordTrace (prefixWord ++ tailWord_4038092) baseStart_4038092 baseEnd_4038092 := by
    simpa [prefixWord, tailWord_4038092, baseEnd_4038092] using wordTrace_append hprefix tailTrace_4038092
  have hstable : (prefixWord ++ tailWord_4038092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038092).length < 2 ^ (prefixWord ++ tailWord_4038092).sum := by decide
  have hdescent : baseEnd_4038092 < baseStart_4038092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038119 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 1, 3, 2]
def baseStart_4038119 : Nat := 118140960795 + 4038119 * 2 ^ 59
def prefixEnd_4038119 : Nat := 4983230072969 + 3 ^ 40 * 4038119 * 2
def baseEnd_4038119 : Nat := 2073495987053191574541535

theorem tailTrace_4038119 : CollatzResearch.WordTrace tailWord_4038119 prefixEnd_4038119 2073495987053191574541535 := by
  unfold tailWord_4038119
  simp only [CollatzResearch.WordTrace]
  refine ⟨147282299657591993664005411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98188199771727995776003607 147282299657591993664005411)
  ·
    refine ⟨220923449486387990496008117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147282299657591993664005411 220923449486387990496008117)
    ·
      refine ⟨20711573389348874109000761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220923449486387990496008117 20711573389348874109000761)
      ·
        refine ⟨15533680042011655581750571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20711573389348874109000761 15533680042011655581750571)
        ·
          refine ⟨23300520063017483372625857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533680042011655581750571 23300520063017483372625857)
          ·
            refine ⟨17475390047263112529469393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23300520063017483372625857 17475390047263112529469393)
            ·
              refine ⟨13106542535447334397102045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17475390047263112529469393 13106542535447334397102045)
              ·
                refine ⟨4914953450792750398913267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13106542535447334397102045 4914953450792750398913267)
                ·
                  refine ⟨7372430176189125598369901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914953450792750398913267 7372430176189125598369901)
                  ·
                    refine ⟨2764661316070922099388713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7372430176189125598369901 2764661316070922099388713)
                    ·
                      refine ⟨2073495987053191574541535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764661316070922099388713 2073495987053191574541535)
                      ·
                        rfl

theorem cell23_4038119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_4038119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038119 prefixEnd_4038119 := by exact prefixLift 4038119
  have htrace : WordTrace (prefixWord ++ tailWord_4038119) baseStart_4038119 baseEnd_4038119 := by
    simpa [prefixWord, tailWord_4038119, baseEnd_4038119] using wordTrace_append hprefix tailTrace_4038119
  have hstable : (prefixWord ++ tailWord_4038119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038119).length < 2 ^ (prefixWord ++ tailWord_4038119).sum := by decide
  have hdescent : baseEnd_4038119 < baseStart_4038119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038172 : List Nat := [2, 2, 3, 1, 2, 1, 2, 5, 5]
def baseStart_4038172 : Nat := 118140960795 + 4038172 * 2 ^ 59
def prefixEnd_4038172 : Nat := 4983230072969 + 3 ^ 40 * 4038172 * 2
def baseEnd_4038172 : Nat := 230391466836431096353199

theorem tailTrace_4038172 : CollatzResearch.WordTrace tailWord_4038172 prefixEnd_4038172 230391466836431096353199 := by
  unfold tailWord_4038172
  simp only [CollatzResearch.WordTrace]
  refine ⟨73642116363199991857842385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98189488484266655810456513 73642116363199991857842385)
  ·
    refine ⟨55231587272399993893381789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73642116363199991857842385 55231587272399993893381789)
    ·
      refine ⟨20711845227149997710018171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55231587272399993893381789 20711845227149997710018171)
      ·
        refine ⟨31067767840724996565027257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20711845227149997710018171 31067767840724996565027257)
        ·
          refine ⟨23300825880543747423770443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31067767840724996565027257 23300825880543747423770443)
          ·
            refine ⟨34951238820815621135655665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23300825880543747423770443 34951238820815621135655665)
            ·
              refine ⟨26213429115611715851741749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34951238820815621135655665 26213429115611715851741749)
              ·
                refine ⟨2457508979588598361100789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26213429115611715851741749 2457508979588598361100789)
                ·
                  refine ⟨230391466836431096353199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2457508979588598361100789 230391466836431096353199)
                  ·
                    rfl

theorem cell23_4038172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 5, 5].length) (baseStart_4038172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038172 prefixEnd_4038172 := by exact prefixLift 4038172
  have htrace : WordTrace (prefixWord ++ tailWord_4038172) baseStart_4038172 baseEnd_4038172 := by
    simpa [prefixWord, tailWord_4038172, baseEnd_4038172] using wordTrace_append hprefix tailTrace_4038172
  have hstable : (prefixWord ++ tailWord_4038172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038172).length < 2 ^ (prefixWord ++ tailWord_4038172).sum := by decide
  have hdescent : baseEnd_4038172 < baseStart_4038172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038195 : List Nat := [1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_4038195 : Nat := 118140960795 + 4038195 * 2 ^ 59
def prefixEnd_4038195 : Nat := 4983230072969 + 3 ^ 40 * 4038195 * 2
def baseEnd_4038195 : Nat := 2073535011582933277191185

theorem tailTrace_4038195 : CollatzResearch.WordTrace tailWord_4038195 prefixEnd_4038195 2073535011582933277191185 := by
  unfold tailWord_4038195
  simp only [CollatzResearch.WordTrace]
  refine ⟨147285071605316658643772039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98190047736877772429181359 147285071605316658643772039)
  ·
    refine ⟨220927607407974987965658059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147285071605316658643772039 220927607407974987965658059)
    ·
      refine ⟨331391411111962481948487089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220927607407974987965658059 331391411111962481948487089)
      ·
        refine ⟨248543558333971861461365317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331391411111962481948487089 248543558333971861461365317)
        ·
          refine ⟨46601917187619724024005997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248543558333971861461365317 46601917187619724024005997)
          ·
            refine ⟨17475718945357396509002249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46601917187619724024005997 17475718945357396509002249)
            ·
              refine ⟨13106789209018047381751687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17475718945357396509002249 13106789209018047381751687)
              ·
                refine ⟨19660183813527071072627531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106789209018047381751687 19660183813527071072627531)
                ·
                  refine ⟨29490275720290606608941297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19660183813527071072627531 29490275720290606608941297)
                  ·
                    refine ⟨22117706790217954956705973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29490275720290606608941297 22117706790217954956705973)
                    ·
                      refine ⟨2073535011582933277191185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22117706790217954956705973 2073535011582933277191185)
                      ·
                        rfl

theorem cell23_4038195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_4038195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038195 prefixEnd_4038195 := by exact prefixLift 4038195
  have htrace : WordTrace (prefixWord ++ tailWord_4038195) baseStart_4038195 baseEnd_4038195 := by
    simpa [prefixWord, tailWord_4038195, baseEnd_4038195] using wordTrace_append hprefix tailTrace_4038195
  have hstable : (prefixWord ++ tailWord_4038195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038195).length < 2 ^ (prefixWord ++ tailWord_4038195).sum := by decide
  have hdescent : baseEnd_4038195 < baseStart_4038195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038222 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2]
def baseStart_4038222 : Nat := 118140960795 + 4038222 * 2 ^ 59
def prefixEnd_4038222 : Nat := 4983230072969 + 3 ^ 40 * 4038222 * 2
def baseEnd_4038222 : Nat := 2073548875560604671553561

theorem tailTrace_4038222 : CollatzResearch.WordTrace tailWord_4038222 prefixEnd_4038222 2073548875560604671553561 := by
  unfold tailWord_4038222
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410757047027355281875615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98190704250812561503336613 18410757047027355281875615)
  ·
    refine ⟨27616135570541032922813423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18410757047027355281875615 27616135570541032922813423)
    ·
      refine ⟨41424203355811549384220135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27616135570541032922813423 41424203355811549384220135)
      ·
        refine ⟨62136305033717324076330203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41424203355811549384220135 62136305033717324076330203)
        ·
          refine ⟨93204457550575986114495305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62136305033717324076330203 93204457550575986114495305)
          ·
            refine ⟨69903343162931989585871479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93204457550575986114495305 69903343162931989585871479)
            ·
              refine ⟨104855014744397984378807219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69903343162931989585871479 104855014744397984378807219)
              ·
                refine ⟨157282522116596976568210829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104855014744397984378807219 157282522116596976568210829)
                ·
                  refine ⟨58980945793723866213079061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157282522116596976568210829 58980945793723866213079061)
                  ·
                    refine ⟨2764731834080806228738081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 58980945793723866213079061 2764731834080806228738081)
                    ·
                      refine ⟨2073548875560604671553561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764731834080806228738081 2073548875560604671553561)
                      ·
                        rfl

theorem cell23_4038222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2].length) (baseStart_4038222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038222 prefixEnd_4038222 := by exact prefixLift 4038222
  have htrace : WordTrace (prefixWord ++ tailWord_4038222) baseStart_4038222 baseEnd_4038222 := by
    simpa [prefixWord, tailWord_4038222, baseEnd_4038222] using wordTrace_append hprefix tailTrace_4038222
  have hstable : (prefixWord ++ tailWord_4038222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038222).length < 2 ^ (prefixWord ++ tailWord_4038222).sum := by decide
  have hdescent : baseEnd_4038222 < baseStart_4038222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038249 : List Nat := [1, 2, 1, 1, 1, 4, 4, 4, 1, 4]
def baseStart_4038249 : Nat := 118140960795 + 4038249 * 2 ^ 59
def prefixEnd_4038249 : Nat := 4983230072969 + 3 ^ 40 * 4038249 * 2
def baseEnd_4038249 : Nat := 691187579846092021971979

theorem tailTrace_4038249 : CollatzResearch.WordTrace tailWord_4038249 prefixEnd_4038249 691187579846092021971979 := by
  unfold tailWord_4038249
  simp only [CollatzResearch.WordTrace]
  refine ⟨147287041147121025866237801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98191360764747350577491867 147287041147121025866237801)
  ·
    refine ⟨110465280860340769399678351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147287041147121025866237801 110465280860340769399678351)
    ·
      refine ⟨165697921290511154099517527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110465280860340769399678351 165697921290511154099517527)
      ·
        refine ⟨248546881935766731149276291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165697921290511154099517527 248546881935766731149276291)
        ·
          refine ⟨372820322903650096723914437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248546881935766731149276291 372820322903650096723914437)
          ·
            refine ⟨69903810544434393135733957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372820322903650096723914437 69903810544434393135733957)
            ·
              refine ⟨13106964477081448712950117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69903810544434393135733957 13106964477081448712950117)
              ·
                refine ⟨2457555839452771633678147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13106964477081448712950117 2457555839452771633678147)
                ·
                  refine ⟨3686333759179157450517221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2457555839452771633678147 3686333759179157450517221)
                  ·
                    refine ⟨691187579846092021971979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686333759179157450517221 691187579846092021971979)
                    ·
                      rfl

theorem cell23_4038249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 4, 1, 4].length) (baseStart_4038249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038249 prefixEnd_4038249 := by exact prefixLift 4038249
  have htrace : WordTrace (prefixWord ++ tailWord_4038249) baseStart_4038249 baseEnd_4038249 := by
    simpa [prefixWord, tailWord_4038249, baseEnd_4038249] using wordTrace_append hprefix tailTrace_4038249
  have hstable : (prefixWord ++ tailWord_4038249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038249).length < 2 ^ (prefixWord ++ tailWord_4038249).sum := by decide
  have hdescent : baseEnd_4038249 < baseStart_4038249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038265 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_4038265 : Nat := 118140960795 + 4038265 * 2 ^ 59
def prefixEnd_4038265 : Nat := 4983230072969 + 3 ^ 40 * 4038265 * 2
def baseEnd_4038265 : Nat := 2073570955228748003315863

theorem tailTrace_4038265 : CollatzResearch.WordTrace tailWord_4038265 prefixEnd_4038265 2073570955228748003315863 := by
  unfold tailWord_4038265
  simp only [CollatzResearch.WordTrace]
  refine ⟨147287624715063060598820249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98191749810042040399213499 147287624715063060598820249)
  ·
    refine ⟨110465718536297295449115187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147287624715063060598820249 110465718536297295449115187)
    ·
      refine ⟨165698577804445943173672781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110465718536297295449115187 165698577804445943173672781)
      ·
        refine ⟨62136966676667228690127293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165698577804445943173672781 62136966676667228690127293)
        ·
          refine ⟨23301362503750210758797735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62136966676667228690127293 23301362503750210758797735)
          ·
            refine ⟨34952043755625316138196603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23301362503750210758797735 34952043755625316138196603)
            ·
              refine ⟨52428065633437974207294905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34952043755625316138196603 52428065633437974207294905)
              ·
                refine ⟨39321049225078480655471179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52428065633437974207294905 39321049225078480655471179)
                ·
                  refine ⟨58981573837617720983206769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39321049225078480655471179 58981573837617720983206769)
                  ·
                    refine ⟨44236180378213290737405077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58981573837617720983206769 44236180378213290737405077)
                    ·
                      refine ⟨2073570955228748003315863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44236180378213290737405077 2073570955228748003315863)
                      ·
                        rfl

theorem cell23_4038265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_4038265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038265 prefixEnd_4038265 := by exact prefixLift 4038265
  have htrace : WordTrace (prefixWord ++ tailWord_4038265) baseStart_4038265 baseEnd_4038265 := by
    simpa [prefixWord, tailWord_4038265, baseEnd_4038265] using wordTrace_append hprefix tailTrace_4038265
  have hstable : (prefixWord ++ tailWord_4038265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038265).length < 2 ^ (prefixWord ++ tailWord_4038265).sum := by decide
  have hdescent : baseEnd_4038265 < baseStart_4038265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038326 : List Nat := [5, 1, 3, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4038326 : Nat := 118140960795 + 4038326 * 2 ^ 59
def prefixEnd_4038326 : Nat := 4983230072969 + 3 ^ 40 * 4038326 * 2
def baseEnd_4038326 : Nat := 691200759182890754884361

theorem tailTrace_4038326 : CollatzResearch.WordTrace tailWord_4038326 prefixEnd_4038326 691200759182890754884361 := by
  unfold tailWord_4038326
  simp only [CollatzResearch.WordTrace]
  refine ⟨9205615597990129251049427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98193233045228045344527221 9205615597990129251049427)
  ·
    refine ⟨13808423396985193876574141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9205615597990129251049427 13808423396985193876574141)
    ·
      refine ⟨5178158773869447703715303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13808423396985193876574141 5178158773869447703715303)
      ·
        refine ⟨7767238160804171555572955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178158773869447703715303 7767238160804171555572955)
        ·
          refine ⟨11650857241206257333359433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767238160804171555572955 11650857241206257333359433)
          ·
            refine ⟨8738142930904693000019575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11650857241206257333359433 8738142930904693000019575)
            ·
              refine ⟨13107214396357039500029363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738142930904693000019575 13107214396357039500029363)
              ·
                refine ⟨19660821594535559250044045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13107214396357039500029363 19660821594535559250044045)
                ·
                  refine ⟨7372808097950834718766517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19660821594535559250044045 7372808097950834718766517)
                  ·
                    refine ⟨691200759182890754884361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7372808097950834718766517 691200759182890754884361)
                    ·
                      rfl

theorem cell23_4038326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4038326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038326 prefixEnd_4038326 := by exact prefixLift 4038326
  have htrace : WordTrace (prefixWord ++ tailWord_4038326) baseStart_4038326 baseEnd_4038326 := by
    simpa [prefixWord, tailWord_4038326, baseEnd_4038326] using wordTrace_append hprefix tailTrace_4038326
  have hstable : (prefixWord ++ tailWord_4038326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038326).length < 2 ^ (prefixWord ++ tailWord_4038326).sum := by decide
  have hdescent : baseEnd_4038326 < baseStart_4038326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038329 : List Nat := [1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 4]
def baseStart_4038329 : Nat := 118140960795 + 4038329 * 2 ^ 59
def prefixEnd_4038329 : Nat := 4983230072969 + 3 ^ 40 * 4038329 * 2
def baseEnd_4038329 : Nat := 2073603817990635752915569

theorem tailTrace_4038329 : CollatzResearch.WordTrace tailWord_4038329 prefixEnd_4038329 2073603817990635752915569 := by
  unfold tailWord_4038329
  simp only [CollatzResearch.WordTrace]
  refine ⟨147289958986831199529150041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98193305991220799686100027 147289958986831199529150041)
  ·
    refine ⟨110467469240123399646862531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147289958986831199529150041 110467469240123399646862531)
    ·
      refine ⟨165701203860185099470293797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110467469240123399646862531 165701203860185099470293797)
      ·
        refine ⟨31068975723784706150680087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165701203860185099470293797 31068975723784706150680087)
        ·
          refine ⟨46603463585677059226020131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31068975723784706150680087 46603463585677059226020131)
          ·
            refine ⟨69905195378515588839030197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46603463585677059226020131 69905195378515588839030197)
            ·
              refine ⟨6553612066735836453659081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69905195378515588839030197 6553612066735836453659081)
              ·
                refine ⟨4915209050051877340244311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553612066735836453659081 4915209050051877340244311)
                ·
                  refine ⟨7372813575077816010366467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915209050051877340244311 7372813575077816010366467)
                  ·
                    refine ⟨11059220362616724015549701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7372813575077816010366467 11059220362616724015549701)
                    ·
                      refine ⟨2073603817990635752915569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11059220362616724015549701 2073603817990635752915569)
                      ·
                        rfl

theorem cell23_4038329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 2, 1, 1, 4].length) (baseStart_4038329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038329 prefixEnd_4038329 := by exact prefixLift 4038329
  have htrace : WordTrace (prefixWord ++ tailWord_4038329) baseStart_4038329 baseEnd_4038329 := by
    simpa [prefixWord, tailWord_4038329, baseEnd_4038329] using wordTrace_append hprefix tailTrace_4038329
  have hstable : (prefixWord ++ tailWord_4038329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038329).length < 2 ^ (prefixWord ++ tailWord_4038329).sum := by decide
  have hdescent : baseEnd_4038329 < baseStart_4038329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038335 : List Nat := [1, 1, 2, 2, 2, 3, 1, 11]
def baseStart_4038335 : Nat := 118140960795 + 4038335 * 2 ^ 59
def prefixEnd_4038335 : Nat := 4983230072969 + 3 ^ 40 * 4038335 * 2
def baseEnd_4038335 : Nat := 76800255513872693682983

theorem tailTrace_4038335 : CollatzResearch.WordTrace tailWord_4038335 prefixEnd_4038335 76800255513872693682983 := by
  unfold tailWord_4038335
  simp only [CollatzResearch.WordTrace]
  refine ⟨147290177824809462553868459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98193451883206308369245639 147290177824809462553868459)
  ·
    refine ⟨220935266737214193830802689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147290177824809462553868459 220935266737214193830802689)
    ·
      refine ⟨165701450052910645373102017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220935266737214193830802689 165701450052910645373102017)
      ·
        refine ⟨124276087539682984029826513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165701450052910645373102017 124276087539682984029826513)
        ·
          refine ⟨93207065654762238022369885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124276087539682984029826513 93207065654762238022369885)
          ·
            refine ⟨34952649620535839258388707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93207065654762238022369885 34952649620535839258388707)
            ·
              refine ⟨52428974430803758887583061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34952649620535839258388707 52428974430803758887583061)
              ·
                refine ⟨76800255513872693682983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 52428974430803758887583061 76800255513872693682983)
                ·
                  rfl

theorem cell23_4038335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 11].length) (baseStart_4038335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038335 prefixEnd_4038335 := by exact prefixLift 4038335
  have htrace : WordTrace (prefixWord ++ tailWord_4038335) baseStart_4038335 baseEnd_4038335 := by
    simpa [prefixWord, tailWord_4038335, baseEnd_4038335] using wordTrace_append hprefix tailTrace_4038335
  have hstable : (prefixWord ++ tailWord_4038335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038335).length < 2 ^ (prefixWord ++ tailWord_4038335).sum := by decide
  have hdescent : baseEnd_4038335 < baseStart_4038335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038355 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_4038355 : Nat := 118140960795 + 4038355 * 2 ^ 59
def prefixEnd_4038355 : Nat := 4983230072969 + 3 ^ 40 * 4038355 * 2
def baseEnd_4038355 : Nat := 2073617168487652651190449

theorem tailTrace_4038355 : CollatzResearch.WordTrace tailWord_4038355 prefixEnd_4038355 2073617168487652651190449 := by
  unfold tailWord_4038355
  simp only [CollatzResearch.WordTrace]
  refine ⟨147290907284737005969596519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98193938189824670646397679 147290907284737005969596519)
  ·
    refine ⟨220936360927105508954394779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147290907284737005969596519 220936360927105508954394779)
    ·
      refine ⟨331404541390658263431592169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220936360927105508954394779 331404541390658263431592169)
      ·
        refine ⟨248553406042993697573694127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331404541390658263431592169 248553406042993697573694127)
        ·
          refine ⟨372830109064490546360541191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248553406042993697573694127 372830109064490546360541191)
          ·
            refine ⟨559245163596735819540811787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372830109064490546360541191 559245163596735819540811787)
            ·
              refine ⟨838867745395103729311217681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559245163596735819540811787 838867745395103729311217681)
              ·
                refine ⟨629150809046327796983413261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838867745395103729311217681 629150809046327796983413261)
                ·
                  refine ⟨235931553392372923868779973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629150809046327796983413261 235931553392372923868779973)
                  ·
                    refine ⟨44237166261069923225396245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235931553392372923868779973 44237166261069923225396245)
                    ·
                      refine ⟨2073617168487652651190449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44237166261069923225396245 2073617168487652651190449)
                      ·
                        rfl

theorem cell23_4038355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_4038355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038355 prefixEnd_4038355 := by exact prefixLift 4038355
  have htrace : WordTrace (prefixWord ++ tailWord_4038355) baseStart_4038355 baseEnd_4038355 := by
    simpa [prefixWord, tailWord_4038355, baseEnd_4038355] using wordTrace_append hprefix tailTrace_4038355
  have hstable : (prefixWord ++ tailWord_4038355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038355).length < 2 ^ (prefixWord ++ tailWord_4038355).sum := by decide
  have hdescent : baseEnd_4038355 < baseStart_4038355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038356 : List Nat := [2, 4, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_4038356 : Nat := 118140960795 + 4038356 * 2 ^ 59
def prefixEnd_4038356 : Nat := 4983230072969 + 3 ^ 40 * 4038356 * 2
def baseEnd_4038356 : Nat := 691205893989435715759315

theorem tailTrace_4038356 : CollatzResearch.WordTrace tailWord_4038356 prefixEnd_4038356 691205893989435715759315 := by
  unfold tailWord_4038356
  simp only [CollatzResearch.WordTrace]
  refine ⟨73645471878866691570191461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98193962505155588760255281 73645471878866691570191461)
  ·
    refine ⟨13808525977287504669410899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73645471878866691570191461 13808525977287504669410899)
    ·
      refine ⟨20712788965931257004116349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13808525977287504669410899 20712788965931257004116349)
      ·
        refine ⟨7767295862224221376543631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20712788965931257004116349 7767295862224221376543631)
        ·
          refine ⟨11650943793336332064815447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767295862224221376543631 11650943793336332064815447)
          ·
            refine ⟨17476415690004498097223171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650943793336332064815447 17476415690004498097223171)
            ·
              refine ⟨26214623535006747145834757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17476415690004498097223171 26214623535006747145834757)
              ·
                refine ⟨4915241912813765089844017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26214623535006747145834757 4915241912813765089844017)
                ·
                  refine ⟨3686431434610323817383013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915241912813765089844017 3686431434610323817383013)
                  ·
                    refine ⟨691205893989435715759315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3686431434610323817383013 691205893989435715759315)
                    ·
                      rfl

theorem cell23_4038356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_4038356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038356 prefixEnd_4038356 := by exact prefixLift 4038356
  have htrace : WordTrace (prefixWord ++ tailWord_4038356) baseStart_4038356 baseEnd_4038356 := by
    simpa [prefixWord, tailWord_4038356, baseEnd_4038356] using wordTrace_append hprefix tailTrace_4038356
  have hstable : (prefixWord ++ tailWord_4038356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038356).length < 2 ^ (prefixWord ++ tailWord_4038356).sum := by decide
  have hdescent : baseEnd_4038356 < baseStart_4038356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038369 : List Nat := [1, 2, 3, 1, 5, 2, 1, 8]
def baseStart_4038369 : Nat := 118140960795 + 4038369 * 2 ^ 59
def prefixEnd_4038369 : Nat := 4983230072969 + 3 ^ 40 * 4038369 * 2
def baseEnd_4038369 : Nat := 76800902119141318385755

theorem tailTrace_4038369 : CollatzResearch.WordTrace tailWord_4038369 prefixEnd_4038369 76800902119141318385755 := by
  unfold tailWord_4038369
  simp only [CollatzResearch.WordTrace]
  refine ⟨147291417906686286360606161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98194278604457524240404107 147291417906686286360606161)
  ·
    refine ⟨110468563430014714770454621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147291417906686286360606161 110468563430014714770454621)
    ·
      refine ⟨41425711286255518038920483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110468563430014714770454621 41425711286255518038920483)
      ·
        refine ⟨62138566929383277058380725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41425711286255518038920483 62138566929383277058380725)
        ·
          refine ⟨5825490649629682224223193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62138566929383277058380725 5825490649629682224223193)
          ·
            refine ⟨4369117987222261668167395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825490649629682224223193 4369117987222261668167395)
            ·
              refine ⟨6553676980833392502251093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369117987222261668167395 6553676980833392502251093)
              ·
                refine ⟨76800902119141318385755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6553676980833392502251093 76800902119141318385755)
                ·
                  rfl

theorem cell23_4038369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 8].length) (baseStart_4038369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038369 prefixEnd_4038369 := by exact prefixLift 4038369
  have htrace : WordTrace (prefixWord ++ tailWord_4038369) baseStart_4038369 baseEnd_4038369 := by
    simpa [prefixWord, tailWord_4038369, baseEnd_4038369] using wordTrace_append hprefix tailTrace_4038369
  have hstable : (prefixWord ++ tailWord_4038369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038369).length < 2 ^ (prefixWord ++ tailWord_4038369).sum := by decide
  have hdescent : baseEnd_4038369 < baseStart_4038369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038382 : List Nat := [4, 1, 2, 1, 1, 2, 1, 2, 2, 7]
def baseStart_4038382 : Nat := 118140960795 + 4038382 * 2 ^ 59
def prefixEnd_4038382 : Nat := 4983230072969 + 3 ^ 40 * 4038382 * 2
def baseEnd_4038382 : Nat := 691210344155108015184275

theorem tailTrace_4038382 : CollatzResearch.WordTrace tailWord_4038382 prefixEnd_4038382 691210344155108015184275 := by
  unfold tailWord_4038382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411486506954898697603675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98194594703759459720552933 18411486506954898697603675)
  ·
    refine ⟨27617229760432348046405513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18411486506954898697603675 27617229760432348046405513)
    ·
      refine ⟨20712922320324261034804135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27617229760432348046405513 20712922320324261034804135)
      ·
        refine ⟨31069383480486391552206203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20712922320324261034804135 31069383480486391552206203)
        ·
          refine ⟨46604075220729587328309305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31069383480486391552206203 46604075220729587328309305)
          ·
            refine ⟨34953056415547190496231979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46604075220729587328309305 34953056415547190496231979)
            ·
              refine ⟨52429584623320785744347969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34953056415547190496231979 52429584623320785744347969)
              ·
                refine ⟨39322188467490589308260977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52429584623320785744347969 39322188467490589308260977)
                ·
                  refine ⟨29491641350617941981195733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39322188467490589308260977 29491641350617941981195733)
                  ·
                    refine ⟨691210344155108015184275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29491641350617941981195733 691210344155108015184275)
                    ·
                      rfl

theorem cell23_4038382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_4038382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038382 prefixEnd_4038382 := by exact prefixLift 4038382
  have htrace : WordTrace (prefixWord ++ tailWord_4038382) baseStart_4038382 baseEnd_4038382 := by
    simpa [prefixWord, tailWord_4038382, baseEnd_4038382] using wordTrace_append hprefix tailTrace_4038382
  have hstable : (prefixWord ++ tailWord_4038382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038382).length < 2 ^ (prefixWord ++ tailWord_4038382).sum := by decide
  have hdescent : baseEnd_4038382 < baseStart_4038382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038412 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 2, 6]
def baseStart_4038412 : Nat := 118140960795 + 4038412 * 2 ^ 59
def prefixEnd_4038412 : Nat := 4983230072969 + 3 ^ 40 * 4038412 * 2
def baseEnd_4038412 : Nat := 691215478961652976059229

theorem tailTrace_4038412 : CollatzResearch.WordTrace tailWord_4038412 prefixEnd_4038412 691215478961652976059229 := by
  unfold tailWord_4038412
  simp only [CollatzResearch.WordTrace]
  refine ⟨73646493122765252352210745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98195324163687003136280993 73646493122765252352210745)
  ·
    refine ⟨55234869842073939264158059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73646493122765252352210745 55234869842073939264158059)
    ·
      refine ⟨82852304763110908896237089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55234869842073939264158059 82852304763110908896237089)
      ·
        refine ⟨62139228572333181672177817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82852304763110908896237089 62139228572333181672177817)
        ·
          refine ⟨46604421429249886254133363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62139228572333181672177817 46604421429249886254133363)
          ·
            refine ⟨69906632143874829381200045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46604421429249886254133363 69906632143874829381200045)
            ·
              refine ⟨26214987053953061017950017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69906632143874829381200045 26214987053953061017950017)
              ·
                refine ⟨19661240290464795763462513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26214987053953061017950017 19661240290464795763462513)
                ·
                  refine ⟨14745930217848596822596885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19661240290464795763462513 14745930217848596822596885)
                  ·
                    refine ⟨691215478961652976059229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14745930217848596822596885 691215478961652976059229)
                    ·
                      rfl

theorem cell23_4038412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 2, 6].length) (baseStart_4038412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038412 prefixEnd_4038412 := by exact prefixLift 4038412
  have htrace : WordTrace (prefixWord ++ tailWord_4038412) baseStart_4038412 baseEnd_4038412 := by
    simpa [prefixWord, tailWord_4038412, baseEnd_4038412] using wordTrace_append hprefix tailTrace_4038412
  have hstable : (prefixWord ++ tailWord_4038412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038412).length < 2 ^ (prefixWord ++ tailWord_4038412).sum := by decide
  have hdescent : baseEnd_4038412 < baseStart_4038412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038476 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 7]
def baseStart_4038476 : Nat := 118140960795 + 4038476 * 2 ^ 59
def prefixEnd_4038476 : Nat := 4983230072969 + 3 ^ 40 * 4038476 * 2
def baseEnd_4038476 : Nat := 230408811071871853086377

theorem tailTrace_4038476 : CollatzResearch.WordTrace tailWord_4038476 prefixEnd_4038476 230408811071871853086377 := by
  unfold tailWord_4038476
  simp only [CollatzResearch.WordTrace]
  refine ⟨73647660258649321817375641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98196880344865762423167521 73647660258649321817375641)
  ·
    refine ⟨55235745193986991363031731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73647660258649321817375641 55235745193986991363031731)
    ·
      refine ⟨82853617790980487044547597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55235745193986991363031731 82853617790980487044547597)
      ·
        refine ⟨31070106671617682641705349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82853617790980487044547597 31070106671617682641705349)
        ·
          refine ⟨5825645000928315495319753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31070106671617682641705349 5825645000928315495319753)
          ·
            refine ⟨4369233750696236621489815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825645000928315495319753 4369233750696236621489815)
            ·
              refine ⟨6553850626044354932234723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369233750696236621489815 6553850626044354932234723)
              ·
                refine ⟨9830775939066532398352085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553850626044354932234723 9830775939066532398352085)
                ·
                  refine ⟨230408811071871853086377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9830775939066532398352085 230408811071871853086377)
                  ·
                    rfl

theorem cell23_4038476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 7].length) (baseStart_4038476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038476 prefixEnd_4038476 := by exact prefixLift 4038476
  have htrace : WordTrace (prefixWord ++ tailWord_4038476) baseStart_4038476 baseEnd_4038476 := by
    simpa [prefixWord, tailWord_4038476, baseEnd_4038476] using wordTrace_append hprefix tailTrace_4038476
  have hstable : (prefixWord ++ tailWord_4038476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038476).length < 2 ^ (prefixWord ++ tailWord_4038476).sum := by decide
  have hdescent : baseEnd_4038476 < baseStart_4038476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4038487 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 2, 2, 2]
def baseStart_4038487 : Nat := 118140960795 + 4038487 * 2 ^ 59
def prefixEnd_4038487 : Nat := 4983230072969 + 3 ^ 40 * 4038487 * 2
def baseEnd_4038487 : Nat := 2073684947934046134739843

theorem tailTrace_4038487 : CollatzResearch.WordTrace tailWord_4038487 prefixEnd_4038487 2073684947934046134739843 := by
  unfold tailWord_4038487
  simp only [CollatzResearch.WordTrace]
  refine ⟨147295721720258792513401715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98197147813505861675601143 147295721720258792513401715)
  ·
    refine ⟨220943582580388188770102573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147295721720258792513401715 220943582580388188770102573)
    ·
      refine ⟨82853843467645570788788465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220943582580388188770102573 82853843467645570788788465)
      ·
        refine ⟨62140382600734178091591349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82853843467645570788788465 62140382600734178091591349)
        ·
          refine ⟨5825660868818829196086689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62140382600734178091591349 5825660868818829196086689)
          ·
            refine ⟨4369245651614121897065017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5825660868818829196086689 4369245651614121897065017)
            ·
              refine ⟨3276934238710591422798763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4369245651614121897065017 3276934238710591422798763)
              ·
                refine ⟨4915401358065887134198145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276934238710591422798763 4915401358065887134198145)
                ·
                  refine ⟨3686551018549415350648609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4915401358065887134198145 3686551018549415350648609)
                  ·
                    refine ⟨2764913263912061512986457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3686551018549415350648609 2764913263912061512986457)
                    ·
                      refine ⟨2073684947934046134739843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2764913263912061512986457 2073684947934046134739843)
                      ·
                        rfl

theorem cell23_4038487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 2, 2].length) (baseStart_4038487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4038487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4038487 prefixEnd_4038487 := by exact prefixLift 4038487
  have htrace : WordTrace (prefixWord ++ tailWord_4038487) baseStart_4038487 baseEnd_4038487 := by
    simpa [prefixWord, tailWord_4038487, baseEnd_4038487] using wordTrace_append hprefix tailTrace_4038487
  have hstable : (prefixWord ++ tailWord_4038487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4038487).length < 2 ^ (prefixWord ++ tailWord_4038487).sum := by decide
  have hdescent : baseEnd_4038487 < baseStart_4038487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4038487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
