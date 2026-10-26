import V185TrunkScan20Chunk164

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_1004607 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_1004607 : Nat := 118140960795 + 1004607 * 2 ^ 59
def prefixEnd_1004607 : Nat := 4983230072969 + 3 ^ 40 * 1004607 * 2
def baseEnd_1004607 : Nat := 458530008774627737059913

theorem tailTrace_1004607 : CollatzResearch.WordTrace tailWord_1004607 prefixEnd_1004607 458530008774627737059913 := by
  unfold tailWord_1004607
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641027471487887061068075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24427351647658591374045383 36641027471487887061068075)
  ·
    refine ⟨54961541207231830591602113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36641027471487887061068075 54961541207231830591602113)
    ·
      refine ⟨41221155905423872943701585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54961541207231830591602113 41221155905423872943701585)
      ·
        refine ⟨30915866929067904707776189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41221155905423872943701585 30915866929067904707776189)
        ·
          refine ⟨11593450098400464265416071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30915866929067904707776189 11593450098400464265416071)
          ·
            refine ⟨17390175147600696398124107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11593450098400464265416071 17390175147600696398124107)
            ·
              refine ⟨26085262721401044597186161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17390175147600696398124107 26085262721401044597186161)
              ·
                refine ⟨19563947041050783447889621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26085262721401044597186161 19563947041050783447889621)
                ·
                  refine ⟨458530008774627737059913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19563947041050783447889621 458530008774627737059913)
                  ·
                    rfl

theorem cell20_1004607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_1004607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004607 prefixEnd_1004607 := by exact prefixLift 1004607
  have htrace : WordTrace (prefixWord ++ tailWord_1004607) baseStart_1004607 baseEnd_1004607 := by
    simpa [prefixWord, tailWord_1004607, baseEnd_1004607] using wordTrace_append hprefix tailTrace_1004607
  have hstable : (prefixWord ++ tailWord_1004607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004607).length < 2 ^ (prefixWord ++ tailWord_1004607).sum := by decide
  have hdescent : baseEnd_1004607 < baseStart_1004607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004637 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 3]
def baseStart_1004637 : Nat := 118140960795 + 1004637 * 2 ^ 59
def prefixEnd_1004637 : Nat := 4983230072969 + 3 ^ 40 * 1004637 * 2
def baseEnd_1004637 : Nat := 458543701592080966059791

theorem tailTrace_1004637 : CollatzResearch.WordTrace tailWord_1004637 prefixEnd_1004637 458543701592080966059791 := by
  unfold tailWord_1004637
  simp only [CollatzResearch.WordTrace]
  refine ⟨36642121661379202184660165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24428081107586134789773443 36642121661379202184660165)
  ·
    refine ⟨6870397811508600409623781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36642121661379202184660165 6870397811508600409623781)
    ·
      refine ⟨1288199589657862576804459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6870397811508600409623781 1288199589657862576804459)
      ·
        refine ⟨1932299384486793865206689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288199589657862576804459 1932299384486793865206689)
        ·
          refine ⟨1449224538365095398905017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932299384486793865206689 1449224538365095398905017)
          ·
            refine ⟨1086918403773821549178763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449224538365095398905017 1086918403773821549178763)
            ·
              refine ⟨1630377605660732323768145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086918403773821549178763 1630377605660732323768145)
              ·
                refine ⟨1222783204245549242826109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630377605660732323768145 1222783204245549242826109)
                ·
                  refine ⟨458543701592080966059791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222783204245549242826109 458543701592080966059791)
                  ·
                    rfl

theorem cell20_1004637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_1004637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004637 prefixEnd_1004637 := by exact prefixLift 1004637
  have htrace : WordTrace (prefixWord ++ tailWord_1004637) baseStart_1004637 baseEnd_1004637 := by
    simpa [prefixWord, tailWord_1004637, baseEnd_1004637] using wordTrace_append hprefix tailTrace_1004637
  have hstable : (prefixWord ++ tailWord_1004637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004637).length < 2 ^ (prefixWord ++ tailWord_1004637).sum := by decide
  have hdescent : baseEnd_1004637 < baseStart_1004637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004669 : List Nat := [1, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_1004669 : Nat := 118140960795 + 1004669 * 2 ^ 59
def prefixEnd_1004669 : Nat := 4983230072969 + 3 ^ 40 * 1004669 * 2
def baseEnd_1004669 : Nat := 458558307264031076992993

theorem tailTrace_1004669 : CollatzResearch.WordTrace tailWord_1004669 prefixEnd_1004669 458558307264031076992993 := by
  unfold tailWord_1004669
  simp only [CollatzResearch.WordTrace]
  refine ⟨36643288797263271649825061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24428859198175514433216707 36643288797263271649825061)
  ·
    refine ⟨6870616649486863434342199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36643288797263271649825061 6870616649486863434342199)
    ·
      refine ⟨10305924974230295151513299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6870616649486863434342199 10305924974230295151513299)
      ·
        refine ⟨15458887461345442727269949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305924974230295151513299 15458887461345442727269949)
        ·
          refine ⟨5797082798004541022726231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15458887461345442727269949 5797082798004541022726231)
          ·
            refine ⟨8695624197006811534089347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797082798004541022726231 8695624197006811534089347)
            ·
              refine ⟨13043436295510217301134021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8695624197006811534089347 13043436295510217301134021)
              ·
                refine ⟨2445644305408165743962629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13043436295510217301134021 2445644305408165743962629)
                ·
                  refine ⟨458558307264031076992993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445644305408165743962629 458558307264031076992993)
                  ·
                    rfl

theorem cell20_1004669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_1004669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004669 prefixEnd_1004669 := by exact prefixLift 1004669
  have htrace : WordTrace (prefixWord ++ tailWord_1004669) baseStart_1004669 baseEnd_1004669 := by
    simpa [prefixWord, tailWord_1004669, baseEnd_1004669] using wordTrace_append hprefix tailTrace_1004669
  have hstable : (prefixWord ++ tailWord_1004669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004669).length < 2 ^ (prefixWord ++ tailWord_1004669).sum := by decide
  have hdescent : baseEnd_1004669 < baseStart_1004669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004700 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1004700 : Nat := 118140960795 + 1004700 * 2 ^ 59
def prefixEnd_1004700 : Nat := 4983230072969 + 3 ^ 40 * 1004700 * 2
def baseEnd_1004700 : Nat := 458572456508732746959533

theorem tailTrace_1004700 : CollatzResearch.WordTrace tailWord_1004700 prefixEnd_1004700 458572456508732746959533 := by
  unfold tailWord_1004700
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322209730075481972101777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24429612973433975962802369 18322209730075481972101777)
  ·
    refine ⟨13741657297556611479076333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18322209730075481972101777 13741657297556611479076333)
    ·
      refine ⟨5153121486583729304653625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13741657297556611479076333 5153121486583729304653625)
      ·
        refine ⟨3864841114937796978490219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5153121486583729304653625 3864841114937796978490219)
        ·
          refine ⟨5797261672406695467735329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3864841114937796978490219 5797261672406695467735329)
          ·
            refine ⟨4347946254305021600801497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797261672406695467735329 4347946254305021600801497)
            ·
              refine ⟨3260959690728766200601123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347946254305021600801497 3260959690728766200601123)
              ·
                refine ⟨4891439536093149300901685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260959690728766200601123 4891439536093149300901685)
                ·
                  refine ⟨458572456508732746959533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891439536093149300901685 458572456508732746959533)
                  ·
                    rfl

theorem cell20_1004700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1004700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004700 prefixEnd_1004700 := by exact prefixLift 1004700
  have htrace : WordTrace (prefixWord ++ tailWord_1004700) baseStart_1004700 baseEnd_1004700 := by
    simpa [prefixWord, tailWord_1004700, baseEnd_1004700] using wordTrace_append hprefix tailTrace_1004700
  have hstable : (prefixWord ++ tailWord_1004700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004700).length < 2 ^ (prefixWord ++ tailWord_1004700).sum := by decide
  have hdescent : baseEnd_1004700 < baseStart_1004700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004703 : List Nat := [1, 1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_1004703 : Nat := 118140960795 + 1004703 * 2 ^ 59
def prefixEnd_1004703 : Nat := 4983230072969 + 3 ^ 40 * 1004703 * 2
def baseEnd_1004703 : Nat := 458573825790478069859521

theorem tailTrace_1004703 : CollatzResearch.WordTrace tailWord_1004703 prefixEnd_1004703 458573825790478069859521 := by
  unfold tailWord_1004703
  simp only [CollatzResearch.WordTrace]
  refine ⟨36644528879140095456562763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24429685919426730304375175 36644528879140095456562763)
  ·
    refine ⟨54966793318710143184844145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36644528879140095456562763 54966793318710143184844145)
    ·
      refine ⟨41225094989032607388633109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54966793318710143184844145 41225094989032607388633109)
      ·
        refine ⟨1932426327610903471342177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 41225094989032607388633109 1932426327610903471342177)
        ·
          refine ⟨1449319745708177603506633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932426327610903471342177 1449319745708177603506633)
          ·
            refine ⟨1086989809281133202629975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449319745708177603506633 1086989809281133202629975)
            ·
              refine ⟨1630484713921699803944963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086989809281133202629975 1630484713921699803944963)
              ·
                refine ⟨2445727070882549705917445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630484713921699803944963 2445727070882549705917445)
                ·
                  refine ⟨458573825790478069859521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445727070882549705917445 458573825790478069859521)
                  ·
                    rfl

theorem cell20_1004703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_1004703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004703 prefixEnd_1004703 := by exact prefixLift 1004703
  have htrace : WordTrace (prefixWord ++ tailWord_1004703) baseStart_1004703 baseEnd_1004703 := by
    simpa [prefixWord, tailWord_1004703, baseEnd_1004703] using wordTrace_append hprefix tailTrace_1004703
  have hstable : (prefixWord ++ tailWord_1004703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004703).length < 2 ^ (prefixWord ++ tailWord_1004703).sum := by decide
  have hdescent : baseEnd_1004703 < baseStart_1004703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004759 : List Nat := [1, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_1004759 : Nat := 118140960795 + 1004759 * 2 ^ 59
def prefixEnd_1004759 : Nat := 4983230072969 + 3 ^ 40 * 1004759 * 2
def baseEnd_1004759 : Nat := 458599385716390763992625

theorem tailTrace_1004759 : CollatzResearch.WordTrace tailWord_1004759 prefixEnd_1004759 458599385716390763992625 := by
  unfold tailWord_1004759
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646571366937217020601331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24431047577958144680400887 36646571366937217020601331)
  ·
    refine ⟨54969857050405825530901997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36646571366937217020601331 54969857050405825530901997)
    ·
      refine ⟨20613696393902184574088249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54969857050405825530901997 20613696393902184574088249)
      ·
        refine ⟨15460272295426638430566187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20613696393902184574088249 15460272295426638430566187)
        ·
          refine ⟨23190408443139957645849281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460272295426638430566187 23190408443139957645849281)
          ·
            refine ⟨17392806332354968234386961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23190408443139957645849281 17392806332354968234386961)
            ·
              refine ⟨13044604749266226175790221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17392806332354968234386961 13044604749266226175790221)
              ·
                refine ⟨4891726780974834815921333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13044604749266226175790221 4891726780974834815921333)
                ·
                  refine ⟨458599385716390763992625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891726780974834815921333 458599385716390763992625)
                  ·
                    rfl

theorem cell20_1004759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_1004759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004759 prefixEnd_1004759 := by exact prefixLift 1004759
  have htrace : WordTrace (prefixWord ++ tailWord_1004759) baseStart_1004759 baseEnd_1004759 := by
    simpa [prefixWord, tailWord_1004759, baseEnd_1004759] using wordTrace_append hprefix tailTrace_1004759
  have hstable : (prefixWord ++ tailWord_1004759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004759).length < 2 ^ (prefixWord ++ tailWord_1004759).sum := by decide
  have hdescent : baseEnd_1004759 < baseStart_1004759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004765 : List Nat := [1, 4, 3, 2, 3, 1, 1, 5]
def baseStart_1004765 : Nat := 118140960795 + 1004765 * 2 ^ 59
def prefixEnd_1004765 : Nat := 4983230072969 + 3 ^ 40 * 1004765 * 2
def baseEnd_1004765 : Nat := 152867374759960469930867

theorem tailTrace_1004765 : CollatzResearch.WordTrace tailWord_1004765 prefixEnd_1004765 152867374759960469930867 := by
  unfold tailWord_1004765
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646790204915480045319749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24431193469943653363546499 36646790204915480045319749)
  ·
    refine ⟨6871273163421652508497453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36646790204915480045319749 6871273163421652508497453)
    ·
      refine ⟨2576727436283119690686545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6871273163421652508497453 2576727436283119690686545)
      ·
        refine ⟨1932545577212339768014909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2576727436283119690686545 1932545577212339768014909)
        ·
          refine ⟨724704591454627413005591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1932545577212339768014909 724704591454627413005591)
          ·
            refine ⟨1087056887181941119508387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724704591454627413005591 1087056887181941119508387)
            ·
              refine ⟨1630585330772911679262581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087056887181941119508387 1630585330772911679262581)
              ·
                refine ⟨152867374759960469930867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1630585330772911679262581 152867374759960469930867)
                ·
                  rfl

theorem cell20_1004765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_1004765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004765 prefixEnd_1004765 := by exact prefixLift 1004765
  have htrace : WordTrace (prefixWord ++ tailWord_1004765) baseStart_1004765 baseEnd_1004765 := by
    simpa [prefixWord, tailWord_1004765, baseEnd_1004765] using wordTrace_append hprefix tailTrace_1004765
  have hstable : (prefixWord ++ tailWord_1004765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004765).length < 2 ^ (prefixWord ++ tailWord_1004765).sum := by decide
  have hdescent : baseEnd_1004765 < baseStart_1004765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004769 : List Nat := [1, 2, 3, 1, 3, 4, 1, 5]
def baseStart_1004769 : Nat := 118140960795 + 1004769 * 2 ^ 59
def prefixEnd_1004769 : Nat := 4983230072969 + 3 ^ 40 * 1004769 * 2
def baseEnd_1004769 : Nat := 152867983329625057886417

theorem tailTrace_1004769 : CollatzResearch.WordTrace tailWord_1004769 prefixEnd_1004769 152867983329625057886417 := by
  unfold tailWord_1004769
  simp only [CollatzResearch.WordTrace]
  refine ⟨36646936096900988728465361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24431290731267325818976907 36646936096900988728465361)
  ·
    refine ⟨27485202072675741546349021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36646936096900988728465361 27485202072675741546349021)
    ·
      refine ⟨10306950777253403079880883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27485202072675741546349021 10306950777253403079880883)
      ·
        refine ⟨15460426165880104619821325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10306950777253403079880883 15460426165880104619821325)
        ·
          refine ⟨5797659812205039232432997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15460426165880104619821325 5797659812205039232432997)
          ·
            refine ⟨1087061214788444856081187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5797659812205039232432997 1087061214788444856081187)
            ·
              refine ⟨1630591822182667284121781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087061214788444856081187 1630591822182667284121781)
              ·
                refine ⟨152867983329625057886417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1630591822182667284121781 152867983329625057886417)
                ·
                  rfl

theorem cell20_1004769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 5].length) (baseStart_1004769 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004769 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004769 prefixEnd_1004769 := by exact prefixLift 1004769
  have htrace : WordTrace (prefixWord ++ tailWord_1004769) baseStart_1004769 baseEnd_1004769 := by
    simpa [prefixWord, tailWord_1004769, baseEnd_1004769] using wordTrace_append hprefix tailTrace_1004769
  have hstable : (prefixWord ++ tailWord_1004769).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004769).length < 2 ^ (prefixWord ++ tailWord_1004769).sum := by decide
  have hdescent : baseEnd_1004769 < baseStart_1004769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004776 : List Nat := [2, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1004776 : Nat := 118140960795 + 1004776 * 2 ^ 59
def prefixEnd_1004776 : Nat := 4983230072969 + 3 ^ 40 * 1004776 * 2
def baseEnd_1004776 : Nat := 458607144979614260425889

theorem tailTrace_1004776 : CollatzResearch.WordTrace tailWord_1004776 prefixEnd_1004776 458607144979614260425889 := by
  unfold tailWord_1004776
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323595703937814461985091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24431460938583752615980121 18323595703937814461985091)
  ·
    refine ⟨27485393555906721692977637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18323595703937814461985091 27485393555906721692977637)
    ·
      refine ⟨5153511291732510317433307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27485393555906721692977637 5153511291732510317433307)
      ·
        refine ⟨7730266937598765476149961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5153511291732510317433307 7730266937598765476149961)
        ·
          refine ⟨5797700203199074107112471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7730266937598765476149961 5797700203199074107112471)
          ·
            refine ⟨8696550304798611160668707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5797700203199074107112471 8696550304798611160668707)
            ·
              refine ⟨13044825457197916741003061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8696550304798611160668707 13044825457197916741003061)
              ·
                refine ⟨1222952386612304694469037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13044825457197916741003061 1222952386612304694469037)
                ·
                  refine ⟨458607144979614260425889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222952386612304694469037 458607144979614260425889)
                  ·
                    rfl

theorem cell20_1004776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1004776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004776 prefixEnd_1004776 := by exact prefixLift 1004776
  have htrace : WordTrace (prefixWord ++ tailWord_1004776) baseStart_1004776 baseEnd_1004776 := by
    simpa [prefixWord, tailWord_1004776, baseEnd_1004776] using wordTrace_append hprefix tailTrace_1004776
  have hstable : (prefixWord ++ tailWord_1004776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004776).length < 2 ^ (prefixWord ++ tailWord_1004776).sum := by decide
  have hdescent : baseEnd_1004776 < baseStart_1004776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004786 : List Nat := [3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_1004786 : Nat := 118140960795 + 1004786 * 2 ^ 59
def prefixEnd_1004786 : Nat := 4983230072969 + 3 ^ 40 * 1004786 * 2
def baseEnd_1004786 : Nat := 152870569750699556697505

theorem tailTrace_1004786 : CollatzResearch.WordTrace tailWord_1004786 prefixEnd_1004786 152870569750699556697505 := by
  unfold tailWord_1004786
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161889034459850157958553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24431704091892933754556141 9161889034459850157958553)
  ·
    refine ⟨6871416775844887618468915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9161889034459850157958553 6871416775844887618468915)
    ·
      refine ⟨10307125163767331427703373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871416775844887618468915 10307125163767331427703373)
      ·
        refine ⟨3865171936412749285388765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10307125163767331427703373 3865171936412749285388765)
        ·
          refine ⟨1449439476154780982020787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3865171936412749285388765 1449439476154780982020787)
          ·
            refine ⟨2174159214232171473031181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449439476154780982020787 2174159214232171473031181)
            ·
              refine ⟨815309705337064302386693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2174159214232171473031181 815309705337064302386693)
              ·
                refine ⟨152870569750699556697505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815309705337064302386693 152870569750699556697505)
                ·
                  rfl

theorem cell20_1004786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_1004786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004786 prefixEnd_1004786 := by exact prefixLift 1004786
  have htrace : WordTrace (prefixWord ++ tailWord_1004786) baseStart_1004786 baseEnd_1004786 := by
    simpa [prefixWord, tailWord_1004786, baseEnd_1004786] using wordTrace_append hprefix tailTrace_1004786
  have hstable : (prefixWord ++ tailWord_1004786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004786).length < 2 ^ (prefixWord ++ tailWord_1004786).sum := by decide
  have hdescent : baseEnd_1004786 < baseStart_1004786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004814 : List Nat := [4, 1, 1, 2, 1, 4, 1, 1, 5]
def baseStart_1004814 : Nat := 118140960795 + 1004814 * 2 ^ 59
def prefixEnd_1004814 : Nat := 4983230072969 + 3 ^ 40 * 1004814 * 2
def baseEnd_1004814 : Nat := 458624489215055017159067

theorem tailTrace_1004814 : CollatzResearch.WordTrace tailWord_1004814 prefixEnd_1004814 458624489215055017159067 := by
  unfold tailWord_1004814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581072172717245176731687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24432384921158640942568997 4581072172717245176731687)
  ·
    refine ⟨6871608259075867765097531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581072172717245176731687 6871608259075867765097531)
    ·
      refine ⟨10307412388613801647646297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871608259075867765097531 10307412388613801647646297)
      ·
        refine ⟨7730559291460351235734723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10307412388613801647646297 7730559291460351235734723)
        ·
          refine ⟨11595838937190526853602085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7730559291460351235734723 11595838937190526853602085)
          ·
            refine ⟨2174219800723223785050391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11595838937190526853602085 2174219800723223785050391)
            ·
              refine ⟨3261329701084835677575587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174219800723223785050391 3261329701084835677575587)
              ·
                refine ⟨4891994551627253516363381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261329701084835677575587 4891994551627253516363381)
                ·
                  refine ⟨458624489215055017159067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4891994551627253516363381 458624489215055017159067)
                  ·
                    rfl

theorem cell20_1004814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_1004814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004814 prefixEnd_1004814 := by exact prefixLift 1004814
  have htrace : WordTrace (prefixWord ++ tailWord_1004814) baseStart_1004814 baseEnd_1004814 := by
    simpa [prefixWord, tailWord_1004814, baseEnd_1004814] using wordTrace_append hprefix tailTrace_1004814
  have hstable : (prefixWord ++ tailWord_1004814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004814).length < 2 ^ (prefixWord ++ tailWord_1004814).sum := by decide
  have hdescent : baseEnd_1004814 < baseStart_1004814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004852 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1004852 : Nat := 118140960795 + 1004852 * 2 ^ 59
def prefixEnd_1004852 : Nat := 4983230072969 + 3 ^ 40 * 1004852 * 2
def baseEnd_1004852 : Nat := 458641833450495773892245

theorem tailTrace_1004852 : CollatzResearch.WordTrace tailWord_1004852 prefixEnd_1004852 458641833450495773892245 := by
  unfold tailWord_1004852
  simp only [CollatzResearch.WordTrace]
  refine ⟨18324981677800146951868405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24433308903733529269157873 18324981677800146951868405)
  ·
    refine ⟨1717967032293763776737663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18324981677800146951868405 1717967032293763776737663)
    ·
      refine ⟨2576950548440645665106495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1717967032293763776737663 2576950548440645665106495)
      ·
        refine ⟨3865425822660968497659743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2576950548440645665106495 3865425822660968497659743)
        ·
          refine ⟨5798138733991452746489615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865425822660968497659743 5798138733991452746489615)
          ·
            refine ⟨8697208100987179119734423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798138733991452746489615 8697208100987179119734423)
            ·
              refine ⟨13045812151480768679601635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8697208100987179119734423 13045812151480768679601635)
              ·
                refine ⟨19568718227221153019402453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13045812151480768679601635 19568718227221153019402453)
                ·
                  refine ⟨458641833450495773892245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19568718227221153019402453 458641833450495773892245)
                  ·
                    rfl

theorem cell20_1004852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1004852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004852 prefixEnd_1004852 := by exact prefixLift 1004852
  have htrace : WordTrace (prefixWord ++ tailWord_1004852) baseStart_1004852 baseEnd_1004852 := by
    simpa [prefixWord, tailWord_1004852, baseEnd_1004852] using wordTrace_append hprefix tailTrace_1004852
  have hstable : (prefixWord ++ tailWord_1004852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004852).length < 2 ^ (prefixWord ++ tailWord_1004852).sum := by decide
  have hdescent : baseEnd_1004852 < baseStart_1004852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004873 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_1004873 : Nat := 118140960795 + 1004873 * 2 ^ 59
def prefixEnd_1004873 : Nat := 4983230072969 + 3 ^ 40 * 1004873 * 2
def baseEnd_1004873 : Nat := 458651418422713034192159

theorem tailTrace_1004873 : CollatzResearch.WordTrace tailWord_1004873 prefixEnd_1004873 458651418422713034192159 := by
  unfold tailWord_1004873
  simp only [CollatzResearch.WordTrace]
  refine ⟨36650729288524214490251273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24433819525682809660167515 36650729288524214490251273)
  ·
    refine ⟨27488046966393160867688455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36650729288524214490251273 27488046966393160867688455)
    ·
      refine ⟨41232070449589741301532683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27488046966393160867688455 41232070449589741301532683)
      ·
        refine ⟨61848105674384611952299025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41232070449589741301532683 61848105674384611952299025)
        ·
          refine ⟨46386079255788458964224269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61848105674384611952299025 46386079255788458964224269)
          ·
            refine ⟨17394779720920672111584101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46386079255788458964224269 17394779720920672111584101)
            ·
              refine ⟨3261521197672626020922019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17394779720920672111584101 3261521197672626020922019)
              ·
                refine ⟨4892281796508939031383029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261521197672626020922019 4892281796508939031383029)
                ·
                  refine ⟨458651418422713034192159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4892281796508939031383029 458651418422713034192159)
                  ·
                    rfl

theorem cell20_1004873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_1004873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004873 prefixEnd_1004873 := by exact prefixLift 1004873
  have htrace : WordTrace (prefixWord ++ tailWord_1004873) baseStart_1004873 baseEnd_1004873 := by
    simpa [prefixWord, tailWord_1004873, baseEnd_1004873] using wordTrace_append hprefix tailTrace_1004873
  have hstable : (prefixWord ++ tailWord_1004873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004873).length < 2 ^ (prefixWord ++ tailWord_1004873).sum := by decide
  have hdescent : baseEnd_1004873 < baseStart_1004873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004876 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_1004876 : Nat := 118140960795 + 1004876 * 2 ^ 59
def prefixEnd_1004876 : Nat := 4983230072969 + 3 ^ 40 * 1004876 * 2
def baseEnd_1004876 : Nat := 458652787704458357092147

theorem tailTrace_1004876 : CollatzResearch.WordTrace tailWord_1004876 prefixEnd_1004876 458652787704458357092147 := by
  unfold tailWord_1004876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18325419353756673001305241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24433892471675564001740321 18325419353756673001305241)
  ·
    refine ⟨13744064515317504750978931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18325419353756673001305241 13744064515317504750978931)
    ·
      refine ⟨20616096772976257126468397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13744064515317504750978931 20616096772976257126468397)
      ·
        refine ⟨7731036289866096422425649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20616096772976257126468397 7731036289866096422425649)
        ·
          refine ⟨5798277217399572316819237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7731036289866096422425649 5798277217399572316819237)
          ·
            refine ⟨1087176978262419809403607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5798277217399572316819237 1087176978262419809403607)
            ·
              refine ⟨1630765467393629714105411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087176978262419809403607 1630765467393629714105411)
              ·
                refine ⟨2446148201090444571158117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630765467393629714105411 2446148201090444571158117)
                ·
                  refine ⟨458652787704458357092147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446148201090444571158117 458652787704458357092147)
                  ·
                    rfl

theorem cell20_1004876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_1004876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004876 prefixEnd_1004876 := by exact prefixLift 1004876
  have htrace : WordTrace (prefixWord ++ tailWord_1004876) baseStart_1004876 baseEnd_1004876 := by
    simpa [prefixWord, tailWord_1004876, baseEnd_1004876] using wordTrace_append hprefix tailTrace_1004876
  have hstable : (prefixWord ++ tailWord_1004876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004876).length < 2 ^ (prefixWord ++ tailWord_1004876).sum := by decide
  have hdescent : baseEnd_1004876 < baseStart_1004876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004914 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 2]
def baseStart_1004914 : Nat := 118140960795 + 1004914 * 2 ^ 59
def prefixEnd_1004914 : Nat := 4983230072969 + 3 ^ 40 * 1004914 * 2
def baseEnd_1004914 : Nat := 458670131939899113825325

theorem tailTrace_1004914 : CollatzResearch.WordTrace tailWord_1004914 prefixEnd_1004914 458670131939899113825325 := by
  unfold tailWord_1004914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163056170343919623123449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24434816454250452328329197 9163056170343919623123449)
  ·
    refine ⟨6872292127757939717342587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9163056170343919623123449 6872292127757939717342587)
    ·
      refine ⟨10308438191636909576013881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872292127757939717342587 10308438191636909576013881)
      ·
        refine ⟨7731328643727682182010411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10308438191636909576013881 7731328643727682182010411)
        ·
          refine ⟨11596992965591523273015617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7731328643727682182010411 11596992965591523273015617)
          ·
            refine ⟨8697744724193642454761713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11596992965591523273015617 8697744724193642454761713)
            ·
              refine ⟨6523308543145231841071285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8697744724193642454761713 6523308543145231841071285)
              ·
                refine ⟨611560175919865485100433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6523308543145231841071285 611560175919865485100433)
                ·
                  refine ⟨458670131939899113825325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611560175919865485100433 458670131939899113825325)
                  ·
                    rfl

theorem cell20_1004914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_1004914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004914 prefixEnd_1004914 := by exact prefixLift 1004914
  have htrace : WordTrace (prefixWord ++ tailWord_1004914) baseStart_1004914 baseEnd_1004914 := by
    simpa [prefixWord, tailWord_1004914, baseEnd_1004914] using wordTrace_append hprefix tailTrace_1004914
  have hstable : (prefixWord ++ tailWord_1004914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004914).length < 2 ^ (prefixWord ++ tailWord_1004914).sum := by decide
  have hdescent : baseEnd_1004914 < baseStart_1004914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004931 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 2]
def baseStart_1004931 : Nat := 118140960795 + 1004931 * 2 ^ 59
def prefixEnd_1004931 : Nat := 4983230072969 + 3 ^ 40 * 1004931 * 2
def baseEnd_1004931 : Nat := 458677891203122610258589

theorem tailTrace_1004931 : CollatzResearch.WordTrace tailWord_1004931 prefixEnd_1004931 458677891203122610258589 := by
  unfold tailWord_1004931
  simp only [CollatzResearch.WordTrace]
  refine ⟨36652844722314090395862647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24435229814876060263908431 36652844722314090395862647)
  ·
    refine ⟨54979267083471135593793971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36652844722314090395862647 54979267083471135593793971)
    ·
      refine ⟨82468900625206703390690957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54979267083471135593793971 82468900625206703390690957)
      ·
        refine ⟨30925837734452513771509109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82468900625206703390690957 30925837734452513771509109)
        ·
          refine ⟨2899297287604923166078979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30925837734452513771509109 2899297287604923166078979)
          ·
            refine ⟨4348945931407384749118469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899297287604923166078979 4348945931407384749118469)
            ·
              refine ⟨815427362138884640459713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4348945931407384749118469 815427362138884640459713)
              ·
                refine ⟨611570521604163480344785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815427362138884640459713 611570521604163480344785)
                ·
                  refine ⟨458677891203122610258589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611570521604163480344785 458677891203122610258589)
                  ·
                    rfl

theorem cell20_1004931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 2].length) (baseStart_1004931 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004931 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004931 prefixEnd_1004931 := by exact prefixLift 1004931
  have htrace : WordTrace (prefixWord ++ tailWord_1004931) baseStart_1004931 baseEnd_1004931 := by
    simpa [prefixWord, tailWord_1004931, baseEnd_1004931] using wordTrace_append hprefix tailTrace_1004931
  have hstable : (prefixWord ++ tailWord_1004931).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004931).length < 2 ^ (prefixWord ++ tailWord_1004931).sum := by decide
  have hdescent : baseEnd_1004931 < baseStart_1004931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004952 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 4]
def baseStart_1004952 : Nat := 118140960795 + 1004952 * 2 ^ 59
def prefixEnd_1004952 : Nat := 4983230072969 + 3 ^ 40 * 1004952 * 2
def baseEnd_1004952 : Nat := 458687476175339870558503

theorem tailTrace_1004952 : CollatzResearch.WordTrace tailWord_1004952 prefixEnd_1004952 458687476175339870558503 := by
  unfold tailWord_1004952
  simp only [CollatzResearch.WordTrace]
  refine ⟨18326805327619005491188555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24435740436825340654918073 18326805327619005491188555)
  ·
    refine ⟨27490207991428508236782833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18326805327619005491188555 27490207991428508236782833)
    ·
      refine ⟨20617655993571381177587125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27490207991428508236782833 20617655993571381177587125)
      ·
        refine ⟨1932905249397316985398793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20617655993571381177587125 1932905249397316985398793)
        ·
          refine ⟨1449678937047987739049095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932905249397316985398793 1449678937047987739049095)
          ·
            refine ⟨2174518405571981608573643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449678937047987739049095 2174518405571981608573643)
            ·
              refine ⟨3261777608357972412860465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174518405571981608573643 3261777608357972412860465)
              ·
                refine ⟨2446333206268479309645349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261777608357972412860465 2446333206268479309645349)
                ·
                  refine ⟨458687476175339870558503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446333206268479309645349 458687476175339870558503)
                  ·
                    rfl

theorem cell20_1004952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 4].length) (baseStart_1004952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004952 prefixEnd_1004952 := by exact prefixLift 1004952
  have htrace : WordTrace (prefixWord ++ tailWord_1004952) baseStart_1004952 baseEnd_1004952 := by
    simpa [prefixWord, tailWord_1004952, baseEnd_1004952] using wordTrace_append hprefix tailTrace_1004952
  have hstable : (prefixWord ++ tailWord_1004952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004952).length < 2 ^ (prefixWord ++ tailWord_1004952).sum := by decide
  have hdescent : baseEnd_1004952 < baseStart_1004952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004959 : List Nat := [1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_1004959 : Nat := 118140960795 + 1004959 * 2 ^ 59
def prefixEnd_1004959 : Nat := 4983230072969 + 3 ^ 40 * 1004959 * 2
def baseEnd_1004959 : Nat := 152896890388692985775047

theorem tailTrace_1004959 : CollatzResearch.WordTrace tailWord_1004959 prefixEnd_1004959 152896890388692985775047 := by
  unfold tailWord_1004959
  simp only [CollatzResearch.WordTrace]
  refine ⟨36653865966212651177881931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24435910644141767451921287 36653865966212651177881931)
  ·
    refine ⟨54980798949318976766822897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36653865966212651177881931 54980798949318976766822897)
    ·
      refine ⟨41235599211989232575117173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54980798949318976766822897 41235599211989232575117173)
      ·
        refine ⟨3865837426123990553917235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41235599211989232575117173 3865837426123990553917235)
        ·
          refine ⟨5798756139185985830875853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865837426123990553917235 5798756139185985830875853)
          ·
            refine ⟨2174533552194744686578445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5798756139185985830875853 2174533552194744686578445)
            ·
              refine ⟨815450082073029257466917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2174533552194744686578445 815450082073029257466917)
              ·
                refine ⟨152896890388692985775047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815450082073029257466917 152896890388692985775047)
                ·
                  rfl

theorem cell20_1004959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_1004959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1004959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1004959 prefixEnd_1004959 := by exact prefixLift 1004959
  have htrace : WordTrace (prefixWord ++ tailWord_1004959) baseStart_1004959 baseEnd_1004959 := by
    simpa [prefixWord, tailWord_1004959, baseEnd_1004959] using wordTrace_append hprefix tailTrace_1004959
  have hstable : (prefixWord ++ tailWord_1004959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004959).length < 2 ^ (prefixWord ++ tailWord_1004959).sum := by decide
  have hdescent : baseEnd_1004959 < baseStart_1004959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005001 : List Nat := [1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_1005001 : Nat := 118140960795 + 1005001 * 2 ^ 59
def prefixEnd_1005001 : Nat := 4983230072969 + 3 ^ 40 * 1005001 * 2
def baseEnd_1005001 : Nat := 152903280370171159308323

theorem tailTrace_1005001 : CollatzResearch.WordTrace tailWord_1005001 prefixEnd_1005001 152903280370171159308323 := by
  unfold tailWord_1005001
  simp only [CollatzResearch.WordTrace]
  refine ⟨36655397832060492350910857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24436931888040328233940571 36655397832060492350910857)
  ·
    refine ⟨27491548374045369263183143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36655397832060492350910857 27491548374045369263183143)
    ·
      refine ⟨41237322561068053894774715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27491548374045369263183143 41237322561068053894774715)
      ·
        refine ⟨61855983841602080842162073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41237322561068053894774715 61855983841602080842162073)
        ·
          refine ⟨46391987881201560631621555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61855983841602080842162073 46391987881201560631621555)
          ·
            refine ⟨69587981821802340947432333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46391987881201560631621555 69587981821802340947432333)
            ·
              refine ⟨26095493183175877855287125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69587981821802340947432333 26095493183175877855287125)
              ·
                refine ⟨152903280370171159308323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26095493183175877855287125 152903280370171159308323)
                ·
                  rfl

theorem cell20_1005001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_1005001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005001 prefixEnd_1005001 := by exact prefixLift 1005001
  have htrace : WordTrace (prefixWord ++ tailWord_1005001) baseStart_1005001 baseEnd_1005001 := by
    simpa [prefixWord, tailWord_1005001, baseEnd_1005001] using wordTrace_append hprefix tailTrace_1005001
  have hstable : (prefixWord ++ tailWord_1005001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005001).length < 2 ^ (prefixWord ++ tailWord_1005001).sum := by decide
  have hdescent : baseEnd_1005001 < baseStart_1005001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005014 : List Nat := [5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_1005014 : Nat := 118140960795 + 1005014 * 2 ^ 59
def prefixEnd_1005014 : Nat := 4983230072969 + 3 ^ 40 * 1005014 * 2
def baseEnd_1005014 : Nat := 152905258221581070163861

theorem tailTrace_1005014 : CollatzResearch.WordTrace tailWord_1005014 prefixEnd_1005014 152905258221581070163861 := by
  unfold tailWord_1005014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290991998813337223195881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24437247987342263714089397 2290991998813337223195881)
  ·
    refine ⟨1718243999110002917396911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2290991998813337223195881 1718243999110002917396911)
    ·
      refine ⟨2577365998665004376095367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718243999110002917396911 2577365998665004376095367)
      ·
        refine ⟨3866048997997506564143051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577365998665004376095367 3866048997997506564143051)
        ·
          refine ⟨5799073496996259846214577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866048997997506564143051 5799073496996259846214577)
          ·
            refine ⟨4349305122747194884660933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5799073496996259846214577 4349305122747194884660933)
            ·
              refine ⟨815494710515099040873925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4349305122747194884660933 815494710515099040873925)
              ·
                refine ⟨152905258221581070163861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815494710515099040873925 152905258221581070163861)
                ·
                  rfl

theorem cell20_1005014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_1005014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005014 prefixEnd_1005014 := by exact prefixLift 1005014
  have htrace : WordTrace (prefixWord ++ tailWord_1005014) baseStart_1005014 baseEnd_1005014 := by
    simpa [prefixWord, tailWord_1005014, baseEnd_1005014] using wordTrace_append hprefix tailTrace_1005014
  have hstable : (prefixWord ++ tailWord_1005014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005014).length < 2 ^ (prefixWord ++ tailWord_1005014).sum := by decide
  have hdescent : baseEnd_1005014 < baseStart_1005014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005018 : List Nat := [3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_1005018 : Nat := 118140960795 + 1005018 * 2 ^ 59
def prefixEnd_1005018 : Nat := 4983230072969 + 3 ^ 40 * 1005018 * 2
def baseEnd_1005018 : Nat := 152905866791245658119411

theorem tailTrace_1005018 : CollatzResearch.WordTrace tailWord_1005018 prefixEnd_1005018 152905866791245658119411 := by
  unfold tailWord_1005018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164004468249726063569927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24437345248665936169519805 9164004468249726063569927)
  ·
    refine ⟨13746006702374589095354891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9164004468249726063569927 13746006702374589095354891)
    ·
      refine ⟨20619010053561883643032337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746006702374589095354891 20619010053561883643032337)
      ·
        refine ⟨15464257540171412732274253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20619010053561883643032337 15464257540171412732274253)
        ·
          refine ⟨5799096577564279774602845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15464257540171412732274253 5799096577564279774602845)
          ·
            refine ⟨2174661216586604915476067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5799096577564279774602845 2174661216586604915476067)
            ·
              refine ⟨3261991824879907373214101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174661216586604915476067 3261991824879907373214101)
              ·
                refine ⟨152905866791245658119411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3261991824879907373214101 152905866791245658119411)
                ·
                  rfl

theorem cell20_1005018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_1005018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005018 prefixEnd_1005018 := by exact prefixLift 1005018
  have htrace : WordTrace (prefixWord ++ tailWord_1005018) baseStart_1005018 baseEnd_1005018 := by
    simpa [prefixWord, tailWord_1005018, baseEnd_1005018] using wordTrace_append hprefix tailTrace_1005018
  have hstable : (prefixWord ++ tailWord_1005018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005018).length < 2 ^ (prefixWord ++ tailWord_1005018).sum := by decide
  have hdescent : baseEnd_1005018 < baseStart_1005018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005025 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1005025 : Nat := 118140960795 + 1005025 * 2 ^ 59
def prefixEnd_1005025 : Nat := 4983230072969 + 3 ^ 40 * 1005025 * 2
def baseEnd_1005025 : Nat := 458720795364476061124871

theorem tailTrace_1005025 : CollatzResearch.WordTrace tailWord_1005025 prefixEnd_1005025 458720795364476061124871 := by
  unfold tailWord_1005025
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656273183973544449784529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24437515455982362966523019 36656273183973544449784529)
  ·
    refine ⟨27492204887980158337338397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36656273183973544449784529 27492204887980158337338397)
    ·
      refine ⟨10309576832992559376501899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27492204887980158337338397 10309576832992559376501899)
      ·
        refine ⟨15464365249488839064752849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10309576832992559376501899 15464365249488839064752849)
        ·
          refine ⟨11598273937116629298564637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15464365249488839064752849 11598273937116629298564637)
          ·
            refine ⟨4349352726418735986961739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11598273937116629298564637 4349352726418735986961739)
            ·
              refine ⟨6524029089628103980442609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4349352726418735986961739 6524029089628103980442609)
              ·
                refine ⟨4893021817221077985331957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6524029089628103980442609 4893021817221077985331957)
                ·
                  refine ⟨458720795364476061124871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4893021817221077985331957 458720795364476061124871)
                  ·
                    rfl

theorem cell20_1005025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1005025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005025 prefixEnd_1005025 := by exact prefixLift 1005025
  have htrace : WordTrace (prefixWord ++ tailWord_1005025) baseStart_1005025 baseEnd_1005025 := by
    simpa [prefixWord, tailWord_1005025, baseEnd_1005025] using wordTrace_append hprefix tailTrace_1005025
  have hstable : (prefixWord ++ tailWord_1005025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005025).length < 2 ^ (prefixWord ++ tailWord_1005025).sum := by decide
  have hdescent : baseEnd_1005025 < baseStart_1005025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005039 : List Nat := [1, 1, 2, 1, 4, 1, 10]
def baseStart_1005039 : Nat := 118140960795 + 1005039 * 2 ^ 59
def prefixEnd_1005039 : Nat := 4983230072969 + 3 ^ 40 * 1005039 * 2
def baseEnd_1005039 : Nat := 50969687260661581628683

theorem tailTrace_1005039 : CollatzResearch.WordTrace tailWord_1005039 prefixEnd_1005039 50969687260661581628683 := by
  unfold tailWord_1005039
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656783805922824840794171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24437855870615216560529447 36656783805922824840794171)
  ·
    refine ⟨54985175708884237261191257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36656783805922824840794171 54985175708884237261191257)
    ·
      refine ⟨41238881781663177945893443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54985175708884237261191257 41238881781663177945893443)
      ·
        refine ⟨61858322672494766918840165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41238881781663177945893443 61858322672494766918840165)
        ·
          refine ⟨11598435501092768797282531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61858322672494766918840165 11598435501092768797282531)
          ·
            refine ⟨17397653251639153195923797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11598435501092768797282531 17397653251639153195923797)
            ·
              refine ⟨50969687260661581628683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17397653251639153195923797 50969687260661581628683)
              ·
                rfl

theorem cell20_1005039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 10].length) (baseStart_1005039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005039 prefixEnd_1005039 := by exact prefixLift 1005039
  have htrace : WordTrace (prefixWord ++ tailWord_1005039) baseStart_1005039 baseEnd_1005039 := by
    simpa [prefixWord, tailWord_1005039, baseEnd_1005039] using wordTrace_append hprefix tailTrace_1005039
  have hstable : (prefixWord ++ tailWord_1005039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005039).length < 2 ^ (prefixWord ++ tailWord_1005039).sum := by decide
  have hdescent : baseEnd_1005039 < baseStart_1005039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005042 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_1005042 : Nat := 118140960795 + 1005042 * 2 ^ 59
def prefixEnd_1005042 : Nat := 4983230072969 + 3 ^ 40 * 1005042 * 2
def baseEnd_1005042 : Nat := 458728554627699557558135

theorem tailTrace_1005042 : CollatzResearch.WordTrace tailWord_1005042 prefixEnd_1005042 458728554627699557558135 := by
  unfold tailWord_1005042
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164223306227989088288345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24437928816607970902102253 9164223306227989088288345)
  ·
    refine ⟨6873167479670991816216259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9164223306227989088288345 6873167479670991816216259)
    ·
      refine ⟨10309751219506487724324389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873167479670991816216259 10309751219506487724324389)
      ·
        refine ⟨1933078353657466448310823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10309751219506487724324389 1933078353657466448310823)
        ·
          refine ⟨2899617530486199672466235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933078353657466448310823 2899617530486199672466235)
          ·
            refine ⟨4349426295729299508699353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2899617530486199672466235 4349426295729299508699353)
            ·
              refine ⟨3262069721796974631524515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4349426295729299508699353 3262069721796974631524515)
              ·
                refine ⟨4893104582695461947286773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3262069721796974631524515 4893104582695461947286773)
                ·
                  refine ⟨458728554627699557558135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4893104582695461947286773 458728554627699557558135)
                  ·
                    rfl

theorem cell20_1005042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_1005042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005042 prefixEnd_1005042 := by exact prefixLift 1005042
  have htrace : WordTrace (prefixWord ++ tailWord_1005042) baseStart_1005042 baseEnd_1005042 := by
    simpa [prefixWord, tailWord_1005042, baseEnd_1005042] using wordTrace_append hprefix tailTrace_1005042
  have hstable : (prefixWord ++ tailWord_1005042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005042).length < 2 ^ (prefixWord ++ tailWord_1005042).sum := by decide
  have hdescent : baseEnd_1005042 < baseStart_1005042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005045 : List Nat := [1, 3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_1005045 : Nat := 118140960795 + 1005045 * 2 ^ 59
def prefixEnd_1005045 : Nat := 4983230072969 + 3 ^ 40 * 1005045 * 2
def baseEnd_1005045 : Nat := 458729923909444880458123

theorem tailTrace_1005045 : CollatzResearch.WordTrace tailWord_1005045 prefixEnd_1005045 458729923909444880458123 := by
  unfold tailWord_1005045
  simp only [CollatzResearch.WordTrace]
  refine ⟨36657002643901087865512589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24438001762600725243675059 36657002643901087865512589)
  ·
    refine ⟨13746375991462907949567221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36657002643901087865512589 13746375991462907949567221)
    ·
      refine ⟨1288722749199647620271927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13746375991462907949567221 1288722749199647620271927)
      ·
        refine ⟨1933084123799471430407891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288722749199647620271927 1933084123799471430407891)
        ·
          refine ⟨2899626185699207145611837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933084123799471430407891 2899626185699207145611837)
          ·
            refine ⟨1087359819637202679604439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2899626185699207145611837 1087359819637202679604439)
            ·
              refine ⟨1631039729455804019406659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087359819637202679604439 1631039729455804019406659)
              ·
                refine ⟨2446559594183706029109989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631039729455804019406659 2446559594183706029109989)
                ·
                  refine ⟨458729923909444880458123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446559594183706029109989 458729923909444880458123)
                  ·
                    rfl

theorem cell20_1005045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_1005045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005045 prefixEnd_1005045 := by exact prefixLift 1005045
  have htrace : WordTrace (prefixWord ++ tailWord_1005045) baseStart_1005045 baseEnd_1005045 := by
    simpa [prefixWord, tailWord_1005045, baseEnd_1005045] using wordTrace_append hprefix tailTrace_1005045
  have hstable : (prefixWord ++ tailWord_1005045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005045).length < 2 ^ (prefixWord ++ tailWord_1005045).sum := by decide
  have hdescent : baseEnd_1005045 < baseStart_1005045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005153 : List Nat := [1, 2, 3, 1, 1, 3, 9]
def baseStart_1005153 : Nat := 118140960795 + 1005153 * 2 ^ 59
def prefixEnd_1005153 : Nat := 4983230072969 + 3 ^ 40 * 1005153 * 2
def baseEnd_1005153 : Nat := 50975468672475167206409

theorem tailTrace_1005153 : CollatzResearch.WordTrace tailWord_1005153 prefixEnd_1005153 50975468672475167206409 := by
  unfold tailWord_1005153
  simp only [CollatzResearch.WordTrace]
  refine ⟨36660941727509822310444113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24440627818339881540296075 36660941727509822310444113)
  ·
    refine ⟨27495706295632366732833085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36660941727509822310444113 27495706295632366732833085)
    ·
      refine ⟨10310889860862137524812407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27495706295632366732833085 10310889860862137524812407)
      ·
        refine ⟨15466334791293206287218611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310889860862137524812407 15466334791293206287218611)
        ·
          refine ⟨23199502186939809430827917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15466334791293206287218611 23199502186939809430827917)
          ·
            refine ⟨8699813320102428536560469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23199502186939809430827917 8699813320102428536560469)
            ·
              refine ⟨50975468672475167206409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8699813320102428536560469 50975468672475167206409)
              ·
                rfl

theorem cell20_1005153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_1005153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005153 prefixEnd_1005153 := by exact prefixLift 1005153
  have htrace : WordTrace (prefixWord ++ tailWord_1005153) baseStart_1005153 baseEnd_1005153 := by
    simpa [prefixWord, tailWord_1005153, baseEnd_1005153] using wordTrace_append hprefix tailTrace_1005153
  have hstable : (prefixWord ++ tailWord_1005153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005153).length < 2 ^ (prefixWord ++ tailWord_1005153).sum := by decide
  have hdescent : baseEnd_1005153 < baseStart_1005153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005156 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_1005156 : Nat := 118140960795 + 1005156 * 2 ^ 59
def prefixEnd_1005156 : Nat := 4983230072969 + 3 ^ 40 * 1005156 * 2
def baseEnd_1005156 : Nat := 458780587334021827757669

theorem tailTrace_1005156 : CollatzResearch.WordTrace tailWord_1005156 prefixEnd_1005156 458780587334021827757669 := by
  unfold tailWord_1005156
  simp only [CollatzResearch.WordTrace]
  refine ⟨18330525573249476911401661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24440700764332635881868881 18330525573249476911401661)
  ·
    refine ⟨6873947089968553841775623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18330525573249476911401661 6873947089968553841775623)
    ·
      refine ⟨10310920634952830762663435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873947089968553841775623 10310920634952830762663435)
      ·
        refine ⟨15466380952429246143995153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310920634952830762663435 15466380952429246143995153)
        ·
          refine ⟨11599785714321934607996365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15466380952429246143995153 11599785714321934607996365)
          ·
            refine ⟨4349919642870725477998637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11599785714321934607996365 4349919642870725477998637)
            ·
              refine ⟨1631219866076522054249489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4349919642870725477998637 1631219866076522054249489)
              ·
                refine ⟨1223414899557391540687117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631219866076522054249489 1223414899557391540687117)
                ·
                  refine ⟨458780587334021827757669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223414899557391540687117 458780587334021827757669)
                  ·
                    rfl

theorem cell20_1005156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_1005156 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005156 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005156 prefixEnd_1005156 := by exact prefixLift 1005156
  have htrace : WordTrace (prefixWord ++ tailWord_1005156) baseStart_1005156 baseEnd_1005156 := by
    simpa [prefixWord, tailWord_1005156, baseEnd_1005156] using wordTrace_append hprefix tailTrace_1005156
  have hstable : (prefixWord ++ tailWord_1005156).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005156).length < 2 ^ (prefixWord ++ tailWord_1005156).sum := by decide
  have hdescent : baseEnd_1005156 < baseStart_1005156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005184 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1005184 : Nat := 118140960795 + 1005184 * 2 ^ 59
def prefixEnd_1005184 : Nat := 4983230072969 + 3 ^ 40 * 1005184 * 2
def baseEnd_1005184 : Nat := 458793367296978174824221

theorem tailTrace_1005184 : CollatzResearch.WordTrace tailWord_1005184 prefixEnd_1005184 458793367296978174824221 := by
  unfold tailWord_1005184
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331036195198757302411303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24441381593598343069881737 18331036195198757302411303)
  ·
    refine ⟨27496554292798135953616955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18331036195198757302411303 27496554292798135953616955)
    ·
      refine ⟨41244831439197203930425433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27496554292798135953616955 41244831439197203930425433)
      ·
        refine ⟨30933623579397902947819075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41244831439197203930425433 30933623579397902947819075)
        ·
          refine ⟨46400435369096854421728613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30933623579397902947819075 46400435369096854421728613)
          ·
            refine ⟨8700081631705660204074115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46400435369096854421728613 8700081631705660204074115)
            ·
              refine ⟨13050122447558490306111173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700081631705660204074115 13050122447558490306111173)
              ·
                refine ⟨2446897958917216932395845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13050122447558490306111173 2446897958917216932395845)
                ·
                  refine ⟨458793367296978174824221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2446897958917216932395845 458793367296978174824221)
                  ·
                    rfl

theorem cell20_1005184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1005184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005184 prefixEnd_1005184 := by exact prefixLift 1005184
  have htrace : WordTrace (prefixWord ++ tailWord_1005184) baseStart_1005184 baseEnd_1005184 := by
    simpa [prefixWord, tailWord_1005184, baseEnd_1005184] using wordTrace_append hprefix tailTrace_1005184
  have hstable : (prefixWord ++ tailWord_1005184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005184).length < 2 ^ (prefixWord ++ tailWord_1005184).sum := by decide
  have hdescent : baseEnd_1005184 < baseStart_1005184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005201 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 2]
def baseStart_1005201 : Nat := 118140960795 + 1005201 * 2 ^ 59
def prefixEnd_1005201 : Nat := 4983230072969 + 3 ^ 40 * 1005201 * 2
def baseEnd_1005201 : Nat := 458801126560201671257485

theorem tailTrace_1005201 : CollatzResearch.WordTrace tailWord_1005201 prefixEnd_1005201 458801126560201671257485 := by
  unfold tailWord_1005201
  simp only [CollatzResearch.WordTrace]
  refine ⟨36662692431335926508191457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24441794954223951005460971 36662692431335926508191457)
  ·
    refine ⟨27497019323501944881143593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36662692431335926508191457 27497019323501944881143593)
    ·
      refine ⟨20622764492626458660857695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27497019323501944881143593 20622764492626458660857695)
      ·
        refine ⟨30934146738939687991286543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20622764492626458660857695 30934146738939687991286543)
        ·
          refine ⟨46401220108409531986929815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30934146738939687991286543 46401220108409531986929815)
          ·
            refine ⟨69601830162614297980394723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46401220108409531986929815 69601830162614297980394723)
            ·
              refine ⟨104402745243921446970592085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69601830162614297980394723 104402745243921446970592085)
              ·
                refine ⟨611734835413602228343313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 104402745243921446970592085 611734835413602228343313)
                ·
                  refine ⟨458801126560201671257485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611734835413602228343313 458801126560201671257485)
                  ·
                    rfl

theorem cell20_1005201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 2].length) (baseStart_1005201 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005201 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005201 prefixEnd_1005201 := by exact prefixLift 1005201
  have htrace : WordTrace (prefixWord ++ tailWord_1005201) baseStart_1005201 baseEnd_1005201 := by
    simpa [prefixWord, tailWord_1005201, baseEnd_1005201] using wordTrace_append hprefix tailTrace_1005201
  have hstable : (prefixWord ++ tailWord_1005201).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005201).length < 2 ^ (prefixWord ++ tailWord_1005201).sum := by decide
  have hdescent : baseEnd_1005201 < baseStart_1005201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005204 : List Nat := [2, 4, 2, 2, 3, 1, 6]
def baseStart_1005204 : Nat := 118140960795 + 1005204 * 2 ^ 59
def prefixEnd_1005204 : Nat := 4983230072969 + 3 ^ 40 * 1005204 * 2
def baseEnd_1005204 : Nat := 50978055093549666017497

theorem tailTrace_1005204 : CollatzResearch.WordTrace tailWord_1005204 prefixEnd_1005204 50978055093549666017497 := by
  unfold tailWord_1005204
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331400925162529010275333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24441867900216705347033777 18331400925162529010275333)
  ·
    refine ⟨3437137673467974189426625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18331400925162529010275333 3437137673467974189426625)
    ·
      refine ⟨2577853255100980642069969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3437137673467974189426625 2577853255100980642069969)
      ·
        refine ⟨1933389941325735481552477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2577853255100980642069969 1933389941325735481552477)
        ·
          refine ⟨725021227997150805582179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1933389941325735481552477 725021227997150805582179)
          ·
            refine ⟨1087531841995726208373269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725021227997150805582179 1087531841995726208373269)
            ·
              refine ⟨50978055093549666017497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1087531841995726208373269 50978055093549666017497)
              ·
                rfl

theorem cell20_1005204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 6].length) (baseStart_1005204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005204 prefixEnd_1005204 := by exact prefixLift 1005204
  have htrace : WordTrace (prefixWord ++ tailWord_1005204) baseStart_1005204 baseEnd_1005204 := by
    simpa [prefixWord, tailWord_1005204, baseEnd_1005204] using wordTrace_append hprefix tailTrace_1005204
  have hstable : (prefixWord ++ tailWord_1005204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005204).length < 2 ^ (prefixWord ++ tailWord_1005204).sum := by decide
  have hdescent : baseEnd_1005204 < baseStart_1005204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005208 : List Nat := [2, 1, 2, 4, 1, 4, 6]
def baseStart_1005208 : Nat := 118140960795 + 1005208 * 2 ^ 59
def prefixEnd_1005208 : Nat := 4983230072969 + 3 ^ 40 * 1005208 * 2
def baseEnd_1005208 : Nat := 50978257950104528669347

theorem tailTrace_1005208 : CollatzResearch.WordTrace tailWord_1005208 prefixEnd_1005208 50978257950104528669347 := by
  unfold tailWord_1005208
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331473871155283351848139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24441965161540377802464185 18331473871155283351848139)
  ·
    refine ⟨27497210806732925027772209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18331473871155283351848139 27497210806732925027772209)
    ·
      refine ⟨20622908105049693770829157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27497210806732925027772209 20622908105049693770829157)
      ·
        refine ⟨3866795269696817582030467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20622908105049693770829157 3866795269696817582030467)
        ·
          refine ⟨5800192904545226373045701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866795269696817582030467 5800192904545226373045701)
          ·
            refine ⟨1087536169602229944946069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5800192904545226373045701 1087536169602229944946069)
            ·
              refine ⟨50978257950104528669347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1087536169602229944946069 50978257950104528669347)
              ·
                rfl

theorem cell20_1005208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_1005208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005208 prefixEnd_1005208 := by exact prefixLift 1005208
  have htrace : WordTrace (prefixWord ++ tailWord_1005208) baseStart_1005208 baseEnd_1005208 := by
    simpa [prefixWord, tailWord_1005208, baseEnd_1005208] using wordTrace_append hprefix tailTrace_1005208
  have hstable : (prefixWord ++ tailWord_1005208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005208).length < 2 ^ (prefixWord ++ tailWord_1005208).sum := by decide
  have hdescent : baseEnd_1005208 < baseStart_1005208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005214 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1005214 : Nat := 118140960795 + 1005214 * 2 ^ 59
def prefixEnd_1005214 : Nat := 4983230072969 + 3 ^ 40 * 1005214 * 2
def baseEnd_1005214 : Nat := 458807060114431403824099

theorem tailTrace_1005214 : CollatzResearch.WordTrace tailWord_1005214 prefixEnd_1005214 458807060114431403824099 := by
  unfold tailWord_1005214
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582895822536103716051837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24442111053525886485609797 4582895822536103716051837)
  ·
    refine ⟨1718585933451038893519439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4582895822536103716051837 1718585933451038893519439)
    ·
      refine ⟨2577878900176558340279159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718585933451038893519439 2577878900176558340279159)
      ·
        refine ⟨3866818350264837510418739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577878900176558340279159 3866818350264837510418739)
        ·
          refine ⟨5800227525397256265628109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866818350264837510418739 5800227525397256265628109)
          ·
            refine ⟨2175085322023971099610541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5800227525397256265628109 2175085322023971099610541)
            ·
              refine ⟨815656995758989162353953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2175085322023971099610541 815656995758989162353953)
              ·
                refine ⟨611742746819241871765465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815656995758989162353953 611742746819241871765465)
                ·
                  refine ⟨458807060114431403824099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611742746819241871765465 458807060114431403824099)
                  ·
                    rfl

theorem cell20_1005214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1005214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005214 prefixEnd_1005214 := by exact prefixLift 1005214
  have htrace : WordTrace (prefixWord ++ tailWord_1005214) baseStart_1005214 baseEnd_1005214 := by
    simpa [prefixWord, tailWord_1005214, baseEnd_1005214] using wordTrace_append hprefix tailTrace_1005214
  have hstable : (prefixWord ++ tailWord_1005214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005214).length < 2 ^ (prefixWord ++ tailWord_1005214).sum := by decide
  have hdescent : baseEnd_1005214 < baseStart_1005214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005224 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_1005224 : Nat := 118140960795 + 1005224 * 2 ^ 59
def prefixEnd_1005224 : Nat := 4983230072969 + 3 ^ 40 * 1005224 * 2
def baseEnd_1005224 : Nat := 458811624386915813490725

theorem tailTrace_1005224 : CollatzResearch.WordTrace tailWord_1005224 prefixEnd_1005224 458811624386915813490725 := by
  unfold tailWord_1005224
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331765655126300718139363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24442354206835067624185817 18331765655126300718139363)
  ·
    refine ⟨27497648482689451077209045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18331765655126300718139363 27497648482689451077209045)
    ·
      refine ⟨644476136313034009622087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 27497648482689451077209045 644476136313034009622087)
      ·
        refine ⟨966714204469551014433131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644476136313034009622087 966714204469551014433131)
        ·
          refine ⟨1450071306704326521649697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966714204469551014433131 1450071306704326521649697)
          ·
            refine ⟨1087553480028244891237273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450071306704326521649697 1087553480028244891237273)
            ·
              refine ⟨815665110021183668427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087553480028244891237273 815665110021183668427955)
              ·
                refine ⟨1223497665031775502641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815665110021183668427955 1223497665031775502641933)
                ·
                  refine ⟨458811624386915813490725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223497665031775502641933 458811624386915813490725)
                  ·
                    rfl

theorem cell20_1005224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_1005224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005224 prefixEnd_1005224 := by exact prefixLift 1005224
  have htrace : WordTrace (prefixWord ++ tailWord_1005224) baseStart_1005224 baseEnd_1005224 := by
    simpa [prefixWord, tailWord_1005224, baseEnd_1005224] using wordTrace_append hprefix tailTrace_1005224
  have hstable : (prefixWord ++ tailWord_1005224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005224).length < 2 ^ (prefixWord ++ tailWord_1005224).sum := by decide
  have hdescent : baseEnd_1005224 < baseStart_1005224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005232 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_1005232 : Nat := 118140960795 + 1005232 * 2 ^ 59
def prefixEnd_1005232 : Nat := 4983230072969 + 3 ^ 40 * 1005232 * 2
def baseEnd_1005232 : Nat := 458815275804903341224025

theorem tailTrace_1005232 : CollatzResearch.WordTrace tailWord_1005232 prefixEnd_1005232 458815275804903341224025 := by
  unfold tailWord_1005232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331911547111809401284975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24442548729482412535046633 18331911547111809401284975)
  ·
    refine ⟨27497867320667714101927463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18331911547111809401284975 27497867320667714101927463)
    ·
      refine ⟨41246800981001571152891195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27497867320667714101927463 41246800981001571152891195)
      ·
        refine ⟨61870201471502356729336793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41246800981001571152891195 61870201471502356729336793)
        ·
          refine ⟨46402651103626767547002595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61870201471502356729336793 46402651103626767547002595)
          ·
            refine ⟨69603976655440151320503893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46402651103626767547002595 69603976655440151320503893)
            ·
              refine ⟨815671601430939273287155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69603976655440151320503893 815671601430939273287155)
              ·
                refine ⟨1223507402146408909930733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815671601430939273287155 1223507402146408909930733)
                ·
                  refine ⟨458815275804903341224025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223507402146408909930733 458815275804903341224025)
                  ·
                    rfl

theorem cell20_1005232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_1005232 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005232 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005232 prefixEnd_1005232 := by exact prefixLift 1005232
  have htrace : WordTrace (prefixWord ++ tailWord_1005232) baseStart_1005232 baseEnd_1005232 := by
    simpa [prefixWord, tailWord_1005232, baseEnd_1005232] using wordTrace_append hprefix tailTrace_1005232
  have hstable : (prefixWord ++ tailWord_1005232).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005232).length < 2 ^ (prefixWord ++ tailWord_1005232).sum := by decide
  have hdescent : baseEnd_1005232 < baseStart_1005232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005246 : List Nat := [4, 2, 1, 1, 2, 2, 2, 6]
def baseStart_1005246 : Nat := 118140960795 + 1005246 * 2 ^ 59
def prefixEnd_1005246 : Nat := 4983230072969 + 3 ^ 40 * 1005246 * 2
def baseEnd_1005246 : Nat := 152940555262127171585767

theorem tailTrace_1005246 : CollatzResearch.WordTrace tailWord_1005246 prefixEnd_1005246 152940555262127171585767 := by
  unfold tailWord_1005246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4583041714521612399197449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24442889144115266129053061 4583041714521612399197449)
  ·
    refine ⟨3437281285891209299398087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4583041714521612399197449 3437281285891209299398087)
    ·
      refine ⟨5155921928836813949097131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437281285891209299398087 5155921928836813949097131)
      ·
        refine ⟨7733882893255220923645697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5155921928836813949097131 7733882893255220923645697)
        ·
          refine ⟨5800412169941415692734273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7733882893255220923645697 5800412169941415692734273)
          ·
            refine ⟨4350309127456061769550705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800412169941415692734273 4350309127456061769550705)
            ·
              refine ⟨3262731845592046327163029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4350309127456061769550705 3262731845592046327163029)
              ·
                refine ⟨152940555262127171585767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3262731845592046327163029 152940555262127171585767)
                ·
                  rfl

theorem cell20_1005246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_1005246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005246 prefixEnd_1005246 := by exact prefixLift 1005246
  have htrace : WordTrace (prefixWord ++ tailWord_1005246) baseStart_1005246 baseEnd_1005246 := by
    simpa [prefixWord, tailWord_1005246, baseEnd_1005246] using wordTrace_append hprefix tailTrace_1005246
  have hstable : (prefixWord ++ tailWord_1005246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005246).length < 2 ^ (prefixWord ++ tailWord_1005246).sum := by decide
  have hdescent : baseEnd_1005246 < baseStart_1005246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005273 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 2]
def baseStart_1005273 : Nat := 118140960795 + 1005273 * 2 ^ 59
def prefixEnd_1005273 : Nat := 4983230072969 + 3 ^ 40 * 1005273 * 2
def baseEnd_1005273 : Nat := 458833989322089420857191

theorem tailTrace_1005273 : CollatzResearch.WordTrace tailWord_1005273 prefixEnd_1005273 458833989322089420857191 := by
  unfold tailWord_1005273
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665318487075082804812473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24443545658050055203208315 36665318487075082804812473)
  ·
    refine ⟨27498988865306312103609355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36665318487075082804812473 27498988865306312103609355)
    ·
      refine ⟨41248483297959468155414033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498988865306312103609355 41248483297959468155414033)
      ·
        refine ⟨30936362473469601116560525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41248483297959468155414033 30936362473469601116560525)
        ·
          refine ⟨11601135927551100418710197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30936362473469601116560525 11601135927551100418710197)
          ·
            refine ⟨1087606493207915664254081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11601135927551100418710197 1087606493207915664254081)
            ·
              refine ⟨815704869905936748190561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087606493207915664254081 815704869905936748190561)
              ·
                refine ⟨611778652429452561142921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 815704869905936748190561 611778652429452561142921)
                ·
                  refine ⟨458833989322089420857191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611778652429452561142921 458833989322089420857191)
                  ·
                    rfl

theorem cell20_1005273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 2].length) (baseStart_1005273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005273 prefixEnd_1005273 := by exact prefixLift 1005273
  have htrace : WordTrace (prefixWord ++ tailWord_1005273) baseStart_1005273 baseEnd_1005273 := by
    simpa [prefixWord, tailWord_1005273, baseEnd_1005273] using wordTrace_append hprefix tailTrace_1005273
  have hstable : (prefixWord ++ tailWord_1005273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005273).length < 2 ^ (prefixWord ++ tailWord_1005273).sum := by decide
  have hdescent : baseEnd_1005273 < baseStart_1005273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005291 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 3]
def baseStart_1005291 : Nat := 118140960795 + 1005291 * 2 ^ 59
def prefixEnd_1005291 : Nat := 4983230072969 + 3 ^ 40 * 1005291 * 2
def baseEnd_1005291 : Nat := 458842205012561358257117

theorem tailTrace_1005291 : CollatzResearch.WordTrace tailWord_1005291 prefixEnd_1005291 458842205012561358257117 := by
  unfold tailWord_1005291
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665975001009871878967727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24443983334006581252645151 36665975001009871878967727)
  ·
    refine ⟨54998962501514807818451591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36665975001009871878967727 54998962501514807818451591)
    ·
      refine ⟨82498443752272211727677387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54998962501514807818451591 82498443752272211727677387)
      ·
        refine ⟨123747665628408317591516081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82498443752272211727677387 123747665628408317591516081)
        ·
          refine ⟨92810749221306238193637061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123747665628408317591516081 92810749221306238193637061)
          ·
            refine ⟨17402015478994919661306949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92810749221306238193637061 17402015478994919661306949)
            ·
              refine ⟨3262877902311547436495053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17402015478994919661306949 3262877902311547436495053)
              ·
                refine ⟨1223579213366830288685645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3262877902311547436495053 1223579213366830288685645)
                ·
                  refine ⟨458842205012561358257117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223579213366830288685645 458842205012561358257117)
                  ·
                    rfl

theorem cell20_1005291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 3].length) (baseStart_1005291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005291 prefixEnd_1005291 := by exact prefixLift 1005291
  have htrace : WordTrace (prefixWord ++ tailWord_1005291) baseStart_1005291 baseEnd_1005291 := by
    simpa [prefixWord, tailWord_1005291, baseEnd_1005291] using wordTrace_append hprefix tailTrace_1005291
  have hstable : (prefixWord ++ tailWord_1005291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005291).length < 2 ^ (prefixWord ++ tailWord_1005291).sum := by decide
  have hdescent : baseEnd_1005291 < baseStart_1005291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005312 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_1005312 : Nat := 118140960795 + 1005312 * 2 ^ 59
def prefixEnd_1005312 : Nat := 4983230072969 + 3 ^ 40 * 1005312 * 2
def baseEnd_1005312 : Nat := 458851789984778618557031

theorem tailTrace_1005312 : CollatzResearch.WordTrace tailWord_1005312 prefixEnd_1005312 458851789984778618557031 := by
  unfold tailWord_1005312
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333370466966896232741095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24444493955955861643654793 18333370466966896232741095)
  ·
    refine ⟨27500055700450344349111643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333370466966896232741095 27500055700450344349111643)
    ·
      refine ⟨41250083550675516523667465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500055700450344349111643 41250083550675516523667465)
      ·
        refine ⟨30937562663006637392750599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41250083550675516523667465 30937562663006637392750599)
        ·
          refine ⟨46406343994509956089125899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30937562663006637392750599 46406343994509956089125899)
          ·
            refine ⟨69609515991764934133688849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46406343994509956089125899 69609515991764934133688849)
            ·
              refine ⟨52207136993823700600266637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69609515991764934133688849 52207136993823700600266637)
              ·
                refine ⟨19577676372683887725099989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52207136993823700600266637 19577676372683887725099989)
                ·
                  refine ⟨458851789984778618557031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19577676372683887725099989 458851789984778618557031)
                  ·
                    rfl

theorem cell20_1005312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_1005312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005312 prefixEnd_1005312 := by exact prefixLift 1005312
  have htrace : WordTrace (prefixWord ++ tailWord_1005312) baseStart_1005312 baseEnd_1005312 := by
    simpa [prefixWord, tailWord_1005312, baseEnd_1005312] using wordTrace_append hprefix tailTrace_1005312
  have hstable : (prefixWord ++ tailWord_1005312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005312).length < 2 ^ (prefixWord ++ tailWord_1005312).sum := by decide
  have hdescent : baseEnd_1005312 < baseStart_1005312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005315 : List Nat := [1, 1, 1, 3, 2, 2, 3, 5, 2]
def baseStart_1005315 : Nat := 118140960795 + 1005315 * 2 ^ 59
def prefixEnd_1005315 : Nat := 4983230072969 + 3 ^ 40 * 1005315 * 2
def baseEnd_1005315 : Nat := 458853159266523941457019

theorem tailTrace_1005315 : CollatzResearch.WordTrace tailWord_1005315 prefixEnd_1005315 458853159266523941457019 := by
  unfold tailWord_1005315
  simp only [CollatzResearch.WordTrace]
  refine ⟨36666850352922923977841399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24444566901948615985227599 36666850352922923977841399)
  ·
    refine ⟨55000275529384385966762099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36666850352922923977841399 55000275529384385966762099)
    ·
      refine ⟨82500413294076578950143149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55000275529384385966762099 82500413294076578950143149)
      ·
        refine ⟨30937654985278717106303681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82500413294076578950143149 30937654985278717106303681)
        ·
          refine ⟨23203241238959037829727761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30937654985278717106303681 23203241238959037829727761)
          ·
            refine ⟨17402430929219278372295821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23203241238959037829727761 17402430929219278372295821)
            ·
              refine ⟨6525911598457229389610933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17402430929219278372295821 6525911598457229389610933)
              ·
                refine ⟨611804212355365255276025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6525911598457229389610933 611804212355365255276025)
                ·
                  refine ⟨458853159266523941457019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611804212355365255276025 458853159266523941457019)
                  ·
                    rfl

theorem cell20_1005315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2].length) (baseStart_1005315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005315 prefixEnd_1005315 := by exact prefixLift 1005315
  have htrace : WordTrace (prefixWord ++ tailWord_1005315) baseStart_1005315 baseEnd_1005315 := by
    simpa [prefixWord, tailWord_1005315, baseEnd_1005315] using wordTrace_append hprefix tailTrace_1005315
  have hstable : (prefixWord ++ tailWord_1005315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005315).length < 2 ^ (prefixWord ++ tailWord_1005315).sum := by decide
  have hdescent : baseEnd_1005315 < baseStart_1005315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005336 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_1005336 : Nat := 118140960795 + 1005336 * 2 ^ 59
def prefixEnd_1005336 : Nat := 4983230072969 + 3 ^ 40 * 1005336 * 2
def baseEnd_1005336 : Nat := 458862744238741201756933

theorem tailTrace_1005336 : CollatzResearch.WordTrace tailWord_1005336 prefixEnd_1005336 458862744238741201756933 := by
  unfold tailWord_1005336
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333808142923422282177931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24445077523897896376237241 18333808142923422282177931)
  ·
    refine ⟨27500712214385133423266897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333808142923422282177931 27500712214385133423266897)
    ·
      refine ⟨20625534160788850067450173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27500712214385133423266897 20625534160788850067450173)
      ·
        refine ⟨7734575310295818775293815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20625534160788850067450173 7734575310295818775293815)
        ·
          refine ⟨11601862965443728162940723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734575310295818775293815 11601862965443728162940723)
          ·
            refine ⟨17402794448165592244411085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601862965443728162940723 17402794448165592244411085)
            ·
              refine ⟨6526047918062097091654157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17402794448165592244411085 6526047918062097091654157)
              ·
                refine ⟨2447267969273286409370309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6526047918062097091654157 2447267969273286409370309)
                ·
                  refine ⟨458862744238741201756933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2447267969273286409370309 458862744238741201756933)
                  ·
                    rfl

theorem cell20_1005336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_1005336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005336 prefixEnd_1005336 := by exact prefixLift 1005336
  have htrace : WordTrace (prefixWord ++ tailWord_1005336) baseStart_1005336 baseEnd_1005336 := by
    simpa [prefixWord, tailWord_1005336, baseEnd_1005336] using wordTrace_append hprefix tailTrace_1005336
  have hstable : (prefixWord ++ tailWord_1005336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005336).length < 2 ^ (prefixWord ++ tailWord_1005336).sum := by decide
  have hdescent : baseEnd_1005336 < baseStart_1005336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005343 : List Nat := [1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_1005343 : Nat := 118140960795 + 1005343 * 2 ^ 59
def prefixEnd_1005343 : Nat := 4983230072969 + 3 ^ 40 * 1005343 * 2
def baseEnd_1005343 : Nat := 152955313076493429507857

theorem tailTrace_1005343 : CollatzResearch.WordTrace tailWord_1005343 prefixEnd_1005343 152955313076493429507857 := by
  unfold tailWord_1005343
  simp only [CollatzResearch.WordTrace]
  refine ⟨36667871596821484759860683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24445247731214323173240455 36667871596821484759860683)
  ·
    refine ⟨55001807395232227139791025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36667871596821484759860683 55001807395232227139791025)
    ·
      refine ⟨41251355546424170354843269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55001807395232227139791025 41251355546424170354843269)
      ·
        refine ⟨7734629164954531941533113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41251355546424170354843269 7734629164954531941533113)
        ·
          refine ⟨5800971873715898956149835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7734629164954531941533113 5800971873715898956149835)
          ·
            refine ⟨8701457810573848434224753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800971873715898956149835 8701457810573848434224753)
            ·
              refine ⟨6526093357930386325668565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8701457810573848434224753 6526093357930386325668565)
              ·
                refine ⟨152955313076493429507857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6526093357930386325668565 152955313076493429507857)
                ·
                  rfl

theorem cell20_1005343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_1005343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005343 prefixEnd_1005343 := by exact prefixLift 1005343
  have htrace : WordTrace (prefixWord ++ tailWord_1005343) baseStart_1005343 baseEnd_1005343 := by
    simpa [prefixWord, tailWord_1005343, baseEnd_1005343] using wordTrace_append hprefix tailTrace_1005343
  have hstable : (prefixWord ++ tailWord_1005343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005343).length < 2 ^ (prefixWord ++ tailWord_1005343).sum := by decide
  have hdescent : baseEnd_1005343 < baseStart_1005343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005366 : List Nat := [5, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_1005366 : Nat := 118140960795 + 1005366 * 2 ^ 59
def prefixEnd_1005366 : Nat := 4983230072969 + 3 ^ 40 * 1005366 * 2
def baseEnd_1005366 : Nat := 458876437056194430756811

theorem tailTrace_1005366 : CollatzResearch.WordTrace tailWord_1005366 prefixEnd_1005366 458876437056194430756811 := by
  unfold tailWord_1005366
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291794404733634980496747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24445806983825439791965301 2291794404733634980496747)
  ·
    refine ⟨3437691607100452470745121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2291794404733634980496747 3437691607100452470745121)
    ·
      refine ⟨2578268705325339353058841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3437691607100452470745121 2578268705325339353058841)
      ·
        refine ⟨1933701528994004514794131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2578268705325339353058841 1933701528994004514794131)
        ·
          refine ⟨2900552293491006772191197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933701528994004514794131 2900552293491006772191197)
          ·
            refine ⟨1087707110059127539571699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2900552293491006772191197 1087707110059127539571699)
            ·
              refine ⟨1631560665088691309357549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087707110059127539571699 1631560665088691309357549)
              ·
                refine ⟨611835249408259241009081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631560665088691309357549 611835249408259241009081)
                ·
                  refine ⟨458876437056194430756811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611835249408259241009081 458876437056194430756811)
                  ·
                    rfl

theorem cell20_1005366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_1005366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005366 prefixEnd_1005366 := by exact prefixLift 1005366
  have htrace : WordTrace (prefixWord ++ tailWord_1005366) baseStart_1005366 baseEnd_1005366 := by
    simpa [prefixWord, tailWord_1005366, baseEnd_1005366] using wordTrace_append hprefix tailTrace_1005366
  have hstable : (prefixWord ++ tailWord_1005366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005366).length < 2 ^ (prefixWord ++ tailWord_1005366).sum := by decide
  have hdescent : baseEnd_1005366 < baseStart_1005366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005370 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 2]
def baseStart_1005370 : Nat := 118140960795 + 1005370 * 2 ^ 59
def prefixEnd_1005370 : Nat := 4983230072969 + 3 ^ 40 * 1005370 * 2
def baseEnd_1005370 : Nat := 458878262765188194623461

theorem tailTrace_1005370 : CollatzResearch.WordTrace tailWord_1005370 prefixEnd_1005370 458878262765188194623461 := by
  unfold tailWord_1005370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167214091930917092773391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24445904245149112247395709 9167214091930917092773391)
  ·
    refine ⟨13750821137896375639160087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9167214091930917092773391 13750821137896375639160087)
    ·
      refine ⟨20626231706844563458740131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13750821137896375639160087 20626231706844563458740131)
      ·
        refine ⟨30939347560266845188110197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20626231706844563458740131 30939347560266845188110197)
        ·
          refine ⟨2900563833775016736385331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30939347560266845188110197 2900563833775016736385331)
          ·
            refine ⟨4350845750662525104577997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900563833775016736385331 4350845750662525104577997)
            ·
              refine ⟨1631567156498446914216749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350845750662525104577997 1631567156498446914216749)
              ·
                refine ⟨611837683686917592831281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631567156498446914216749 611837683686917592831281)
                ·
                  refine ⟨458878262765188194623461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611837683686917592831281 458878262765188194623461)
                  ·
                    rfl

theorem cell20_1005370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 2].length) (baseStart_1005370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005370 prefixEnd_1005370 := by exact prefixLift 1005370
  have htrace : WordTrace (prefixWord ++ tailWord_1005370) baseStart_1005370 baseEnd_1005370 := by
    simpa [prefixWord, tailWord_1005370, baseEnd_1005370] using wordTrace_append hprefix tailTrace_1005370
  have hstable : (prefixWord ++ tailWord_1005370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005370).length < 2 ^ (prefixWord ++ tailWord_1005370).sum := by decide
  have hdescent : baseEnd_1005370 < baseStart_1005370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005443 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_1005443 : Nat := 118140960795 + 1005443 * 2 ^ 59
def prefixEnd_1005443 : Nat := 4983230072969 + 3 ^ 40 * 1005443 * 2
def baseEnd_1005443 : Nat := 458911581954324385189829

theorem tailTrace_1005443 : CollatzResearch.WordTrace tailWord_1005443 prefixEnd_1005443 458911581954324385189829 := by
  unfold tailWord_1005443
  simp only [CollatzResearch.WordTrace]
  refine ⟨36671518896459201838500983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24447679264306134559000655 36671518896459201838500983)
  ·
    refine ⟨55007278344688802757751475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36671518896459201838500983 55007278344688802757751475)
    ·
      refine ⟨82510917517033204136627213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55007278344688802757751475 82510917517033204136627213)
      ·
        refine ⟨30941594068887451551235205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82510917517033204136627213 30941594068887451551235205)
        ·
          refine ⟨5801548887916397165856601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30941594068887451551235205 5801548887916397165856601)
          ·
            refine ⟨4351161665937297874392451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5801548887916397165856601 4351161665937297874392451)
            ·
              refine ⟨6526742498905946811588677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351161665937297874392451 6526742498905946811588677)
              ·
                refine ⟨1223764218544865027172877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6526742498905946811588677 1223764218544865027172877)
                ·
                  refine ⟨458911581954324385189829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223764218544865027172877 458911581954324385189829)
                  ·
                    rfl

theorem cell20_1005443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_1005443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005443 prefixEnd_1005443 := by exact prefixLift 1005443
  have htrace : WordTrace (prefixWord ++ tailWord_1005443) baseStart_1005443 baseEnd_1005443 := by
    simpa [prefixWord, tailWord_1005443, baseEnd_1005443] using wordTrace_append hprefix tailTrace_1005443
  have hstable : (prefixWord ++ tailWord_1005443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005443).length < 2 ^ (prefixWord ++ tailWord_1005443).sum := by decide
  have hdescent : baseEnd_1005443 < baseStart_1005443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005457 : List Nat := [1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_1005457 : Nat := 118140960795 + 1005457 * 2 ^ 59
def prefixEnd_1005457 : Nat := 4983230072969 + 3 ^ 40 * 1005457 * 2
def baseEnd_1005457 : Nat := 152972657311934186241035

theorem tailTrace_1005457 : CollatzResearch.WordTrace tailWord_1005457 prefixEnd_1005457 152972657311934186241035 := by
  unfold tailWord_1005457
  simp only [CollatzResearch.WordTrace]
  refine ⟨36672029518408482229510625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24448019678938988153007083 36672029518408482229510625)
  ·
    refine ⟨27504022138806361672132969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36672029518408482229510625 27504022138806361672132969)
    ·
      refine ⟨20628016604104771254099727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27504022138806361672132969 20628016604104771254099727)
      ·
        refine ⟨30942024906157156881149591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20628016604104771254099727 30942024906157156881149591)
        ·
          refine ⟨46413037359235735321724387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30942024906157156881149591 46413037359235735321724387)
          ·
            refine ⟨69619556038853602982586581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46413037359235735321724387 69619556038853602982586581)
            ·
              refine ⟨1631708344660631319904373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69619556038853602982586581 1631708344660631319904373)
              ·
                refine ⟨152972657311934186241035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1631708344660631319904373 152972657311934186241035)
                ·
                  rfl

theorem cell20_1005457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_1005457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005457 prefixEnd_1005457 := by exact prefixLift 1005457
  have htrace : WordTrace (prefixWord ++ tailWord_1005457) baseStart_1005457 baseEnd_1005457 := by
    simpa [prefixWord, tailWord_1005457, baseEnd_1005457] using wordTrace_append hprefix tailTrace_1005457
  have hstable : (prefixWord ++ tailWord_1005457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005457).length < 2 ^ (prefixWord ++ tailWord_1005457).sum := by decide
  have hdescent : baseEnd_1005457 < baseStart_1005457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005460 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1005460 : Nat := 118140960795 + 1005460 * 2 ^ 59
def prefixEnd_1005460 : Nat := 4983230072969 + 3 ^ 40 * 1005460 * 2
def baseEnd_1005460 : Nat := 458919341217547881623093

theorem tailTrace_1005460 : CollatzResearch.WordTrace tailWord_1005460 prefixEnd_1005460 458919341217547881623093 := by
  unfold tailWord_1005460
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336069468698806870934917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24448092624931742494579889 18336069468698806870934917)
  ·
    refine ⟨3438013025381026288300297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18336069468698806870934917 3438013025381026288300297)
    ·
      refine ⟨2578509769035769716225223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3438013025381026288300297 2578509769035769716225223)
      ·
        refine ⟨3867764653553654574337835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578509769035769716225223 3867764653553654574337835)
        ·
          refine ⟨5801646980330481861506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867764653553654574337835 5801646980330481861506753)
          ·
            refine ⟨4351235235247861396130065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5801646980330481861506753 4351235235247861396130065)
            ·
              refine ⟨3263426426435896047097549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4351235235247861396130065 3263426426435896047097549)
              ·
                refine ⟨1223784909913461017661581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263426426435896047097549 1223784909913461017661581)
                ·
                  refine ⟨458919341217547881623093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223784909913461017661581 458919341217547881623093)
                  ·
                    rfl

theorem cell20_1005460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1005460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005460 prefixEnd_1005460 := by exact prefixLift 1005460
  have htrace : WordTrace (prefixWord ++ tailWord_1005460) baseStart_1005460 baseEnd_1005460 := by
    simpa [prefixWord, tailWord_1005460, baseEnd_1005460] using wordTrace_append hprefix tailTrace_1005460
  have hstable : (prefixWord ++ tailWord_1005460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005460).length < 2 ^ (prefixWord ++ tailWord_1005460).sum := by decide
  have hdescent : baseEnd_1005460 < baseStart_1005460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005480 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 2]
def baseStart_1005480 : Nat := 118140960795 + 1005480 * 2 ^ 59
def prefixEnd_1005480 : Nat := 4983230072969 + 3 ^ 40 * 1005480 * 2
def baseEnd_1005480 : Nat := 458928469762516700956345

theorem tailTrace_1005480 : CollatzResearch.WordTrace tailWord_1005480 prefixEnd_1005480 458928469762516700956345 := by
  unfold tailWord_1005480
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336434198662578578798947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24448578931550104771731929 18336434198662578578798947)
  ·
    refine ⟨27504651297993867868198421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18336434198662578578798947 27504651297993867868198421)
    ·
      refine ⟨1289280529593462556321801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27504651297993867868198421 1289280529593462556321801)
      ·
        refine ⟨966960397195096917241351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1289280529593462556321801 966960397195096917241351)
        ·
          refine ⟨1450440595792645375862027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966960397195096917241351 1450440595792645375862027)
          ·
            refine ⟨2175660893688968063793041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450440595792645375862027 2175660893688968063793041)
            ·
              refine ⟨1631745670266726047844781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2175660893688968063793041 1631745670266726047844781)
              ·
                refine ⟨611904626350022267941793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631745670266726047844781 611904626350022267941793)
                ·
                  refine ⟨458928469762516700956345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611904626350022267941793 458928469762516700956345)
                  ·
                    rfl

theorem cell20_1005480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 2].length) (baseStart_1005480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005480 prefixEnd_1005480 := by exact prefixLift 1005480
  have htrace : WordTrace (prefixWord ++ tailWord_1005480) baseStart_1005480 baseEnd_1005480 := by
    simpa [prefixWord, tailWord_1005480, baseEnd_1005480] using wordTrace_append hprefix tailTrace_1005480
  have hstable : (prefixWord ++ tailWord_1005480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005480).length < 2 ^ (prefixWord ++ tailWord_1005480).sum := by decide
  have hdescent : baseEnd_1005480 < baseStart_1005480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005529 : List Nat := [1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_1005529 : Nat := 118140960795 + 1005529 * 2 ^ 59
def prefixEnd_1005529 : Nat := 4983230072969 + 3 ^ 40 * 1005529 * 2
def baseEnd_1005529 : Nat := 152983611565896769440937

theorem tailTrace_1005529 : CollatzResearch.WordTrace tailWord_1005529 prefixEnd_1005529 152983611565896769440937 := by
  unfold tailWord_1005529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36674655574147638526131641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24449770382765092350754427 36674655574147638526131641)
  ·
    refine ⟨27505991680610728894598731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36674655574147638526131641 27505991680610728894598731)
    ·
      refine ⟨41258987520916093341898097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27505991680610728894598731 41258987520916093341898097)
      ·
        refine ⟨30944240640687070006423573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41258987520916093341898097 30944240640687070006423573)
        ·
          refine ⟨1450511280032206406551105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30944240640687070006423573 1450511280032206406551105)
          ·
            refine ⟨1087883460024154804913329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450511280032206406551105 1087883460024154804913329)
            ·
              refine ⟨815912595018116103684997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087883460024154804913329 815912595018116103684997)
              ·
                refine ⟨152983611565896769440937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 815912595018116103684997 152983611565896769440937)
                ·
                  rfl

theorem cell20_1005529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_1005529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005529 prefixEnd_1005529 := by exact prefixLift 1005529
  have htrace : WordTrace (prefixWord ++ tailWord_1005529) baseStart_1005529 baseEnd_1005529 := by
    simpa [prefixWord, tailWord_1005529, baseEnd_1005529] using wordTrace_append hprefix tailTrace_1005529
  have hstable : (prefixWord ++ tailWord_1005529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005529).length < 2 ^ (prefixWord ++ tailWord_1005529).sum := by decide
  have hdescent : baseEnd_1005529 < baseStart_1005529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005540 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_1005540 : Nat := 118140960795 + 1005540 * 2 ^ 59
def prefixEnd_1005540 : Nat := 4983230072969 + 3 ^ 40 * 1005540 * 2
def baseEnd_1005540 : Nat := 458955855397423158956099

theorem tailTrace_1005540 : CollatzResearch.WordTrace tailWord_1005540 prefixEnd_1005540 458955855397423158956099 := by
  unfold tailWord_1005540
  simp only [CollatzResearch.WordTrace]
  refine ⟨18337528388553893702391037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24450037851405191603188049 18337528388553893702391037)
  ·
    refine ⟨6876573145707710138396639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18337528388553893702391037 6876573145707710138396639)
    ·
      refine ⟨10314859718561565207594959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6876573145707710138396639 10314859718561565207594959)
      ·
        refine ⟨15472289577842347811392439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10314859718561565207594959 15472289577842347811392439)
        ·
          refine ⟨23208434366763521717088659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15472289577842347811392439 23208434366763521717088659)
          ·
            refine ⟨34812651550145282575632989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23208434366763521717088659 34812651550145282575632989)
            ·
              refine ⟨13054744331304480965862371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34812651550145282575632989 13054744331304480965862371)
              ·
                refine ⟨19582116496956721448793557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13054744331304480965862371 19582116496956721448793557)
                ·
                  refine ⟨458955855397423158956099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19582116496956721448793557 458955855397423158956099)
                  ·
                    rfl

theorem cell20_1005540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_1005540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005540 prefixEnd_1005540 := by exact prefixLift 1005540
  have htrace : WordTrace (prefixWord ++ tailWord_1005540) baseStart_1005540 baseEnd_1005540 := by
    simpa [prefixWord, tailWord_1005540, baseEnd_1005540] using wordTrace_append hprefix tailTrace_1005540
  have hstable : (prefixWord ++ tailWord_1005540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005540).length < 2 ^ (prefixWord ++ tailWord_1005540).sum := by decide
  have hdescent : baseEnd_1005540 < baseStart_1005540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005547 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1005547 : Nat := 118140960795 + 1005547 * 2 ^ 59
def prefixEnd_1005547 : Nat := 4983230072969 + 3 ^ 40 * 1005547 * 2
def baseEnd_1005547 : Nat := 458959050388162245722737

theorem tailTrace_1005547 : CollatzResearch.WordTrace tailWord_1005547 prefixEnd_1005547 458959050388162245722737 := by
  unfold tailWord_1005547
  simp only [CollatzResearch.WordTrace]
  refine ⟨36675312088082427600286895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24450208058721618400191263 36675312088082427600286895)
  ·
    refine ⟨55012968132123641400430343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36675312088082427600286895 55012968132123641400430343)
    ·
      refine ⟨82519452198185462100645515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55012968132123641400430343 82519452198185462100645515)
      ·
        refine ⟨123779178297278193150968273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82519452198185462100645515 123779178297278193150968273)
        ·
          refine ⟨92834383722958644863226205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123779178297278193150968273 92834383722958644863226205)
          ·
            refine ⟨34812893896109491823709827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92834383722958644863226205 34812893896109491823709827)
            ·
              refine ⟨52219340844164237735564741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34812893896109491823709827 52219340844164237735564741)
              ·
                refine ⟨9791126408280794575418389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52219340844164237735564741 9791126408280794575418389)
                ·
                  refine ⟨458959050388162245722737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9791126408280794575418389 458959050388162245722737)
                  ·
                    rfl

theorem cell20_1005547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1005547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005547 prefixEnd_1005547 := by exact prefixLift 1005547
  have htrace : WordTrace (prefixWord ++ tailWord_1005547) baseStart_1005547 baseEnd_1005547 := by
    simpa [prefixWord, tailWord_1005547, baseEnd_1005547] using wordTrace_append hprefix tailTrace_1005547
  have hstable : (prefixWord ++ tailWord_1005547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005547).length < 2 ^ (prefixWord ++ tailWord_1005547).sum := by decide
  have hdescent : baseEnd_1005547 < baseStart_1005547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005550 : List Nat := [4, 1, 2, 1, 3, 3, 6]
def baseStart_1005550 : Nat := 118140960795 + 1005550 * 2 ^ 59
def prefixEnd_1005550 : Nat := 4983230072969 + 3 ^ 40 * 1005550 * 2
def baseEnd_1005550 : Nat := 50995602185545285402525

theorem tailTrace_1005550 : CollatzResearch.WordTrace tailWord_1005550 prefixEnd_1005550 50995602185545285402525 := by
  unfold tailWord_1005550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584427688383944889080763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24450281004714372741764069 4584427688383944889080763)
  ·
    refine ⟨6876641532575917333621145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4584427688383944889080763 6876641532575917333621145)
    ·
      refine ⟨5157481149431938000215859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6876641532575917333621145 5157481149431938000215859)
      ·
        refine ⟨7736221724147907000323789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157481149431938000215859 7736221724147907000323789)
        ·
          refine ⟨2901083146555465125121421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7736221724147907000323789 2901083146555465125121421)
          ·
            refine ⟨1087906179958299421920533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2901083146555465125121421 1087906179958299421920533)
            ·
              refine ⟨50995602185545285402525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1087906179958299421920533 50995602185545285402525)
              ·
                rfl

theorem cell20_1005550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_1005550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005550 prefixEnd_1005550 := by exact prefixLift 1005550
  have htrace : WordTrace (prefixWord ++ tailWord_1005550) baseStart_1005550 baseEnd_1005550 := by
    simpa [prefixWord, tailWord_1005550, baseEnd_1005550] using wordTrace_append hprefix tailTrace_1005550
  have hstable : (prefixWord ++ tailWord_1005550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005550).length < 2 ^ (prefixWord ++ tailWord_1005550).sum := by decide
  have hdescent : baseEnd_1005550 < baseStart_1005550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005657 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 2]
def baseStart_1005657 : Nat := 118140960795 + 1005657 * 2 ^ 59
def prefixEnd_1005657 : Nat := 4983230072969 + 3 ^ 40 * 1005657 * 2
def baseEnd_1005657 : Nat := 459009257385490752055621

theorem tailTrace_1005657 : CollatzResearch.WordTrace tailWord_1005657 prefixEnd_1005657 459009257385490752055621 := by
  unfold tailWord_1005657
  simp only [CollatzResearch.WordTrace]
  refine ⟨36679324117683916386791225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24452882745122610924527483 36679324117683916386791225)
  ·
    refine ⟨27509493088262937290093419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36679324117683916386791225 27509493088262937290093419)
    ·
      refine ⟨41264239632394405935140129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27509493088262937290093419 41264239632394405935140129)
      ·
        refine ⟨30948179724295804451355097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41264239632394405935140129 30948179724295804451355097)
        ·
          refine ⟨23211134793221853338516323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30948179724295804451355097 23211134793221853338516323)
          ·
            refine ⟨34816702189832780007774485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23211134793221853338516323 34816702189832780007774485)
            ·
              refine ⟨1632032915148411562864429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34816702189832780007774485 1632032915148411562864429)
              ·
                refine ⟨612012343180654336074161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632032915148411562864429 612012343180654336074161)
                ·
                  refine ⟨459009257385490752055621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612012343180654336074161 459009257385490752055621)
                  ·
                    rfl

theorem cell20_1005657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_1005657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005657 prefixEnd_1005657 := by exact prefixLift 1005657
  have htrace : WordTrace (prefixWord ++ tailWord_1005657) baseStart_1005657 baseEnd_1005657 := by
    simpa [prefixWord, tailWord_1005657, baseEnd_1005657] using wordTrace_append hprefix tailTrace_1005657
  have hstable : (prefixWord ++ tailWord_1005657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005657).length < 2 ^ (prefixWord ++ tailWord_1005657).sum := by decide
  have hdescent : baseEnd_1005657 < baseStart_1005657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005795 : List Nat := [1, 1, 1, 8, 1, 2, 1, 5]
def baseStart_1005795 : Nat := 118140960795 + 1005795 * 2 ^ 59
def prefixEnd_1005795 : Nat := 4983230072969 + 3 ^ 40 * 1005795 * 2
def baseEnd_1005795 : Nat := 153024081448591868485019

theorem tailTrace_1005795 : CollatzResearch.WordTrace tailWord_1005795 prefixEnd_1005795 153024081448591868485019 := by
  unfold tailWord_1005795
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684357391183965955314839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24456238260789310636876559 36684357391183965955314839)
  ·
    refine ⟨55026536086775948932972259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36684357391183965955314839 55026536086775948932972259)
    ·
      refine ⟨82539804130163923399458389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55026536086775948932972259 82539804130163923399458389)
      ·
        refine ⟨967263329650358477337403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 82539804130163923399458389 967263329650358477337403)
        ·
          refine ⟨1450894994475537716006105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967263329650358477337403 1450894994475537716006105)
          ·
            refine ⟨1088171245856653287004579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1450894994475537716006105 1088171245856653287004579)
            ·
              refine ⟨1632256868784979930506869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088171245856653287004579 1632256868784979930506869)
              ·
                refine ⟨153024081448591868485019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1632256868784979930506869 153024081448591868485019)
                ·
                  rfl

theorem cell20_1005795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 5].length) (baseStart_1005795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005795 prefixEnd_1005795 := by exact prefixLift 1005795
  have htrace : WordTrace (prefixWord ++ tailWord_1005795) baseStart_1005795 baseEnd_1005795 := by
    simpa [prefixWord, tailWord_1005795, baseEnd_1005795] using wordTrace_append hprefix tailTrace_1005795
  have hstable : (prefixWord ++ tailWord_1005795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005795).length < 2 ^ (prefixWord ++ tailWord_1005795).sum := by decide
  have hdescent : baseEnd_1005795 < baseStart_1005795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005806 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1005806 : Nat := 118140960795 + 1005806 * 2 ^ 59
def prefixEnd_1005806 : Nat := 4983230072969 + 3 ^ 40 * 1005806 * 2
def baseEnd_1005806 : Nat := 459077265045508456088345

theorem tailTrace_1005806 : CollatzResearch.WordTrace tailWord_1005806 prefixEnd_1005806 459077265045508456088345 := by
  unfold tailWord_1005806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585594824268014354245659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24456505729429409889310181 4585594824268014354245659)
  ·
    refine ⟨6878392236402021531368489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4585594824268014354245659 6878392236402021531368489)
    ·
      refine ⟨5158794177301516148526367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6878392236402021531368489 5158794177301516148526367)
      ·
        refine ⟨7738191265952274222789551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158794177301516148526367 7738191265952274222789551)
        ·
          refine ⟨11607286898928411334184327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738191265952274222789551 11607286898928411334184327)
          ·
            refine ⟨17410930348392617001276491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11607286898928411334184327 17410930348392617001276491)
            ·
              refine ⟨26116395522588925501914737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17410930348392617001276491 26116395522588925501914737)
              ·
                refine ⟨19587296641941694126436053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26116395522588925501914737 19587296641941694126436053)
                ·
                  refine ⟨459077265045508456088345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19587296641941694126436053 459077265045508456088345)
                  ·
                    rfl

theorem cell20_1005806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1005806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005806 prefixEnd_1005806 := by exact prefixLift 1005806
  have htrace : WordTrace (prefixWord ++ tailWord_1005806) baseStart_1005806 baseEnd_1005806 := by
    simpa [prefixWord, tailWord_1005806, baseEnd_1005806] using wordTrace_append hprefix tailTrace_1005806
  have hstable : (prefixWord ++ tailWord_1005806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005806).length < 2 ^ (prefixWord ++ tailWord_1005806).sum := by decide
  have hdescent : baseEnd_1005806 < baseStart_1005806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005826 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1005826 : Nat := 118140960795 + 1005826 * 2 ^ 59
def prefixEnd_1005826 : Nat := 4983230072969 + 3 ^ 40 * 1005826 * 2
def baseEnd_1005826 : Nat := 459086393590477275421597

theorem tailTrace_1005826 : CollatzResearch.WordTrace tailWord_1005826 prefixEnd_1005826 459086393590477275421597 := by
  unfold tailWord_1005826
  simp only [CollatzResearch.WordTrace]
  refine ⟨9171372013517914562423333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24456992036047772166462221 9171372013517914562423333)
  ·
    refine ⟨1719632252534608980454375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9171372013517914562423333 1719632252534608980454375)
    ·
      refine ⟨2579448378801913470681563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1719632252534608980454375 2579448378801913470681563)
      ·
        refine ⟨3869172568202870206022345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2579448378801913470681563 3869172568202870206022345)
        ·
          refine ⟨2901879426152152654516759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3869172568202870206022345 2901879426152152654516759)
          ·
            refine ⟨4352819139228228981775139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901879426152152654516759 4352819139228228981775139)
            ·
              refine ⟨6529228708842343472662709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4352819139228228981775139 6529228708842343472662709)
              ·
                refine ⟨612115191453969700562129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6529228708842343472662709 612115191453969700562129)
                ·
                  refine ⟨459086393590477275421597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612115191453969700562129 459086393590477275421597)
                  ·
                    rfl

theorem cell20_1005826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1005826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005826 prefixEnd_1005826 := by exact prefixLift 1005826
  have htrace : WordTrace (prefixWord ++ tailWord_1005826) baseStart_1005826 baseEnd_1005826 := by
    simpa [prefixWord, tailWord_1005826, baseEnd_1005826] using wordTrace_append hprefix tailTrace_1005826
  have hstable : (prefixWord ++ tailWord_1005826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005826).length < 2 ^ (prefixWord ++ tailWord_1005826).sum := by decide
  have hdescent : baseEnd_1005826 < baseStart_1005826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005847 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 2]
def baseStart_1005847 : Nat := 118140960795 + 1005847 * 2 ^ 59
def prefixEnd_1005847 : Nat := 4983230072969 + 3 ^ 40 * 1005847 * 2
def baseEnd_1005847 : Nat := 459095978562694535721511

theorem tailTrace_1005847 : CollatzResearch.WordTrace tailWord_1005847 prefixEnd_1005847 459095978562694535721511 := by
  unfold tailWord_1005847
  simp only [CollatzResearch.WordTrace]
  refine ⟨36686253986995578836207795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24457502657997052557471863 36686253986995578836207795)
  ·
    refine ⟨55029380980493368254311693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36686253986995578836207795 55029380980493368254311693)
    ·
      refine ⟨20636017867685013095366885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55029380980493368254311693 20636017867685013095366885)
      ·
        refine ⟨3869253350190939955381291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20636017867685013095366885 3869253350190939955381291)
        ·
          refine ⟨5803880025286409933071937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3869253350190939955381291 5803880025286409933071937)
          ·
            refine ⟨4352910018964807449803953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5803880025286409933071937 4352910018964807449803953)
            ·
              refine ⟨3264682514223605587352965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4352910018964807449803953 3264682514223605587352965)
              ·
                refine ⟨612127971416926047628681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3264682514223605587352965 612127971416926047628681)
                ·
                  refine ⟨459095978562694535721511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612127971416926047628681 459095978562694535721511)
                  ·
                    rfl

theorem cell20_1005847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 2].length) (baseStart_1005847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005847 prefixEnd_1005847 := by exact prefixLift 1005847
  have htrace : WordTrace (prefixWord ++ tailWord_1005847) baseStart_1005847 baseEnd_1005847 := by
    simpa [prefixWord, tailWord_1005847, baseEnd_1005847] using wordTrace_append hprefix tailTrace_1005847
  have hstable : (prefixWord ++ tailWord_1005847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005847).length < 2 ^ (prefixWord ++ tailWord_1005847).sum := by decide
  have hdescent : baseEnd_1005847 < baseStart_1005847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005851 : List Nat := [1, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_1005851 : Nat := 118140960795 + 1005851 * 2 ^ 59
def prefixEnd_1005851 : Nat := 4983230072969 + 3 ^ 40 * 1005851 * 2
def baseEnd_1005851 : Nat := 459097804271688299588161

theorem tailTrace_1005851 : CollatzResearch.WordTrace tailWord_1005851 prefixEnd_1005851 459097804271688299588161 := by
  unfold tailWord_1005851
  simp only [CollatzResearch.WordTrace]
  refine ⟨36686399878981087519353407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24457599919320725012902271 36686399878981087519353407)
  ·
    refine ⟨55029599818471631279030111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36686399878981087519353407 55029599818471631279030111)
    ·
      refine ⟨82544399727707446918545167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55029599818471631279030111 82544399727707446918545167)
      ·
        refine ⟨123816599591561170377817751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82544399727707446918545167 123816599591561170377817751)
        ·
          refine ⟨185724899387341755566726627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123816599591561170377817751 185724899387341755566726627)
          ·
            refine ⟨278587349081012633350089941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185724899387341755566726627 278587349081012633350089941)
            ·
              refine ⟨6529390994086233594142733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 278587349081012633350089941 6529390994086233594142733)
              ·
                refine ⟨2448521622782337597803525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6529390994086233594142733 2448521622782337597803525)
                ·
                  refine ⟨459097804271688299588161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448521622782337597803525 459097804271688299588161)
                  ·
                    rfl

theorem cell20_1005851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_1005851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005851 prefixEnd_1005851 := by exact prefixLift 1005851
  have htrace : WordTrace (prefixWord ++ tailWord_1005851) baseStart_1005851 baseEnd_1005851 := by
    simpa [prefixWord, tailWord_1005851, baseEnd_1005851] using wordTrace_append hprefix tailTrace_1005851
  have hstable : (prefixWord ++ tailWord_1005851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005851).length < 2 ^ (prefixWord ++ tailWord_1005851).sum := by decide
  have hdescent : baseEnd_1005851 < baseStart_1005851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005882 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_1005882 : Nat := 118140960795 + 1005882 * 2 ^ 59
def prefixEnd_1005882 : Nat := 4983230072969 + 3 ^ 40 * 1005882 * 2
def baseEnd_1005882 : Nat := 459111953516389969554701

theorem tailTrace_1005882 : CollatzResearch.WordTrace tailWord_1005882 prefixEnd_1005882 459111953516389969554701 := by
  unfold tailWord_1005882
  simp only [CollatzResearch.WordTrace]
  refine ⟨9171882635467194953432975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24458353694579186542487933 9171882635467194953432975)
  ·
    refine ⟨13757823953200792430149463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9171882635467194953432975 13757823953200792430149463)
    ·
      refine ⟨20636735929801188645224195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13757823953200792430149463 20636735929801188645224195)
      ·
        refine ⟨30955103894701782967836293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20636735929801188645224195 30955103894701782967836293)
        ·
          refine ⟨5804081980256584306469305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30955103894701782967836293 5804081980256584306469305)
          ·
            refine ⟨4353061485192438229851979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5804081980256584306469305 4353061485192438229851979)
            ·
              refine ⟨6529592227788657344777969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4353061485192438229851979 6529592227788657344777969)
              ·
                refine ⟨4897194170841493008583477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6529592227788657344777969 4897194170841493008583477)
                ·
                  refine ⟨459111953516389969554701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4897194170841493008583477 459111953516389969554701)
                  ·
                    rfl

theorem cell20_1005882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_1005882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005882 prefixEnd_1005882 := by exact prefixLift 1005882
  have htrace : WordTrace (prefixWord ++ tailWord_1005882) baseStart_1005882 baseEnd_1005882 := by
    simpa [prefixWord, tailWord_1005882, baseEnd_1005882] using wordTrace_append hprefix tailTrace_1005882
  have hstable : (prefixWord ++ tailWord_1005882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005882).length < 2 ^ (prefixWord ++ tailWord_1005882).sum := by decide
  have hdescent : baseEnd_1005882 < baseStart_1005882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005896 : List Nat := [2, 1, 3, 1, 1, 2, 10]
def baseStart_1005896 : Nat := 118140960795 + 1005896 * 2 ^ 59
def prefixEnd_1005896 : Nat := 4983230072969 + 3 ^ 40 * 1005896 * 2
def baseEnd_1005896 : Nat := 51013149277540904787553

theorem tailTrace_1005896 : CollatzResearch.WordTrace tailWord_1005896 prefixEnd_1005896 51013149277540904787553 := by
  unfold tailWord_1005896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18344020581909030102370771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24458694109212040136494361 18344020581909030102370771)
  ·
    refine ⟨27516030872863545153556157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18344020581909030102370771 27516030872863545153556157)
    ·
      refine ⟨10318511577323829432583559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27516030872863545153556157 10318511577323829432583559)
      ·
        refine ⟨15477767365985744148875339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318511577323829432583559 15477767365985744148875339)
        ·
          refine ⟨23216651048978616223313009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15477767365985744148875339 23216651048978616223313009)
          ·
            refine ⟨17412488286733962167484757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23216651048978616223313009 17412488286733962167484757)
            ·
              refine ⟨51013149277540904787553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17412488286733962167484757 51013149277540904787553)
              ·
                rfl

theorem cell20_1005896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 10].length) (baseStart_1005896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005896 prefixEnd_1005896 := by exact prefixLift 1005896
  have htrace : WordTrace (prefixWord ++ tailWord_1005896) baseStart_1005896 baseEnd_1005896 := by
    simpa [prefixWord, tailWord_1005896, baseEnd_1005896] using wordTrace_append hprefix tailTrace_1005896
  have hstable : (prefixWord ++ tailWord_1005896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005896).length < 2 ^ (prefixWord ++ tailWord_1005896).sum := by decide
  have hdescent : baseEnd_1005896 < baseStart_1005896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005906 : List Nat := [3, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_1005906 : Nat := 118140960795 + 1005906 * 2 ^ 59
def prefixEnd_1005906 : Nat := 4983230072969 + 3 ^ 40 * 1005906 * 2
def baseEnd_1005906 : Nat := 459122907770352552754603

theorem tailTrace_1005906 : CollatzResearch.WordTrace tailWord_1005906 prefixEnd_1005906 459122907770352552754603 := by
  unfold tailWord_1005906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9172101473445457978151393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24458937262521221275070381 9172101473445457978151393)
  ·
    refine ⟨6879076105084093483613545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9172101473445457978151393 6879076105084093483613545)
    ·
      refine ⟨5159307078813070112710159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6879076105084093483613545 5159307078813070112710159)
      ·
        refine ⟨7738960618219605169065239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159307078813070112710159 7738960618219605169065239)
        ·
          refine ⟨11608440927329407753597859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738960618219605169065239 11608440927329407753597859)
          ·
            refine ⟨17412661390994111630396789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11608440927329407753597859 17412661390994111630396789)
            ·
              refine ⟨1632437005405697965349699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17412661390994111630396789 1632437005405697965349699)
              ·
                refine ⟨2448655508108546948024549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632437005405697965349699 2448655508108546948024549)
                ·
                  refine ⟨459122907770352552754603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448655508108546948024549 459122907770352552754603)
                  ·
                    rfl

theorem cell20_1005906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_1005906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005906 prefixEnd_1005906 := by exact prefixLift 1005906
  have htrace : WordTrace (prefixWord ++ tailWord_1005906) baseStart_1005906 baseEnd_1005906 := by
    simpa [prefixWord, tailWord_1005906, baseEnd_1005906] using wordTrace_append hprefix tailTrace_1005906
  have hstable : (prefixWord ++ tailWord_1005906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005906).length < 2 ^ (prefixWord ++ tailWord_1005906).sum := by decide
  have hdescent : baseEnd_1005906 < baseStart_1005906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005961 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 2]
def baseStart_1005961 : Nat := 118140960795 + 1005961 * 2 ^ 59
def prefixEnd_1005961 : Nat := 4983230072969 + 3 ^ 40 * 1005961 * 2
def baseEnd_1005961 : Nat := 459148011269016805921045

theorem tailTrace_1005961 : CollatzResearch.WordTrace tailWord_1005961 prefixEnd_1005961 459148011269016805921045 := by
  unfold tailWord_1005961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36690411908582576305857737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24460274605721717537238491 36690411908582576305857737)
  ·
    refine ⟨27517808931436932229393303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36690411908582576305857737 27517808931436932229393303)
    ·
      refine ⟨41276713397155398344089955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27517808931436932229393303 41276713397155398344089955)
      ·
        refine ⟨61915070095733097516134933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41276713397155398344089955 61915070095733097516134933)
        ·
          refine ⟨2902268910737488946068825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61915070095733097516134933 2902268910737488946068825)
          ·
            refine ⟨2176701683053116709551619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2902268910737488946068825 2176701683053116709551619)
            ·
              refine ⟨3265052524579675064327429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176701683053116709551619 3265052524579675064327429)
              ·
                refine ⟨612197348358689074561393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3265052524579675064327429 612197348358689074561393)
                ·
                  refine ⟨459148011269016805921045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612197348358689074561393 459148011269016805921045)
                  ·
                    rfl

theorem cell20_1005961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_1005961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005961 prefixEnd_1005961 := by exact prefixLift 1005961
  have htrace : WordTrace (prefixWord ++ tailWord_1005961) baseStart_1005961 baseEnd_1005961 := by
    simpa [prefixWord, tailWord_1005961, baseEnd_1005961] using wordTrace_append hprefix tailTrace_1005961
  have hstable : (prefixWord ++ tailWord_1005961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005961).length < 2 ^ (prefixWord ++ tailWord_1005961).sum := by decide
  have hdescent : baseEnd_1005961 < baseStart_1005961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005985 : List Nat := [1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_1005985 : Nat := 118140960795 + 1005985 * 2 ^ 59
def prefixEnd_1005985 : Nat := 4983230072969 + 3 ^ 40 * 1005985 * 2
def baseEnd_1005985 : Nat := 153052988507659796373649

theorem tailTrace_1005985 : CollatzResearch.WordTrace tailWord_1005985 prefixEnd_1005985 153052988507659796373649 := by
  unfold tailWord_1005985
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691287260495628404731409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24460858173663752269820939 36691287260495628404731409)
  ·
    refine ⟨27518465445371721303548557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36691287260495628404731409 27518465445371721303548557)
    ·
      refine ⟨10319424542014395488830709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27518465445371721303548557 10319424542014395488830709)
      ·
        refine ⟨967446050813849577077879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10319424542014395488830709 967446050813849577077879)
        ·
          refine ⟨1451169076220774365616819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967446050813849577077879 1451169076220774365616819)
          ·
            refine ⟨2176753614331161548425229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451169076220774365616819 2176753614331161548425229)
            ·
              refine ⟨816282605374185580659461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2176753614331161548425229 816282605374185580659461)
              ·
                refine ⟨153052988507659796373649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816282605374185580659461 153052988507659796373649)
                ·
                  rfl

theorem cell20_1005985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_1005985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005985 prefixEnd_1005985 := by exact prefixLift 1005985
  have htrace : WordTrace (prefixWord ++ tailWord_1005985) baseStart_1005985 baseEnd_1005985 := by
    simpa [prefixWord, tailWord_1005985, baseEnd_1005985] using wordTrace_append hprefix tailTrace_1005985
  have hstable : (prefixWord ++ tailWord_1005985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005985).length < 2 ^ (prefixWord ++ tailWord_1005985).sum := by decide
  have hdescent : baseEnd_1005985 < baseStart_1005985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005989 : List Nat := [1, 3, 1, 2, 1, 1, 7, 4]
def baseStart_1005989 : Nat := 118140960795 + 1005989 * 2 ^ 59
def prefixEnd_1005989 : Nat := 4983230072969 + 3 ^ 40 * 1005989 * 2
def baseEnd_1005989 : Nat := 153053597077324384329199

theorem tailTrace_1005989 : CollatzResearch.WordTrace tailWord_1005989 prefixEnd_1005989 153053597077324384329199 := by
  unfold tailWord_1005989
  simp only [CollatzResearch.WordTrace]
  refine ⟨36691433152481137087877021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24460955434987424725251347 36691433152481137087877021)
  ·
    refine ⟨13759287432180426407953883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36691433152481137087877021 13759287432180426407953883)
    ·
      refine ⟨20638931148270639611930825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13759287432180426407953883 20638931148270639611930825)
      ·
        refine ⟨15479198361202979708948119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20638931148270639611930825 15479198361202979708948119)
        ·
          refine ⟨23218797541804469563422179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15479198361202979708948119 23218797541804469563422179)
          ·
            refine ⟨34828196312706704345133269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23218797541804469563422179 34828196312706704345133269)
            ·
              refine ⟨816285851079063383089061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34828196312706704345133269 816285851079063383089061)
              ·
                refine ⟨153053597077324384329199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816285851079063383089061 153053597077324384329199)
                ·
                  rfl

theorem cell20_1005989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_1005989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1005989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1005989 prefixEnd_1005989 := by exact prefixLift 1005989
  have htrace : WordTrace (prefixWord ++ tailWord_1005989) baseStart_1005989 baseEnd_1005989 := by
    simpa [prefixWord, tailWord_1005989, baseEnd_1005989] using wordTrace_append hprefix tailTrace_1005989
  have hstable : (prefixWord ++ tailWord_1005989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005989).length < 2 ^ (prefixWord ++ tailWord_1005989).sum := by decide
  have hdescent : baseEnd_1005989 < baseStart_1005989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006013 : List Nat := [1, 4, 1, 2, 2, 2, 3, 2, 3]
def baseStart_1006013 : Nat := 118140960795 + 1006013 * 2 ^ 59
def prefixEnd_1006013 : Nat := 4983230072969 + 3 ^ 40 * 1006013 * 2
def baseEnd_1006013 : Nat := 459171745485935736187499

theorem tailTrace_1006013 : CollatzResearch.WordTrace tailWord_1006013 prefixEnd_1006013 459171745485935736187499 := by
  unfold tailWord_1006013
  simp only [CollatzResearch.WordTrace]
  refine ⟨36692308504394189186750693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24461539002929459457833795 36692308504394189186750693)
  ·
    refine ⟨6879807844573910472515755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36692308504394189186750693 6879807844573910472515755)
    ·
      refine ⟨10319711766860865708773633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6879807844573910472515755 10319711766860865708773633)
      ·
        refine ⟨7739783825145649281580225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10319711766860865708773633 7739783825145649281580225)
        ·
          refine ⟨5804837868859236961185169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739783825145649281580225 5804837868859236961185169)
          ·
            refine ⟨4353628401644427720888877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5804837868859236961185169 4353628401644427720888877)
            ·
              refine ⟨1632610650616660395333329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4353628401644427720888877 1632610650616660395333329)
              ·
                refine ⟨1224457987962495296499997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632610650616660395333329 1224457987962495296499997)
                ·
                  refine ⟨459171745485935736187499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224457987962495296499997 459171745485935736187499)
                  ·
                    rfl

theorem cell20_1006013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_1006013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006013 prefixEnd_1006013 := by exact prefixLift 1006013
  have htrace : WordTrace (prefixWord ++ tailWord_1006013) baseStart_1006013 baseEnd_1006013 := by
    simpa [prefixWord, tailWord_1006013, baseEnd_1006013] using wordTrace_append hprefix tailTrace_1006013
  have hstable : (prefixWord ++ tailWord_1006013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006013).length < 2 ^ (prefixWord ++ tailWord_1006013).sum := by decide
  have hdescent : baseEnd_1006013 < baseStart_1006013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006041 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 4]
def baseStart_1006041 : Nat := 118140960795 + 1006041 * 2 ^ 59
def prefixEnd_1006041 : Nat := 4983230072969 + 3 ^ 40 * 1006041 * 2
def baseEnd_1006041 : Nat := 459184525448892083254051

theorem tailTrace_1006041 : CollatzResearch.WordTrace tailWord_1006041 prefixEnd_1006041 459184525448892083254051 := by
  unfold tailWord_1006041
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693329748292749968769977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24462219832195166645846651 36693329748292749968769977)
  ·
    refine ⟨27519997311219562476577483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36693329748292749968769977 27519997311219562476577483)
    ·
      refine ⟨41279995966829343714866225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27519997311219562476577483 41279995966829343714866225)
      ·
        refine ⟨30959996975122007786149669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41279995966829343714866225 30959996975122007786149669)
        ·
          refine ⟨5804999432835376459903063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30959996975122007786149669 5804999432835376459903063)
          ·
            refine ⟨8707499149253064689854595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804999432835376459903063 8707499149253064689854595)
            ·
              refine ⟨13061248723879597034781893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707499149253064689854595 13061248723879597034781893)
              ·
                refine ⟨2448984135727424444021605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13061248723879597034781893 2448984135727424444021605)
                ·
                  refine ⟨459184525448892083254051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2448984135727424444021605 459184525448892083254051)
                  ·
                    rfl

theorem cell20_1006041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 4].length) (baseStart_1006041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006041 prefixEnd_1006041 := by exact prefixLift 1006041
  have htrace : WordTrace (prefixWord ++ tailWord_1006041) baseStart_1006041 baseEnd_1006041 := by
    simpa [prefixWord, tailWord_1006041, baseEnd_1006041] using wordTrace_append hprefix tailTrace_1006041
  have hstable : (prefixWord ++ tailWord_1006041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006041).length < 2 ^ (prefixWord ++ tailWord_1006041).sum := by decide
  have hdescent : baseEnd_1006041 < baseStart_1006041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006048 : List Nat := [2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_1006048 : Nat := 118140960795 + 1006048 * 2 ^ 59
def prefixEnd_1006048 : Nat := 4983230072969 + 3 ^ 40 * 1006048 * 2
def baseEnd_1006048 : Nat := 153062573479877056673563

theorem tailTrace_1006048 : CollatzResearch.WordTrace tailWord_1006048 prefixEnd_1006048 153062573479877056673563 := by
  unfold tailWord_1006048
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346792529633695082137399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24462390039511593442849865 18346792529633695082137399)
  ·
    refine ⟨27520188794450542623206099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18346792529633695082137399 27520188794450542623206099)
    ·
      refine ⟨41280283191675813934809149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27520188794450542623206099 41280283191675813934809149)
      ·
        refine ⟨15480106196878430225553431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41280283191675813934809149 15480106196878430225553431)
        ·
          refine ⟨23220159295317645338330147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15480106196878430225553431 23220159295317645338330147)
          ·
            refine ⟨34830238942976468007495221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23220159295317645338330147 34830238942976468007495221)
            ·
              refine ⟨3265334900904043875702677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34830238942976468007495221 3265334900904043875702677)
              ·
                refine ⟨153062573479877056673563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3265334900904043875702677 153062573479877056673563)
                ·
                  rfl

theorem cell20_1006048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_1006048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006048 prefixEnd_1006048 := by exact prefixLift 1006048
  have htrace : WordTrace (prefixWord ++ tailWord_1006048) baseStart_1006048 baseEnd_1006048 := by
    simpa [prefixWord, tailWord_1006048, baseEnd_1006048] using wordTrace_append hprefix tailTrace_1006048
  have hstable : (prefixWord ++ tailWord_1006048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006048).length < 2 ^ (prefixWord ++ tailWord_1006048).sum := by decide
  have hdescent : baseEnd_1006048 < baseStart_1006048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006050 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 2]
def baseStart_1006050 : Nat := 118140960795 + 1006050 * 2 ^ 59
def prefixEnd_1006050 : Nat := 4983230072969 + 3 ^ 40 * 1006050 * 2
def baseEnd_1006050 : Nat := 459188633294128051954015

theorem tailTrace_1006050 : CollatzResearch.WordTrace tailWord_1006050 prefixEnd_1006050 459188633294128051954015 := by
  unfold tailWord_1006050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9173414501315036126461901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24462438670173429670565069 9173414501315036126461901)
  ·
    refine ⟨3440030437993138547423213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9173414501315036126461901 3440030437993138547423213)
    ·
      refine ⟨1290011414247426955283705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3440030437993138547423213 1290011414247426955283705)
      ·
        refine ⟨967508560685570216462779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1290011414247426955283705 967508560685570216462779)
        ·
          refine ⟨1451262841028355324694169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967508560685570216462779 1451262841028355324694169)
          ·
            refine ⟨1088447130771266493520627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451262841028355324694169 1088447130771266493520627)
            ·
              refine ⟨1632670696156899740280941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088447130771266493520627 1632670696156899740280941)
              ·
                refine ⟨612251511058837402605353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1632670696156899740280941 612251511058837402605353)
                ·
                  refine ⟨459188633294128051954015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612251511058837402605353 459188633294128051954015)
                  ·
                    rfl

theorem cell20_1006050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_1006050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006050 prefixEnd_1006050 := by exact prefixLift 1006050
  have htrace : WordTrace (prefixWord ++ tailWord_1006050) baseStart_1006050 baseEnd_1006050 := by
    simpa [prefixWord, tailWord_1006050, baseEnd_1006050] using wordTrace_append hprefix tailTrace_1006050
  have hstable : (prefixWord ++ tailWord_1006050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006050).length < 2 ^ (prefixWord ++ tailWord_1006050).sum := by decide
  have hdescent : baseEnd_1006050 < baseStart_1006050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006072 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1006072 : Nat := 118140960795 + 1006072 * 2 ^ 59
def prefixEnd_1006072 : Nat := 4983230072969 + 3 ^ 40 * 1006072 * 2
def baseEnd_1006072 : Nat := 459198674693593753220591

theorem tailTrace_1006072 : CollatzResearch.WordTrace tailWord_1006072 prefixEnd_1006072 459198674693593753220591 := by
  unfold tailWord_1006072
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347230205590221131574235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24462973607453628175432313 18347230205590221131574235)
  ·
    refine ⟨27520845308385331697361353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18347230205590221131574235 27520845308385331697361353)
    ·
      refine ⟨20640633981288998773021015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27520845308385331697361353 20640633981288998773021015)
      ·
        refine ⟨30960950971933498159531523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20640633981288998773021015 30960950971933498159531523)
        ·
          refine ⟨46441426457900247239297285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30960950971933498159531523 46441426457900247239297285)
          ·
            refine ⟨8707767460856296357368241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46441426457900247239297285 8707767460856296357368241)
            ·
              refine ⟨6530825595642222268026181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707767460856296357368241 6530825595642222268026181)
              ·
                refine ⟨1224529799182916675254909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6530825595642222268026181 1224529799182916675254909)
                ·
                  refine ⟨459198674693593753220591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224529799182916675254909 459198674693593753220591)
                  ·
                    rfl

theorem cell20_1006072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1006072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006072 prefixEnd_1006072 := by exact prefixLift 1006072
  have htrace : WordTrace (prefixWord ++ tailWord_1006072) baseStart_1006072 baseEnd_1006072 := by
    simpa [prefixWord, tailWord_1006072, baseEnd_1006072] using wordTrace_append hprefix tailTrace_1006072
  have hstable : (prefixWord ++ tailWord_1006072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006072).length < 2 ^ (prefixWord ++ tailWord_1006072).sum := by decide
  have hdescent : baseEnd_1006072 < baseStart_1006072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006126 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 2]
def baseStart_1006126 : Nat := 118140960795 + 1006126 * 2 ^ 59
def prefixEnd_1006126 : Nat := 4983230072969 + 3 ^ 40 * 1006126 * 2
def baseEnd_1006126 : Nat := 459223321765009565420371

theorem tailTrace_1006126 : CollatzResearch.WordTrace tailWord_1006126 prefixEnd_1006126 459223321765009565420371 := by
  unfold tailWord_1006126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587053744123101185701779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24464286635323206323742821 4587053744123101185701779)
  ·
    refine ⟨6880580616184651778552669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4587053744123101185701779 6880580616184651778552669)
    ·
      refine ⟨2580217731069244416957251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6880580616184651778552669 2580217731069244416957251)
      ·
        refine ⟨3870326596603866625435877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2580217731069244416957251 3870326596603866625435877)
        ·
          refine ⟨725686236863224992269227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3870326596603866625435877 725686236863224992269227)
          ·
            refine ⟨1088529355294837488403841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725686236863224992269227 1088529355294837488403841)
            ·
              refine ⟨816397016471128116302881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088529355294837488403841 816397016471128116302881)
              ·
                refine ⟨612297762353346087227161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816397016471128116302881 612297762353346087227161)
                ·
                  refine ⟨459223321765009565420371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612297762353346087227161 459223321765009565420371)
                  ·
                    rfl

theorem cell20_1006126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_1006126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006126 prefixEnd_1006126 := by exact prefixLift 1006126
  have htrace : WordTrace (prefixWord ++ tailWord_1006126) baseStart_1006126 baseEnd_1006126 := by
    simpa [prefixWord, tailWord_1006126, baseEnd_1006126] using wordTrace_append hprefix tailTrace_1006126
  have hstable : (prefixWord ++ tailWord_1006126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006126).length < 2 ^ (prefixWord ++ tailWord_1006126).sum := by decide
  have hdescent : baseEnd_1006126 < baseStart_1006126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006141 : List Nat := [1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_1006141 : Nat := 118140960795 + 1006141 * 2 ^ 59
def prefixEnd_1006141 : Nat := 4983230072969 + 3 ^ 40 * 1006141 * 2
def baseEnd_1006141 : Nat := 153076722724578726640103

theorem tailTrace_1006141 : CollatzResearch.WordTrace tailWord_1006141 prefixEnd_1006141 153076722724578726640103 := by
  unfold tailWord_1006141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36696977047930467047410277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24464651365286978031606851 36696977047930467047410277)
  ·
    refine ⟨6880683196486962571389427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36696977047930467047410277 6880683196486962571389427)
    ·
      refine ⟨10321024794730443857084141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6880683196486962571389427 10321024794730443857084141)
      ·
        refine ⟨3870384298023916446406553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10321024794730443857084141 3870384298023916446406553)
        ·
          refine ⟨2902788223517937334804915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3870384298023916446406553 2902788223517937334804915)
          ·
            refine ⟨4354182335276906002207373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902788223517937334804915 4354182335276906002207373)
            ·
              refine ⟨1632818375728839750827765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4354182335276906002207373 1632818375728839750827765)
              ·
                refine ⟨153076722724578726640103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1632818375728839750827765 153076722724578726640103)
                ·
                  rfl

theorem cell20_1006141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_1006141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006141 prefixEnd_1006141 := by exact prefixLift 1006141
  have htrace : WordTrace (prefixWord ++ tailWord_1006141) baseStart_1006141 baseEnd_1006141 := by
    simpa [prefixWord, tailWord_1006141, baseEnd_1006141] using wordTrace_append hprefix tailTrace_1006141
  have hstable : (prefixWord ++ tailWord_1006141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006141).length < 2 ^ (prefixWord ++ tailWord_1006141).sum := by decide
  have hdescent : baseEnd_1006141 < baseStart_1006141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006178 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1006178 : Nat := 118140960795 + 1006178 * 2 ^ 59
def prefixEnd_1006178 : Nat := 4983230072969 + 3 ^ 40 * 1006178 * 2
def baseEnd_1006178 : Nat := 459247055981928495686825

theorem tailTrace_1006178 : CollatzResearch.WordTrace tailWord_1006178 prefixEnd_1006178 459247055981928495686825 := by
  unfold tailWord_1006178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174581637199105591626797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24465551032530948244338125 9174581637199105591626797)
  ·
    refine ⟨3440468113949664596860049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9174581637199105591626797 3440468113949664596860049)
    ·
      refine ⟨2580351085462248447645037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3440468113949664596860049 2580351085462248447645037)
      ·
        refine ⟨967631657048343167866889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2580351085462248447645037 967631657048343167866889)
        ·
          refine ⟨725723742786257375900167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967631657048343167866889 725723742786257375900167)
          ·
            refine ⟨1088585614179386063850251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725723742786257375900167 1088585614179386063850251)
            ·
              refine ⟨1632878421269079095775377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088585614179386063850251 1632878421269079095775377)
              ·
                refine ⟨1224658815951809321831533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632878421269079095775377 1224658815951809321831533)
                ·
                  refine ⟨459247055981928495686825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224658815951809321831533 459247055981928495686825)
                  ·
                    rfl

theorem cell20_1006178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1006178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006178 prefixEnd_1006178 := by exact prefixLift 1006178
  have htrace : WordTrace (prefixWord ++ tailWord_1006178) baseStart_1006178 baseEnd_1006178 := by
    simpa [prefixWord, tailWord_1006178, baseEnd_1006178] using wordTrace_append hprefix tailTrace_1006178
  have hstable : (prefixWord ++ tailWord_1006178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006178).length < 2 ^ (prefixWord ++ tailWord_1006178).sum := by decide
  have hdescent : baseEnd_1006178 < baseStart_1006178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006186 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1006186 : Nat := 118140960795 + 1006186 * 2 ^ 59
def prefixEnd_1006186 : Nat := 4983230072969 + 3 ^ 40 * 1006186 * 2
def baseEnd_1006186 : Nat := 459250707399916023420125

theorem tailTrace_1006186 : CollatzResearch.WordTrace tailWord_1006186 prefixEnd_1006186 459250707399916023420125 := by
  unfold tailWord_1006186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174654583191859933199603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24465745555178293155198941 9174654583191859933199603)
  ·
    refine ⟨13761981874787789899799405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174654583191859933199603 13761981874787789899799405)
    ·
      refine ⟨5160743203045421212424777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13761981874787789899799405 5160743203045421212424777)
      ·
        refine ⟨3870557402284065909318583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5160743203045421212424777 3870557402284065909318583)
        ·
          refine ⟨5805836103426098863977875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870557402284065909318583 5805836103426098863977875)
          ·
            refine ⟨8708754155139148295966813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805836103426098863977875 8708754155139148295966813)
            ·
              refine ⟨3265782808177180610987555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8708754155139148295966813 3265782808177180610987555)
              ·
                refine ⟨4898674212265770916481333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3265782808177180610987555 4898674212265770916481333)
                ·
                  refine ⟨459250707399916023420125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4898674212265770916481333 459250707399916023420125)
                  ·
                    rfl

theorem cell20_1006186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1006186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006186 prefixEnd_1006186 := by exact prefixLift 1006186
  have htrace : WordTrace (prefixWord ++ tailWord_1006186) baseStart_1006186 baseEnd_1006186 := by
    simpa [prefixWord, tailWord_1006186, baseEnd_1006186] using wordTrace_append hprefix tailTrace_1006186
  have hstable : (prefixWord ++ tailWord_1006186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006186).length < 2 ^ (prefixWord ++ tailWord_1006186).sum := by decide
  have hdescent : baseEnd_1006186 < baseStart_1006186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006189 : List Nat := [1, 5, 1, 1, 3, 1, 2, 4, 2]
def baseStart_1006189 : Nat := 118140960795 + 1006189 * 2 ^ 59
def prefixEnd_1006189 : Nat := 4983230072969 + 3 ^ 40 * 1006189 * 2
def baseEnd_1006189 : Nat := 459252076681661346320113

theorem tailTrace_1006189 : CollatzResearch.WordTrace tailWord_1006189 prefixEnd_1006189 459252076681661346320113 := by
  unfold tailWord_1006189
  simp only [CollatzResearch.WordTrace]
  refine ⟨36698727751756571245157621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24465818501171047496771747 36698727751756571245157621)
  ·
    refine ⟨3440505726727178554233527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36698727751756571245157621 3440505726727178554233527)
    ·
      refine ⟨5160758590090767831350291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440505726727178554233527 5160758590090767831350291)
      ·
        refine ⟨7741137885136151747025437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5160758590090767831350291 7741137885136151747025437)
        ·
          refine ⟨2902926706926056905134539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7741137885136151747025437 2902926706926056905134539)
          ·
            refine ⟨4354390060389085357701809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2902926706926056905134539 4354390060389085357701809)
            ·
              refine ⟨3265792545291814018276357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4354390060389085357701809 3265792545291814018276357)
              ·
                refine ⟨612336102242215128426817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3265792545291814018276357 612336102242215128426817)
                ·
                  refine ⟨459252076681661346320113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612336102242215128426817 459252076681661346320113)
                  ·
                    rfl

theorem cell20_1006189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_1006189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006189 prefixEnd_1006189 := by exact prefixLift 1006189
  have htrace : WordTrace (prefixWord ++ tailWord_1006189) baseStart_1006189 baseEnd_1006189 := by
    simpa [prefixWord, tailWord_1006189, baseEnd_1006189] using wordTrace_append hprefix tailTrace_1006189
  have hstable : (prefixWord ++ tailWord_1006189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006189).length < 2 ^ (prefixWord ++ tailWord_1006189).sum := by decide
  have hdescent : baseEnd_1006189 < baseStart_1006189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006234 : List Nat := [3, 1, 1, 6, 1, 2, 6]
def baseStart_1006234 : Nat := 118140960795 + 1006234 * 2 ^ 59
def prefixEnd_1006234 : Nat := 4983230072969 + 3 ^ 40 * 1006234 * 2
def baseEnd_1006234 : Nat := 51030290656426798868881

theorem tailTrace_1006234 : CollatzResearch.WordTrace tailWord_1006234 prefixEnd_1006234 51030290656426798868881 := by
  unfold tailWord_1006234
  simp only [CollatzResearch.WordTrace]
  refine ⟨9175092259148385982636439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24466912691062362620363837 9175092259148385982636439)
  ·
    refine ⟨13762638388722578973954659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9175092259148385982636439 13762638388722578973954659)
    ·
      refine ⟨20643957583083868460931989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762638388722578973954659 20643957583083868460931989)
      ·
        refine ⟨967685511707056334106187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20643957583083868460931989 967685511707056334106187)
        ·
          refine ⟨1451528267560584501159281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967685511707056334106187 1451528267560584501159281)
          ·
            refine ⟨1088646200670438375869461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451528267560584501159281 1088646200670438375869461)
            ·
              refine ⟨51030290656426798868881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1088646200670438375869461 51030290656426798868881)
              ·
                rfl

theorem cell20_1006234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_1006234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006234 prefixEnd_1006234 := by exact prefixLift 1006234
  have htrace : WordTrace (prefixWord ++ tailWord_1006234) baseStart_1006234 baseEnd_1006234 := by
    simpa [prefixWord, tailWord_1006234, baseEnd_1006234] using wordTrace_append hprefix tailTrace_1006234
  have hstable : (prefixWord ++ tailWord_1006234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006234).length < 2 ^ (prefixWord ++ tailWord_1006234).sum := by decide
  have hdescent : baseEnd_1006234 < baseStart_1006234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006293 : List Nat := [1, 3, 2, 5, 1, 8]
def baseStart_1006293 : Nat := 118140960795 + 1006293 * 2 ^ 59
def prefixEnd_1006293 : Nat := 4983230072969 + 3 ^ 40 * 1006293 * 2
def baseEnd_1006293 : Nat := 17011094263537007661223

theorem tailTrace_1006293 : CollatzResearch.WordTrace tailWord_1006293 prefixEnd_1006293 17011094263537007661223 := by
  unfold tailWord_1006293
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702520943379797006943533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24468347295586531337962355 36702520943379797006943533)
  ·
    refine ⟨13763445353767423877603825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36702520943379797006943533 13763445353767423877603825)
    ·
      refine ⟨10322584015325567908202869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13763445353767423877603825 10322584015325567908202869)
      ·
        refine ⟨967742251436771991394019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10322584015325567908202869 967742251436771991394019)
        ·
          refine ⟨1451613377155157987091029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967742251436771991394019 1451613377155157987091029)
          ·
            refine ⟨17011094263537007661223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1451613377155157987091029 17011094263537007661223)
            ·
              rfl

theorem cell20_1006293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 8].length) (baseStart_1006293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006293 prefixEnd_1006293 := by exact prefixLift 1006293
  have htrace : WordTrace (prefixWord ++ tailWord_1006293) baseStart_1006293 baseEnd_1006293 := by
    simpa [prefixWord, tailWord_1006293, baseEnd_1006293] using wordTrace_append hprefix tailTrace_1006293
  have hstable : (prefixWord ++ tailWord_1006293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006293).length < 2 ^ (prefixWord ++ tailWord_1006293).sum := by decide
  have hdescent : baseEnd_1006293 < baseStart_1006293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006303 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 2]
def baseStart_1006303 : Nat := 118140960795 + 1006303 * 2 ^ 59
def prefixEnd_1006303 : Nat := 4983230072969 + 3 ^ 40 * 1006303 * 2
def baseEnd_1006303 : Nat := 459304109387983616519647

theorem tailTrace_1006303 : CollatzResearch.WordTrace tailWord_1006303 prefixEnd_1006303 459304109387983616519647 := by
  unfold tailWord_1006303
  simp only [CollatzResearch.WordTrace]
  refine ⟨36702885673343568714807563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24468590448895712476538375 36702885673343568714807563)
  ·
    refine ⟨55054328510015353072211345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36702885673343568714807563 55054328510015353072211345)
    ·
      refine ⟨41290746382511514804158509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55054328510015353072211345 41290746382511514804158509)
      ·
        refine ⟨15484029893441818051559441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41290746382511514804158509 15484029893441818051559441)
        ·
          refine ⟨11613022420081363538669581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15484029893441818051559441 11613022420081363538669581)
          ·
            refine ⟨4354883407530511327001093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11613022420081363538669581 4354883407530511327001093)
            ·
              refine ⟨816540638911970873812705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4354883407530511327001093 816540638911970873812705)
              ·
                refine ⟨612405479183978155359529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816540638911970873812705 612405479183978155359529)
                ·
                  refine ⟨459304109387983616519647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612405479183978155359529 459304109387983616519647)
                  ·
                    rfl

theorem cell20_1006303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 2].length) (baseStart_1006303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006303 prefixEnd_1006303 := by exact prefixLift 1006303
  have htrace : WordTrace (prefixWord ++ tailWord_1006303) baseStart_1006303 baseEnd_1006303 := by
    simpa [prefixWord, tailWord_1006303, baseEnd_1006303] using wordTrace_append hprefix tailTrace_1006303
  have hstable : (prefixWord ++ tailWord_1006303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006303).length < 2 ^ (prefixWord ++ tailWord_1006303).sum := by decide
  have hdescent : baseEnd_1006303 < baseStart_1006303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006362 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 2]
def baseStart_1006362 : Nat := 118140960795 + 1006362 * 2 ^ 59
def prefixEnd_1006362 : Nat := 4983230072969 + 3 ^ 40 * 1006362 * 2
def baseEnd_1006362 : Nat := 459331038595641633552739

theorem tailTrace_1006362 : CollatzResearch.WordTrace tailWord_1006362 prefixEnd_1006362 459331038595641633552739 := by
  unfold tailWord_1006362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176259395032455447801335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24470025053419881194136893 9176259395032455447801335)
  ·
    refine ⟨13764389092548683171702003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176259395032455447801335 13764389092548683171702003)
    ·
      refine ⟨20646583638823024757553005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13764389092548683171702003 20646583638823024757553005)
      ·
        refine ⟨7742468864558634284082377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20646583638823024757553005 7742468864558634284082377)
        ·
          refine ⟨5806851648418975713061783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7742468864558634284082377 5806851648418975713061783)
          ·
            refine ⟨8710277472628463569592675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5806851648418975713061783 8710277472628463569592675)
            ·
              refine ⟨13065416208942695354389013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8710277472628463569592675 13065416208942695354389013)
              ·
                refine ⟨612441384794188844736985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13065416208942695354389013 612441384794188844736985)
                ·
                  refine ⟨459331038595641633552739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612441384794188844736985 459331038595641633552739)
                  ·
                    rfl

theorem cell20_1006362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_1006362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006362 prefixEnd_1006362 := by exact prefixLift 1006362
  have htrace : WordTrace (prefixWord ++ tailWord_1006362) baseStart_1006362 baseEnd_1006362 := by
    simpa [prefixWord, tailWord_1006362, baseEnd_1006362] using wordTrace_append hprefix tailTrace_1006362
  have hstable : (prefixWord ++ tailWord_1006362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006362).length < 2 ^ (prefixWord ++ tailWord_1006362).sum := by decide
  have hdescent : baseEnd_1006362 < baseStart_1006362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006372 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1006372 : Nat := 118140960795 + 1006372 * 2 ^ 59
def prefixEnd_1006372 : Nat := 4983230072969 + 3 ^ 40 * 1006372 * 2
def baseEnd_1006372 : Nat := 459335602868126043219365

theorem tailTrace_1006372 : CollatzResearch.WordTrace tailWord_1006372 prefixEnd_1006372 459335602868126043219365 := by
  unfold tailWord_1006372
  simp only [CollatzResearch.WordTrace]
  refine ⟨18352701155046796749534685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24470268206729062332712913 18352701155046796749534685)
  ·
    refine ⟨6882262933142548781075507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18352701155046796749534685 6882262933142548781075507)
    ·
      refine ⟨10323394399713823171613261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6882262933142548781075507 10323394399713823171613261)
      ·
        refine ⟨3871272899892683689354973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10323394399713823171613261 3871272899892683689354973)
        ·
          refine ⟨1451727337459756383508115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3871272899892683689354973 1451727337459756383508115)
          ·
            refine ⟨2177591006189634575262173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451727337459756383508115 2177591006189634575262173)
            ·
              refine ⟨816596627321112965723315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2177591006189634575262173 816596627321112965723315)
              ·
                refine ⟨1224894940981669448584973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816596627321112965723315 1224894940981669448584973)
                ·
                  refine ⟨459335602868126043219365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224894940981669448584973 459335602868126043219365)
                  ·
                    rfl

theorem cell20_1006372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1006372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006372 prefixEnd_1006372 := by exact prefixLift 1006372
  have htrace : WordTrace (prefixWord ++ tailWord_1006372) baseStart_1006372 baseEnd_1006372 := by
    simpa [prefixWord, tailWord_1006372, baseEnd_1006372] using wordTrace_append hprefix tailTrace_1006372
  have hstable : (prefixWord ++ tailWord_1006372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006372).length < 2 ^ (prefixWord ++ tailWord_1006372).sum := by decide
  have hdescent : baseEnd_1006372 < baseStart_1006372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006413 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 2]
def baseStart_1006413 : Nat := 118140960795 + 1006413 * 2 ^ 59
def prefixEnd_1006413 : Nat := 4983230072969 + 3 ^ 40 * 1006413 * 2
def baseEnd_1006413 : Nat := 459354316385312122852531

theorem tailTrace_1006413 : CollatzResearch.WordTrace tailWord_1006413 prefixEnd_1006413 459354316385312122852531 := by
  unfold tailWord_1006413
  simp only [CollatzResearch.WordTrace]
  refine ⟨36706897702945057501311893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24471265135296705000874595 36706897702945057501311893)
  ·
    refine ⟨1720635829825549570373995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36706897702945057501311893 1720635829825549570373995)
    ·
      refine ⟨2580953744738324355560993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1720635829825549570373995 2580953744738324355560993)
      ·
        refine ⟨1935715308553743266670745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2580953744738324355560993 1935715308553743266670745)
        ·
          refine ⟨1451786481415307450003059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1935715308553743266670745 1451786481415307450003059)
          ·
            refine ⟨2177679722122961175004589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451786481415307450003059 2177679722122961175004589)
            ·
              refine ⟨816629895796110440626721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2177679722122961175004589 816629895796110440626721)
              ·
                refine ⟨612472421847082830470041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816629895796110440626721 612472421847082830470041)
                ·
                  refine ⟨459354316385312122852531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612472421847082830470041 459354316385312122852531)
                  ·
                    rfl

theorem cell20_1006413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_1006413 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006413 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006413 prefixEnd_1006413 := by exact prefixLift 1006413
  have htrace : WordTrace (prefixWord ++ tailWord_1006413) baseStart_1006413 baseEnd_1006413 := by
    simpa [prefixWord, tailWord_1006413, baseEnd_1006413] using wordTrace_append hprefix tailTrace_1006413
  have hstable : (prefixWord ++ tailWord_1006413).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006413).length < 2 ^ (prefixWord ++ tailWord_1006413).sum := by decide
  have hdescent : baseEnd_1006413 < baseStart_1006413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006417 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 4]
def baseStart_1006417 : Nat := 118140960795 + 1006417 * 2 ^ 59
def prefixEnd_1006417 : Nat := 4983230072969 + 3 ^ 40 * 1006417 * 2
def baseEnd_1006417 : Nat := 459356142094305886719181

theorem tailTrace_1006417 : CollatzResearch.WordTrace tailWord_1006417 prefixEnd_1006417 459356142094305886719181 := by
  unfold tailWord_1006417
  simp only [CollatzResearch.WordTrace]
  refine ⟨36707043594930566184457505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24471362396620377456305003 36707043594930566184457505)
  ·
    refine ⟨27530282696197924638343129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36707043594930566184457505 27530282696197924638343129)
    ·
      refine ⟨20647712022148443478757347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27530282696197924638343129 20647712022148443478757347)
      ·
        refine ⟨30971568033222665218136021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20647712022148443478757347 30971568033222665218136021)
        ·
          refine ⟨725896125778656216050063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30971568033222665218136021 725896125778656216050063)
          ·
            refine ⟨1088844188667984324075095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725896125778656216050063 1088844188667984324075095)
            ·
              refine ⟨1633266283001976486112643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088844188667984324075095 1633266283001976486112643)
              ·
                refine ⟨2449899424502964729168965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633266283001976486112643 2449899424502964729168965)
                ·
                  refine ⟨459356142094305886719181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2449899424502964729168965 459356142094305886719181)
                  ·
                    rfl

theorem cell20_1006417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 4].length) (baseStart_1006417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006417 prefixEnd_1006417 := by exact prefixLift 1006417
  have htrace : WordTrace (prefixWord ++ tailWord_1006417) baseStart_1006417 baseEnd_1006417 := by
    simpa [prefixWord, tailWord_1006417, baseEnd_1006417] using wordTrace_append hprefix tailTrace_1006417
  have hstable : (prefixWord ++ tailWord_1006417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006417).length < 2 ^ (prefixWord ++ tailWord_1006417).sum := by decide
  have hdescent : baseEnd_1006417 < baseStart_1006417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006462 : List Nat := [4, 2, 3, 1, 3, 7]
def baseStart_1006462 : Nat := 118140960795 + 1006462 * 2 ^ 59
def prefixEnd_1006462 : Nat := 4983230072969 + 3 ^ 40 * 1006462 * 2
def baseEnd_1006462 : Nat := 17013951160017990008111

theorem tailTrace_1006462 : CollatzResearch.WordTrace tailWord_1006462 prefixEnd_1006462 17013951160017990008111 := by
  unfold tailWord_1006462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4588585609970942358730705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24472456586511692579897093 4588585609970942358730705)
  ·
    refine ⟨3441439207478206769048029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4588585609970942358730705 3441439207478206769048029)
    ·
      refine ⟨1290539702804327538393011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3441439207478206769048029 1290539702804327538393011)
      ·
        refine ⟨1935809554206491307589517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290539702804327538393011 1935809554206491307589517)
        ·
          refine ⟨725928582827434240346069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1935809554206491307589517 725928582827434240346069)
          ·
            refine ⟨17013951160017990008111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 725928582827434240346069 17013951160017990008111)
            ·
              rfl

theorem cell20_1006462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 7].length) (baseStart_1006462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006462 prefixEnd_1006462 := by exact prefixLift 1006462
  have htrace : WordTrace (prefixWord ++ tailWord_1006462) baseStart_1006462 baseEnd_1006462 := by
    simpa [prefixWord, tailWord_1006462, baseEnd_1006462] using wordTrace_append hprefix tailTrace_1006462
  have hstable : (prefixWord ++ tailWord_1006462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006462).length < 2 ^ (prefixWord ++ tailWord_1006462).sum := by decide
  have hdescent : baseEnd_1006462 < baseStart_1006462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006472 : List Nat := [2, 1, 3, 3, 2, 3, 2, 2, 2]
def baseStart_1006472 : Nat := 118140960795 + 1006472 * 2 ^ 59
def prefixEnd_1006472 : Nat := 4983230072969 + 3 ^ 40 * 1006472 * 2
def baseEnd_1006472 : Nat := 459381245592970139885623

theorem tailTrace_1006472 : CollatzResearch.WordTrace tailWord_1006472 prefixEnd_1006472 459381245592970139885623 := by
  unfold tailWord_1006472
  simp only [CollatzResearch.WordTrace]
  refine ⟨18354524804865655288854835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24472699739820873718473113 18354524804865655288854835)
  ·
    refine ⟨27531787207298482933282253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18354524804865655288854835 27531787207298482933282253)
    ·
      refine ⟨10324420202736931099980845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27531787207298482933282253 10324420202736931099980845)
      ·
        refine ⟨3871657576026349162492817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10324420202736931099980845 3871657576026349162492817)
        ·
          refine ⟨2903743182019761871869613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3871657576026349162492817 2903743182019761871869613)
          ·
            refine ⟨1088903693257410701951105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2903743182019761871869613 1088903693257410701951105)
            ·
              refine ⟨816677769943058026463329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088903693257410701951105 816677769943058026463329)
              ·
                refine ⟨612508327457293519847497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816677769943058026463329 612508327457293519847497)
                ·
                  refine ⟨459381245592970139885623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612508327457293519847497 459381245592970139885623)
                  ·
                    rfl

theorem cell20_1006472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 2, 2].length) (baseStart_1006472 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006472 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006472 prefixEnd_1006472 := by exact prefixLift 1006472
  have htrace : WordTrace (prefixWord ++ tailWord_1006472) baseStart_1006472 baseEnd_1006472 := by
    simpa [prefixWord, tailWord_1006472, baseEnd_1006472] using wordTrace_append hprefix tailTrace_1006472
  have hstable : (prefixWord ++ tailWord_1006472).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006472).length < 2 ^ (prefixWord ++ tailWord_1006472).sum := by decide
  have hdescent : baseEnd_1006472 < baseStart_1006472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006497 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 6]
def baseStart_1006497 : Nat := 118140960795 + 1006497 * 2 ^ 59
def prefixEnd_1006497 : Nat := 4983230072969 + 3 ^ 40 * 1006497 * 2
def baseEnd_1006497 : Nat := 459392656274181164052187

theorem tailTrace_1006497 : CollatzResearch.WordTrace tailWord_1006497 prefixEnd_1006497 459392656274181164052187 := by
  unfold tailWord_1006497
  simp only [CollatzResearch.WordTrace]
  refine ⟨36709961434640739847369745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24473307623093826564913163 36709961434640739847369745)
  ·
    refine ⟨27532471075980554885527309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36709961434640739847369745 27532471075980554885527309)
    ·
      refine ⟨10324676653492708082072741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27532471075980554885527309 10324676653492708082072741)
      ·
        refine ⟨1935876872529882765388639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10324676653492708082072741 1935876872529882765388639)
        ·
          refine ⟨2903815308794824148082959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935876872529882765388639 2903815308794824148082959)
          ·
            refine ⟨4355722963192236222124439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2903815308794824148082959 4355722963192236222124439)
            ·
              refine ⟨6533584444788354333186659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4355722963192236222124439 6533584444788354333186659)
              ·
                refine ⟨9800376667182531499779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6533584444788354333186659 9800376667182531499779989)
                ·
                  refine ⟨459392656274181164052187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9800376667182531499779989 459392656274181164052187)
                  ·
                    rfl

theorem cell20_1006497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 6].length) (baseStart_1006497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006497 prefixEnd_1006497 := by exact prefixLift 1006497
  have htrace : WordTrace (prefixWord ++ tailWord_1006497) baseStart_1006497 baseEnd_1006497 := by
    simpa [prefixWord, tailWord_1006497, baseEnd_1006497] using wordTrace_append hprefix tailTrace_1006497
  have hstable : (prefixWord ++ tailWord_1006497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006497).length < 2 ^ (prefixWord ++ tailWord_1006497).sum := by decide
  have hdescent : baseEnd_1006497 < baseStart_1006497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006528 : List Nat := [2, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1006528 : Nat := 118140960795 + 1006528 * 2 ^ 59
def prefixEnd_1006528 : Nat := 4983230072969 + 3 ^ 40 * 1006528 * 2
def baseEnd_1006528 : Nat := 459406805518882834018727

theorem tailTrace_1006528 : CollatzResearch.WordTrace tailWord_1006528 prefixEnd_1006528 459406805518882834018727 := by
  unfold tailWord_1006528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18355546048764216070874119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24474061398352288094498825 18355546048764216070874119)
  ·
    refine ⟨27533319073146324106311179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18355546048764216070874119 27533319073146324106311179)
    ·
      refine ⟨41299978609719486159466769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27533319073146324106311179 41299978609719486159466769)
      ·
        refine ⟨30974983957289614619600077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41299978609719486159466769 30974983957289614619600077)
        ·
          refine ⟨11615618983983605482350029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30974983957289614619600077 11615618983983605482350029)
          ·
            refine ⟨4355857118993852055881261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11615618983983605482350029 4355857118993852055881261)
            ·
              refine ⟨1633446419622694520955473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4355857118993852055881261 1633446419622694520955473)
              ·
                refine ⟨1225084814717020890716605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633446419622694520955473 1225084814717020890716605)
                ·
                  refine ⟨459406805518882834018727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225084814717020890716605 459406805518882834018727)
                  ·
                    rfl

theorem cell20_1006528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1006528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006528 prefixEnd_1006528 := by exact prefixLift 1006528
  have htrace : WordTrace (prefixWord ++ tailWord_1006528) baseStart_1006528 baseEnd_1006528 := by
    simpa [prefixWord, tailWord_1006528, baseEnd_1006528] using wordTrace_append hprefix tailTrace_1006528
  have hstable : (prefixWord ++ tailWord_1006528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006528).length < 2 ^ (prefixWord ++ tailWord_1006528).sum := by decide
  have hdescent : baseEnd_1006528 < baseStart_1006528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006565 : List Nat := [1, 3, 1, 6, 2, 1, 1, 3, 2]
def baseStart_1006565 : Nat := 118140960795 + 1006565 * 2 ^ 59
def prefixEnd_1006565 : Nat := 4983230072969 + 3 ^ 40 * 1006565 * 2
def baseEnd_1006565 : Nat := 459423693327075149785243

theorem tailTrace_1006565 : CollatzResearch.WordTrace tailWord_1006565 prefixEnd_1006565 459423693327075149785243 := by
  unfold tailWord_1006565
  simp only [CollatzResearch.WordTrace]
  refine ⟨36712441598394387460845149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24474961065596258307230099 36712441598394387460845149)
  ·
    refine ⟨13767165599397895297816931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36712441598394387460845149 13767165599397895297816931)
    ·
      refine ⟨20650748399096842946725397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13767165599397895297816931 20650748399096842946725397)
      ·
        refine ⟨968003831207664513127753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20650748399096842946725397 968003831207664513127753)
        ·
          refine ⟨726002873405748384845815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968003831207664513127753 726002873405748384845815)
          ·
            refine ⟨1089004310108622577268723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726002873405748384845815 1089004310108622577268723)
            ·
              refine ⟨1633506465162933865903085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089004310108622577268723 1633506465162933865903085)
              ·
                refine ⟨612564924436100199713657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1633506465162933865903085 612564924436100199713657)
                ·
                  refine ⟨459423693327075149785243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612564924436100199713657 459423693327075149785243)
                  ·
                    rfl

theorem cell20_1006565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 3, 2].length) (baseStart_1006565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006565 prefixEnd_1006565 := by exact prefixLift 1006565
  have htrace : WordTrace (prefixWord ++ tailWord_1006565) baseStart_1006565 baseEnd_1006565 := by
    simpa [prefixWord, tailWord_1006565, baseEnd_1006565] using wordTrace_append hprefix tailTrace_1006565
  have hstable : (prefixWord ++ tailWord_1006565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006565).length < 2 ^ (prefixWord ++ tailWord_1006565).sum := by decide
  have hdescent : baseEnd_1006565 < baseStart_1006565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006587 : List Nat := [1, 1, 1, 1, 1, 3, 3, 6, 3]
def baseStart_1006587 : Nat := 118140960795 + 1006587 * 2 ^ 59
def prefixEnd_1006587 : Nat := 4983230072969 + 3 ^ 40 * 1006587 * 2
def baseEnd_1006587 : Nat := 459433734726540851051819

theorem tailTrace_1006587 : CollatzResearch.WordTrace tailWord_1006587 prefixEnd_1006587 459433734726540851051819 := by
  unfold tailWord_1006587
  simp only [CollatzResearch.WordTrace]
  refine ⟨36713244004314685218146015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24475496002876456812097343 36713244004314685218146015)
  ·
    refine ⟨55069866006472027827219023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36713244004314685218146015 55069866006472027827219023)
    ·
      refine ⟨82604799009708041740828535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55069866006472027827219023 82604799009708041740828535)
      ·
        refine ⟨123907198514562062611242803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82604799009708041740828535 123907198514562062611242803)
        ·
          refine ⟨185860797771843093916864205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123907198514562062611242803 185860797771843093916864205)
          ·
            refine ⟨69697799164441160218824077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185860797771843093916864205 69697799164441160218824077)
            ·
              refine ⟨26136674686665435082059029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69697799164441160218824077 26136674686665435082059029)
              ·
                refine ⟨1225156625937442269471517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26136674686665435082059029 1225156625937442269471517)
                ·
                  refine ⟨459433734726540851051819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225156625937442269471517 459433734726540851051819)
                  ·
                    rfl

theorem cell20_1006587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 6, 3].length) (baseStart_1006587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006587 prefixEnd_1006587 := by exact prefixLift 1006587
  have htrace : WordTrace (prefixWord ++ tailWord_1006587) baseStart_1006587 baseEnd_1006587 := by
    simpa [prefixWord, tailWord_1006587, baseEnd_1006587] using wordTrace_append hprefix tailTrace_1006587
  have hstable : (prefixWord ++ tailWord_1006587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006587).length < 2 ^ (prefixWord ++ tailWord_1006587).sum := by decide
  have hdescent : baseEnd_1006587 < baseStart_1006587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006604 : List Nat := [2, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_1006604 : Nat := 118140960795 + 1006604 * 2 ^ 59
def prefixEnd_1006604 : Nat := 4983230072969 + 3 ^ 40 * 1006604 * 2
def baseEnd_1006604 : Nat := 459441493989764347485083

theorem tailTrace_1006604 : CollatzResearch.WordTrace tailWord_1006604 prefixEnd_1006604 459441493989764347485083 := by
  unfold tailWord_1006604
  simp only [CollatzResearch.WordTrace]
  refine ⟨18356932022626548560757433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24475909363502064747676577 18356932022626548560757433)
  ·
    refine ⟨13767699016969911420568075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18356932022626548560757433 13767699016969911420568075)
    ·
      refine ⟨20651548525454867130852113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13767699016969911420568075 20651548525454867130852113)
      ·
        refine ⟨15488661394091150348139085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20651548525454867130852113 15488661394091150348139085)
        ·
          refine ⟨5808248022784181380552157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15488661394091150348139085 5808248022784181380552157)
          ·
            refine ⟨2178093008544068017707059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5808248022784181380552157 2178093008544068017707059)
            ·
              refine ⟨3267139512816102026560589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178093008544068017707059 3267139512816102026560589)
              ·
                refine ⟨1225177317306038259960221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267139512816102026560589 1225177317306038259960221)
                ·
                  refine ⟨459441493989764347485083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225177317306038259960221 459441493989764347485083)
                  ·
                    rfl

theorem cell20_1006604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_1006604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006604 prefixEnd_1006604 := by exact prefixLift 1006604
  have htrace : WordTrace (prefixWord ++ tailWord_1006604) baseStart_1006604 baseEnd_1006604 := by
    simpa [prefixWord, tailWord_1006604, baseEnd_1006604] using wordTrace_append hprefix tailTrace_1006604
  have hstable : (prefixWord ++ tailWord_1006604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006604).length < 2 ^ (prefixWord ++ tailWord_1006604).sum := by decide
  have hdescent : baseEnd_1006604 < baseStart_1006604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006642 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1006642 : Nat := 118140960795 + 1006642 * 2 ^ 59
def prefixEnd_1006642 : Nat := 4983230072969 + 3 ^ 40 * 1006642 * 2
def baseEnd_1006642 : Nat := 459458838225205104218261

theorem tailTrace_1006642 : CollatzResearch.WordTrace tailWord_1006642 prefixEnd_1006642 459458838225205104218261 := by
  unfold tailWord_1006642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178812504778857402849545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24476833346076953074265453 9178812504778857402849545)
  ·
    refine ⟨6884109378584143052137159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9178812504778857402849545 6884109378584143052137159)
    ·
      refine ⟨10326164067876214578205739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884109378584143052137159 10326164067876214578205739)
      ·
        refine ⟨15489246101814321867308609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10326164067876214578205739 15489246101814321867308609)
        ·
          refine ⟨11616934576360741400481457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15489246101814321867308609 11616934576360741400481457)
          ·
            refine ⟨8712700932270556050361093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11616934576360741400481457 8712700932270556050361093)
            ·
              refine ⟨1633631424800729259442705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8712700932270556050361093 1633631424800729259442705)
              ·
                refine ⟨1225223568600546944582029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633631424800729259442705 1225223568600546944582029)
                ·
                  refine ⟨459458838225205104218261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225223568600546944582029 459458838225205104218261)
                  ·
                    rfl

theorem cell20_1006642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1006642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006642 prefixEnd_1006642 := by exact prefixLift 1006642
  have htrace : WordTrace (prefixWord ++ tailWord_1006642) baseStart_1006642 baseEnd_1006642 := by
    simpa [prefixWord, tailWord_1006642, baseEnd_1006642] using wordTrace_append hprefix tailTrace_1006642
  have hstable : (prefixWord ++ tailWord_1006642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006642).length < 2 ^ (prefixWord ++ tailWord_1006642).sum := by decide
  have hdescent : baseEnd_1006642 < baseStart_1006642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006728 : List Nat := [2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_1006728 : Nat := 118140960795 + 1006728 * 2 ^ 59
def prefixEnd_1006728 : Nat := 4983230072969 + 3 ^ 40 * 1006728 * 2
def baseEnd_1006728 : Nat := 153166030322857009117081

theorem tailTrace_1006728 : CollatzResearch.WordTrace tailWord_1006728 prefixEnd_1006728 153166030322857009117081 := by
  unfold tailWord_1006728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18359193348401933149514419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24478924464535910866019225 18359193348401933149514419)
  ·
    refine ⟨27538790022602899724271629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18359193348401933149514419 27538790022602899724271629)
    ·
      refine ⟨10327046258476087396601861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27538790022602899724271629 10327046258476087396601861)
      ·
        refine ⟨1936321173464266386862849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10327046258476087396601861 1936321173464266386862849)
        ·
          refine ⟨1452240880098199790147137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936321173464266386862849 1452240880098199790147137)
          ·
            refine ⟨1089180660073649842610353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452240880098199790147137 1089180660073649842610353)
            ·
              refine ⟨816885495055237381957765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089180660073649842610353 816885495055237381957765)
              ·
                refine ⟨153166030322857009117081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 816885495055237381957765 153166030322857009117081)
                ·
                  rfl

theorem cell20_1006728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_1006728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006728 prefixEnd_1006728 := by exact prefixLift 1006728
  have htrace : WordTrace (prefixWord ++ tailWord_1006728) baseStart_1006728 baseEnd_1006728 := by
    simpa [prefixWord, tailWord_1006728, baseEnd_1006728] using wordTrace_append hprefix tailTrace_1006728
  have hstable : (prefixWord ++ tailWord_1006728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006728).length < 2 ^ (prefixWord ++ tailWord_1006728).sum := by decide
  have hdescent : baseEnd_1006728 < baseStart_1006728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006770 : List Nat := [3, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1006770 : Nat := 118140960795 + 1006770 * 2 ^ 59
def prefixEnd_1006770 : Nat := 4983230072969 + 3 ^ 40 * 1006770 * 2
def baseEnd_1006770 : Nat := 153172420304335182650357

theorem tailTrace_1006770 : CollatzResearch.WordTrace tailWord_1006770 prefixEnd_1006770 153172420304335182650357 := by
  unfold tailWord_1006770
  simp only [CollatzResearch.WordTrace]
  refine ⟨9179979640662926868014441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24479945708434471648038509 9179979640662926868014441)
  ·
    refine ⟨6884984730497195151010831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9179979640662926868014441 6884984730497195151010831)
    ·
      refine ⟨10327477095745792726516247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884984730497195151010831 10327477095745792726516247)
      ·
        refine ⟨15491215643618689089774371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327477095745792726516247 15491215643618689089774371)
        ·
          refine ⟨23236823465428033634661557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15491215643618689089774371 23236823465428033634661557)
          ·
            refine ⟨2178452199883878153249521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23236823465428033634661557 2178452199883878153249521)
            ·
              refine ⟨1633839149912908614937141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178452199883878153249521 1633839149912908614937141)
              ·
                refine ⟨153172420304335182650357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1633839149912908614937141 153172420304335182650357)
                ·
                  rfl

theorem cell20_1006770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1006770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006770 prefixEnd_1006770 := by exact prefixLift 1006770
  have htrace : WordTrace (prefixWord ++ tailWord_1006770) baseStart_1006770 baseEnd_1006770 := by
    simpa [prefixWord, tailWord_1006770, baseEnd_1006770] using wordTrace_append hprefix tailTrace_1006770
  have hstable : (prefixWord ++ tailWord_1006770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006770).length < 2 ^ (prefixWord ++ tailWord_1006770).sum := by decide
  have hdescent : baseEnd_1006770 < baseStart_1006770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006801 : List Nat := [1, 2, 2, 1, 2, 2, 1, 7, 2]
def baseStart_1006801 : Nat := 118140960795 + 1006801 * 2 ^ 59
def prefixEnd_1006801 : Nat := 4983230072969 + 3 ^ 40 * 1006801 * 2
def baseEnd_1006801 : Nat := 459531410157707217917611

theorem tailTrace_1006801 : CollatzResearch.WordTrace tailWord_1006801 prefixEnd_1006801 459531410157707217917611 := by
  unfold tailWord_1006801
  simp only [CollatzResearch.WordTrace]
  refine ⟨36721049225539399766436257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24480699483692933177624171 36721049225539399766436257)
  ·
    refine ⟨27540786919154549824827193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36721049225539399766436257 27540786919154549824827193)
    ·
      refine ⟨20655590189365912368620395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27540786919154549824827193 20655590189365912368620395)
      ·
        refine ⟨30983385284048868552930593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20655590189365912368620395 30983385284048868552930593)
        ·
          refine ⟨23237538963036651414697945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30983385284048868552930593 23237538963036651414697945)
          ·
            refine ⟨17428154222277488561023459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23237538963036651414697945 17428154222277488561023459)
            ·
              refine ⟨26142231333416232841535189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17428154222277488561023459 26142231333416232841535189)
              ·
                refine ⟨612708546876942957223481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26142231333416232841535189 612708546876942957223481)
                ·
                  refine ⟨459531410157707217917611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612708546876942957223481 459531410157707217917611)
                  ·
                    rfl

theorem cell20_1006801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_1006801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006801 prefixEnd_1006801 := by exact prefixLift 1006801
  have htrace : WordTrace (prefixWord ++ tailWord_1006801) baseStart_1006801 baseEnd_1006801 := by
    simpa [prefixWord, tailWord_1006801, baseEnd_1006801] using wordTrace_append hprefix tailTrace_1006801
  have hstable : (prefixWord ++ tailWord_1006801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006801).length < 2 ^ (prefixWord ++ tailWord_1006801).sum := by decide
  have hdescent : baseEnd_1006801 < baseStart_1006801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006808 : List Nat := [2, 1, 2, 2, 6, 7]
def baseStart_1006808 : Nat := 118140960795 + 1006808 * 2 ^ 59
def prefixEnd_1006808 : Nat := 4983230072969 + 3 ^ 40 * 1006808 * 2
def baseEnd_1006808 : Nat := 17019800190683196469787

theorem tailTrace_1006808 : CollatzResearch.WordTrace tailWord_1006808 prefixEnd_1006808 17019800190683196469787 := by
  unfold tailWord_1006808
  simp only [CollatzResearch.WordTrace]
  refine ⟨18360652268257019980970539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24480869691009359974627385 18360652268257019980970539)
  ·
    refine ⟨27540978402385529971455809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18360652268257019980970539 27540978402385529971455809)
    ·
      refine ⟨20655733801789147478591857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27540978402385529971455809 20655733801789147478591857)
      ·
        refine ⟨15491800351341860608943893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20655733801789147478591857 15491800351341860608943893)
        ·
          refine ⟨726178141469149716044245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15491800351341860608943893 726178141469149716044245)
          ·
            refine ⟨17019800190683196469787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 726178141469149716044245 17019800190683196469787)
            ·
              rfl

theorem cell20_1006808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 7].length) (baseStart_1006808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006808 prefixEnd_1006808 := by exact prefixLift 1006808
  have htrace : WordTrace (prefixWord ++ tailWord_1006808) baseStart_1006808 baseEnd_1006808 := by
    simpa [prefixWord, tailWord_1006808, baseEnd_1006808] using wordTrace_append hprefix tailTrace_1006808
  have hstable : (prefixWord ++ tailWord_1006808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006808).length < 2 ^ (prefixWord ++ tailWord_1006808).sum := by decide
  have hdescent : baseEnd_1006808 < baseStart_1006808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006815 : List Nat := [1, 1, 2, 3, 2, 1, 3, 4, 3]
def baseStart_1006815 : Nat := 118140960795 + 1006815 * 2 ^ 59
def prefixEnd_1006815 : Nat := 4983230072969 + 3 ^ 40 * 1006815 * 2
def baseEnd_1006815 : Nat := 459537800139185391450887

theorem tailTrace_1006815 : CollatzResearch.WordTrace tailWord_1006815 prefixEnd_1006815 459537800139185391450887 := by
  unfold tailWord_1006815
  simp only [CollatzResearch.WordTrace]
  refine ⟨36721559847488680157445899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24481039898325786771630599 36721559847488680157445899)
  ·
    refine ⟨55082339771233020236168849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36721559847488680157445899 55082339771233020236168849)
    ·
      refine ⟨41311754828424765177126637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55082339771233020236168849 41311754828424765177126637)
      ·
        refine ⟨15491908060659286941422489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41311754828424765177126637 15491908060659286941422489)
        ·
          refine ⟨11618931045494465206066867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15491908060659286941422489 11618931045494465206066867)
          ·
            refine ⟨17428396568241697809100301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11618931045494465206066867 17428396568241697809100301)
            ·
              refine ⟨6535648713090636678412613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17428396568241697809100301 6535648713090636678412613)
              ·
                refine ⟨1225434133704494377202365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6535648713090636678412613 1225434133704494377202365)
                ·
                  refine ⟨459537800139185391450887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225434133704494377202365 459537800139185391450887)
                  ·
                    rfl

theorem cell20_1006815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 4, 3].length) (baseStart_1006815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006815 prefixEnd_1006815 := by exact prefixLift 1006815
  have htrace : WordTrace (prefixWord ++ tailWord_1006815) baseStart_1006815 baseEnd_1006815 := by
    simpa [prefixWord, tailWord_1006815, baseEnd_1006815] using wordTrace_append hprefix tailTrace_1006815
  have hstable : (prefixWord ++ tailWord_1006815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006815).length < 2 ^ (prefixWord ++ tailWord_1006815).sum := by decide
  have hdescent : baseEnd_1006815 < baseStart_1006815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006877 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 4]
def baseStart_1006877 : Nat := 118140960795 + 1006877 * 2 ^ 59
def prefixEnd_1006877 : Nat := 4983230072969 + 3 ^ 40 * 1006877 * 2
def baseEnd_1006877 : Nat := 459566098628588731383967

theorem tailTrace_1006877 : CollatzResearch.WordTrace tailWord_1006877 prefixEnd_1006877 459566098628588731383967 := by
  unfold tailWord_1006877
  simp only [CollatzResearch.WordTrace]
  refine ⟨36723821173264064746202885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24482547448842709830801923 36723821173264064746202885)
  ·
    refine ⟨6885716469987012139913041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36723821173264064746202885 6885716469987012139913041)
    ·
      refine ⟨5164287352490259104934781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6885716469987012139913041 5164287352490259104934781)
      ·
        refine ⟨1936607757183847164350543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5164287352490259104934781 1936607757183847164350543)
        ·
          refine ⟨2904911635775770746525815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936607757183847164350543 2904911635775770746525815)
          ·
            refine ⟨4357367453663656119788723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2904911635775770746525815 4357367453663656119788723)
            ·
              refine ⟨6536051180495484179683085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4357367453663656119788723 6536051180495484179683085)
              ·
                refine ⟨2451019192685806567381157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6536051180495484179683085 2451019192685806567381157)
                ·
                  refine ⟨459566098628588731383967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451019192685806567381157 459566098628588731383967)
                  ·
                    rfl

theorem cell20_1006877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_1006877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006877 prefixEnd_1006877 := by exact prefixLift 1006877
  have htrace : WordTrace (prefixWord ++ tailWord_1006877) baseStart_1006877 baseEnd_1006877 := by
    simpa [prefixWord, tailWord_1006877, baseEnd_1006877] using wordTrace_append hprefix tailTrace_1006877
  have hstable : (prefixWord ++ tailWord_1006877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006877).length < 2 ^ (prefixWord ++ tailWord_1006877).sum := by decide
  have hdescent : baseEnd_1006877 < baseStart_1006877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006901 : List Nat := [1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_1006901 : Nat := 118140960795 + 1006901 * 2 ^ 59
def prefixEnd_1006901 : Nat := 4983230072969 + 3 ^ 40 * 1006901 * 2
def baseEnd_1006901 : Nat := 153192350960850438194623

theorem tailTrace_1006901 : CollatzResearch.WordTrace tailWord_1006901 prefixEnd_1006901 153192350960850438194623 := by
  unfold tailWord_1006901
  simp only [CollatzResearch.WordTrace]
  refine ⟨36724696525177116845076557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483131016784744563384371 36724696525177116845076557)
  ·
    refine ⟨13771761196941418816903709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36724696525177116845076557 13771761196941418816903709)
    ·
      refine ⟨5164410448853032056338891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13771761196941418816903709 5164410448853032056338891)
      ·
        refine ⟨7746615673279548084508337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164410448853032056338891 7746615673279548084508337)
        ·
          refine ⟨5809961754959661063381253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7746615673279548084508337 5809961754959661063381253)
          ·
            refine ⟨1089367829054936449383985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5809961754959661063381253 1089367829054936449383985)
            ·
              refine ⟨817025871791202337037989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089367829054936449383985 817025871791202337037989)
              ·
                refine ⟨153192350960850438194623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817025871791202337037989 153192350960850438194623)
                ·
                  rfl

theorem cell20_1006901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_1006901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006901 prefixEnd_1006901 := by exact prefixLift 1006901
  have htrace : WordTrace (prefixWord ++ tailWord_1006901) baseStart_1006901 baseEnd_1006901 := by
    simpa [prefixWord, tailWord_1006901, baseEnd_1006901] using wordTrace_append hprefix tailTrace_1006901
  have hstable : (prefixWord ++ tailWord_1006901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006901).length < 2 ^ (prefixWord ++ tailWord_1006901).sum := by decide
  have hdescent : baseEnd_1006901 < baseStart_1006901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006912 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1006912 : Nat := 118140960795 + 1006912 * 2 ^ 59
def prefixEnd_1006912 : Nat := 4983230072969 + 3 ^ 40 * 1006912 * 2
def baseEnd_1006912 : Nat := 459582073582284165217157

theorem tailTrace_1006912 : CollatzResearch.WordTrace tailWord_1006912 prefixEnd_1006912 459582073582284165217157 := by
  unfold tailWord_1006912
  simp only [CollatzResearch.WordTrace]
  refine ⟨18362548864068632861863495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24483398485424843815817993 18362548864068632861863495)
  ·
    refine ⟨27543823296102949292795243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18362548864068632861863495 27543823296102949292795243)
    ·
      refine ⟨41315734944154423939192865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27543823296102949292795243 41315734944154423939192865)
      ·
        refine ⟨30986801208115817954394649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41315734944154423939192865 30986801208115817954394649)
        ·
          refine ⟨23240100906086863465795987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30986801208115817954394649 23240100906086863465795987)
          ·
            refine ⟨34860151359130295198693981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23240100906086863465795987 34860151359130295198693981)
            ·
              refine ⟨13072556759673860699510243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34860151359130295198693981 13072556759673860699510243)
              ·
                refine ⟨19608835139510791049265365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13072556759673860699510243 19608835139510791049265365)
                ·
                  refine ⟨459582073582284165217157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19608835139510791049265365 459582073582284165217157)
                  ·
                    rfl

theorem cell20_1006912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1006912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006912 prefixEnd_1006912 := by exact prefixLift 1006912
  have htrace : WordTrace (prefixWord ++ tailWord_1006912) baseStart_1006912 baseEnd_1006912 := by
    simpa [prefixWord, tailWord_1006912, baseEnd_1006912] using wordTrace_append hprefix tailTrace_1006912
  have hstable : (prefixWord ++ tailWord_1006912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006912).length < 2 ^ (prefixWord ++ tailWord_1006912).sum := by decide
  have hdescent : baseEnd_1006912 < baseStart_1006912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006929 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 3]
def baseStart_1006929 : Nat := 118140960795 + 1006929 * 2 ^ 59
def prefixEnd_1006929 : Nat := 4983230072969 + 3 ^ 40 * 1006929 * 2
def baseEnd_1006929 : Nat := 459589832845507661650421

theorem tailTrace_1006929 : CollatzResearch.WordTrace tailWord_1006929 prefixEnd_1006929 459589832845507661650421 := by
  unfold tailWord_1006929
  simp only [CollatzResearch.WordTrace]
  refine ⟨36725717769075677627095841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24483811846050451751397227 36725717769075677627095841)
  ·
    refine ⟨27544288326806758220321881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36725717769075677627095841 27544288326806758220321881)
    ·
      refine ⟨20658216245105068665241411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27544288326806758220321881 20658216245105068665241411)
      ·
        refine ⟨30987324367657602997862117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20658216245105068665241411 30987324367657602997862117)
        ·
          refine ⟨5810123318935800562099147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30987324367657602997862117 5810123318935800562099147)
          ·
            refine ⟨8715184978403700843148721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810123318935800562099147 8715184978403700843148721)
            ·
              refine ⟨6536388733802775632361541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8715184978403700843148721 6536388733802775632361541)
              ·
                refine ⟨1225572887588020431067789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6536388733802775632361541 1225572887588020431067789)
                ·
                  refine ⟨459589832845507661650421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225572887588020431067789 459589832845507661650421)
                  ·
                    rfl

theorem cell20_1006929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 3].length) (baseStart_1006929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006929 prefixEnd_1006929 := by exact prefixLift 1006929
  have htrace : WordTrace (prefixWord ++ tailWord_1006929) baseStart_1006929 baseEnd_1006929 := by
    simpa [prefixWord, tailWord_1006929, baseEnd_1006929] using wordTrace_append hprefix tailTrace_1006929
  have hstable : (prefixWord ++ tailWord_1006929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006929).length < 2 ^ (prefixWord ++ tailWord_1006929).sum := by decide
  have hdescent : baseEnd_1006929 < baseStart_1006929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006946 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1006946 : Nat := 118140960795 + 1006946 * 2 ^ 59
def prefixEnd_1006946 : Nat := 4983230072969 + 3 ^ 40 * 1006946 * 2
def baseEnd_1006946 : Nat := 459597592108731158083685

theorem tailTrace_1006946 : CollatzResearch.WordTrace tailWord_1006946 prefixEnd_1006946 459597592108731158083685 := by
  unfold tailWord_1006946
  simp only [CollatzResearch.WordTrace]
  refine ⟨9181584452503522382616173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24484225206676059686976461 9181584452503522382616173)
  ·
    refine ⟨3443094169688820893481065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9181584452503522382616173 3443094169688820893481065)
    ·
      refine ⟨2582320627266615670110799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3443094169688820893481065 2582320627266615670110799)
      ·
        refine ⟨3873480940899923505166199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582320627266615670110799 3873480940899923505166199)
        ·
          refine ⟨5810221411349885257749299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873480940899923505166199 5810221411349885257749299)
          ·
            refine ⟨8715332117024827886623949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5810221411349885257749299 8715332117024827886623949)
            ·
              refine ⟨3268249543884310457483981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8715332117024827886623949 3268249543884310457483981)
              ·
                refine ⟨1225593578956616421556493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3268249543884310457483981 1225593578956616421556493)
                ·
                  refine ⟨459597592108731158083685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225593578956616421556493 459597592108731158083685)
                  ·
                    rfl

theorem cell20_1006946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1006946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006946 prefixEnd_1006946 := by exact prefixLift 1006946
  have htrace : WordTrace (prefixWord ++ tailWord_1006946) baseStart_1006946 baseEnd_1006946 := by
    simpa [prefixWord, tailWord_1006946, baseEnd_1006946] using wordTrace_append hprefix tailTrace_1006946
  have hstable : (prefixWord ++ tailWord_1006946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006946).length < 2 ^ (prefixWord ++ tailWord_1006946).sum := by decide
  have hdescent : baseEnd_1006946 < baseStart_1006946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006984 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1006984 : Nat := 118140960795 + 1006984 * 2 ^ 59
def prefixEnd_1006984 : Nat := 4983230072969 + 3 ^ 40 * 1006984 * 2
def baseEnd_1006984 : Nat := 459614936344171914816863

theorem tailTrace_1006984 : CollatzResearch.WordTrace tailWord_1006984 prefixEnd_1006984 459614936344171914816863 := by
  unfold tailWord_1006984
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363861891938211010174003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24485149189250948013565337 18363861891938211010174003)
  ·
    refine ⟨27545792837907316515261005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18363861891938211010174003 27545792837907316515261005)
    ·
      refine ⟨10329672314215243693222877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27545792837907316515261005 10329672314215243693222877)
      ·
        refine ⟨3873627117830716384958579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10329672314215243693222877 3873627117830716384958579)
        ·
          refine ⟨5810440676746074577437869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873627117830716384958579 5810440676746074577437869)
          ·
            refine ⟨2178915253779777966539201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5810440676746074577437869 2178915253779777966539201)
            ·
              refine ⟨1634186440334833474904401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178915253779777966539201 1634186440334833474904401)
              ·
                refine ⟨1225639830251125106178301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634186440334833474904401 1225639830251125106178301)
                ·
                  refine ⟨459614936344171914816863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225639830251125106178301 459614936344171914816863)
                  ·
                    rfl

theorem cell20_1006984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1006984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006984 prefixEnd_1006984 := by exact prefixLift 1006984
  have htrace : WordTrace (prefixWord ++ tailWord_1006984) baseStart_1006984 baseEnd_1006984 := by
    simpa [prefixWord, tailWord_1006984, baseEnd_1006984] using wordTrace_append hprefix tailTrace_1006984
  have hstable : (prefixWord ++ tailWord_1006984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006984).length < 2 ^ (prefixWord ++ tailWord_1006984).sum := by decide
  have hdescent : baseEnd_1006984 < baseStart_1006984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006994 : List Nat := [3, 2, 3, 3, 1, 2, 1, 5]
def baseStart_1006994 : Nat := 118140960795 + 1006994 * 2 ^ 59
def prefixEnd_1006994 : Nat := 4983230072969 + 3 ^ 40 * 1006994 * 2
def baseEnd_1006994 : Nat := 153206500205552108161163

theorem tailTrace_1006994 : CollatzResearch.WordTrace tailWord_1006994 prefixEnd_1006994 153206500205552108161163 := by
  unfold tailWord_1006994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182022128460048432053009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24485392342560129152141357 9182022128460048432053009)
  ·
    refine ⟨6886516596345036324039757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9182022128460048432053009 6886516596345036324039757)
    ·
      refine ⟨2582443723629388621514909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6886516596345036324039757 2582443723629388621514909)
      ·
        refine ⟨968416396361020733068091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2582443723629388621514909 968416396361020733068091)
        ·
          refine ⟨1452624594541531099602137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968416396361020733068091 1452624594541531099602137)
          ·
            refine ⟨1089468445906148324701603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452624594541531099602137 1089468445906148324701603)
            ·
              refine ⟨1634202668859222487052405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089468445906148324701603 1634202668859222487052405)
              ·
                refine ⟨153206500205552108161163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1634202668859222487052405 153206500205552108161163)
                ·
                  rfl

theorem cell20_1006994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 5].length) (baseStart_1006994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006994 prefixEnd_1006994 := by exact prefixLift 1006994
  have htrace : WordTrace (prefixWord ++ tailWord_1006994) baseStart_1006994 baseEnd_1006994 := by
    simpa [prefixWord, tailWord_1006994, baseEnd_1006994] using wordTrace_append hprefix tailTrace_1006994
  have hstable : (prefixWord ++ tailWord_1006994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006994).length < 2 ^ (prefixWord ++ tailWord_1006994).sum := by decide
  have hdescent : baseEnd_1006994 < baseStart_1006994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1006995 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 10]
def baseStart_1006995 : Nat := 118140960795 + 1006995 * 2 ^ 59
def prefixEnd_1006995 : Nat := 4983230072969 + 3 ^ 40 * 1006995 * 2
def baseEnd_1006995 : Nat := 459619957043904765450151

theorem tailTrace_1006995 : CollatzResearch.WordTrace tailWord_1006995 prefixEnd_1006995 459619957043904765450151 := by
  unfold tailWord_1006995
  simp only [CollatzResearch.WordTrace]
  refine ⟨36728124986836570898998439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24485416657891047265998959 36728124986836570898998439)
  ·
    refine ⟨55092187480254856348497659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36728124986836570898998439 55092187480254856348497659)
    ·
      refine ⟨82638281220382284522746489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55092187480254856348497659 82638281220382284522746489)
      ·
        refine ⟨61978710915286713392059867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82638281220382284522746489 61978710915286713392059867)
        ·
          refine ⟨92968066372930070088089801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61978710915286713392059867 92968066372930070088089801)
          ·
            refine ⟨69726049779697552566067351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92968066372930070088089801 69726049779697552566067351)
            ·
              refine ⟨104589074669546328849101027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69726049779697552566067351 104589074669546328849101027)
              ·
                refine ⟨156883612004319493273651541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104589074669546328849101027 156883612004319493273651541)
                ·
                  refine ⟨459619957043904765450151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 156883612004319493273651541 459619957043904765450151)
                  ·
                    rfl

theorem cell20_1006995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_1006995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1006995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1006995 prefixEnd_1006995 := by exact prefixLift 1006995
  have htrace : WordTrace (prefixWord ++ tailWord_1006995) baseStart_1006995 baseEnd_1006995 := by
    simpa [prefixWord, tailWord_1006995, baseEnd_1006995] using wordTrace_append hprefix tailTrace_1006995
  have hstable : (prefixWord ++ tailWord_1006995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1006995).length < 2 ^ (prefixWord ++ tailWord_1006995).sum := by decide
  have hdescent : baseEnd_1006995 < baseStart_1006995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1006995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007036 : List Nat := [2, 2, 2, 4, 2, 1, 7]
def baseStart_1007036 : Nat := 118140960795 + 1007036 * 2 ^ 59
def prefixEnd_1007036 : Nat := 4983230072969 + 3 ^ 40 * 1007036 * 2
def baseEnd_1007036 : Nat := 51070963395676760564813

theorem tailTrace_1007036 : CollatzResearch.WordTrace tailWord_1007036 prefixEnd_1007036 51070963395676760564813 := by
  unfold tailWord_1007036
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364810189844017450620481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24486413586458689934160641 18364810189844017450620481)
  ·
    refine ⟨13773607642383013087965361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18364810189844017450620481 13773607642383013087965361)
    ·
      refine ⟨10330205731787259815974021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13773607642383013087965361 10330205731787259815974021)
      ·
        refine ⟨1936913574710111215495129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10330205731787259815974021 1936913574710111215495129)
        ·
          refine ⟨1452685181032583411621347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936913574710111215495129 1452685181032583411621347)
          ·
            refine ⟨2179027771548875117432021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452685181032583411621347 2179027771548875117432021)
            ·
              refine ⟨51070963395676760564813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2179027771548875117432021 51070963395676760564813)
              ·
                rfl

theorem cell20_1007036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_1007036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007036 prefixEnd_1007036 := by exact prefixLift 1007036
  have htrace : WordTrace (prefixWord ++ tailWord_1007036) baseStart_1007036 baseEnd_1007036 := by
    simpa [prefixWord, tailWord_1007036, baseEnd_1007036] using wordTrace_append hprefix tailTrace_1007036
  have hstable : (prefixWord ++ tailWord_1007036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007036).length < 2 ^ (prefixWord ++ tailWord_1007036).sum := by decide
  have hdescent : baseEnd_1007036 < baseStart_1007036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007043 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_1007043 : Nat := 118140960795 + 1007043 * 2 ^ 59
def prefixEnd_1007043 : Nat := 4983230072969 + 3 ^ 40 * 1007043 * 2
def baseEnd_1007043 : Nat := 459641865551829931849955

theorem tailTrace_1007043 : CollatzResearch.WordTrace tailWord_1007043 prefixEnd_1007043 459641865551829931849955 := by
  unfold tailWord_1007043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36729875690662675096745783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24486583793775116731163855 36729875690662675096745783)
  ·
    refine ⟨55094813535994012645118675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36729875690662675096745783 55094813535994012645118675)
    ·
      refine ⟨82642220303991018967678013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55094813535994012645118675 82642220303991018967678013)
      ·
        refine ⟨30990832613996632112879255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82642220303991018967678013 30990832613996632112879255)
        ·
          refine ⟨46486248920994948169318883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30990832613996632112879255 46486248920994948169318883)
          ·
            refine ⟨69729373381492422253978325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46486248920994948169318883 69729373381492422253978325)
            ·
              refine ⟨1634282188628728646577617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69729373381492422253978325 1634282188628728646577617)
              ·
                refine ⟨1225711641471546484933213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1634282188628728646577617 1225711641471546484933213)
                ·
                  refine ⟨459641865551829931849955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225711641471546484933213 459641865551829931849955)
                  ·
                    rfl

theorem cell20_1007043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_1007043 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007043 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007043 prefixEnd_1007043 := by exact prefixLift 1007043
  have htrace : WordTrace (prefixWord ++ tailWord_1007043) baseStart_1007043 baseEnd_1007043 := by
    simpa [prefixWord, tailWord_1007043, baseEnd_1007043] using wordTrace_append hprefix tailTrace_1007043
  have hstable : (prefixWord ++ tailWord_1007043).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007043).length < 2 ^ (prefixWord ++ tailWord_1007043).sum := by decide
  have hdescent : baseEnd_1007043 < baseStart_1007043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007050 : List Nat := [3, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1007050 : Nat := 118140960795 + 1007050 * 2 ^ 59
def prefixEnd_1007050 : Nat := 4983230072969 + 3 ^ 40 * 1007050 * 2
def baseEnd_1007050 : Nat := 459645060542569018616593

theorem tailTrace_1007050 : CollatzResearch.WordTrace tailWord_1007050 prefixEnd_1007050 459645060542569018616593 := by
  unfold tailWord_1007050
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182532750409328823062651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24486754001091543528167069 9182532750409328823062651)
  ·
    refine ⟨13773799125613993234593977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9182532750409328823062651 13773799125613993234593977)
    ·
      refine ⟨10330349344210494925945483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13773799125613993234593977 10330349344210494925945483)
      ·
        refine ⟨15495524016315742388918225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10330349344210494925945483 15495524016315742388918225)
        ·
          refine ⟨11621643012236806791688669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15495524016315742388918225 11621643012236806791688669)
          ·
            refine ⟨4358116129588802546883251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11621643012236806791688669 4358116129588802546883251)
            ·
              refine ⟨6537174194383203820324877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358116129588802546883251 6537174194383203820324877)
              ·
                refine ⟨2451440322893701432621829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6537174194383203820324877 2451440322893701432621829)
                ·
                  refine ⟨459645060542569018616593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2451440322893701432621829 459645060542569018616593)
                  ·
                    rfl

theorem cell20_1007050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1007050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007050 prefixEnd_1007050 := by exact prefixLift 1007050
  have htrace : WordTrace (prefixWord ++ tailWord_1007050) baseStart_1007050 baseEnd_1007050 := by
    simpa [prefixWord, tailWord_1007050, baseEnd_1007050] using wordTrace_append hprefix tailTrace_1007050
  have hstable : (prefixWord ++ tailWord_1007050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007050).length < 2 ^ (prefixWord ++ tailWord_1007050).sum := by decide
  have hdescent : baseEnd_1007050 < baseStart_1007050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007115 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 3]
def baseStart_1007115 : Nat := 118140960795 + 1007115 * 2 ^ 59
def prefixEnd_1007115 : Nat := 4983230072969 + 3 ^ 40 * 1007115 * 2
def baseEnd_1007115 : Nat := 459674728313717681449661

theorem tailTrace_1007115 : CollatzResearch.WordTrace tailWord_1007115 prefixEnd_1007115 459674728313717681449661 := by
  unfold tailWord_1007115
  simp only [CollatzResearch.WordTrace]
  refine ⟨36732501746401831393366799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24488334497601220928911199 36732501746401831393366799)
  ·
    refine ⟨55098752619602747090050199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36732501746401831393366799 55098752619602747090050199)
    ·
      refine ⟨82648128929404120635075299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55098752619602747090050199 82648128929404120635075299)
      ·
        refine ⟨123972193394106180952612949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82648128929404120635075299 123972193394106180952612949)
        ·
          refine ⟨1452799141337181808038433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 123972193394106180952612949 1452799141337181808038433)
          ·
            refine ⟨1089599356002886356028825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452799141337181808038433 1089599356002886356028825)
            ·
              refine ⟨817199517002164767021619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089599356002886356028825 817199517002164767021619)
              ·
                refine ⟨1225799275503247150532429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817199517002164767021619 1225799275503247150532429)
                ·
                  refine ⟨459674728313717681449661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225799275503247150532429 459674728313717681449661)
                  ·
                    rfl

theorem cell20_1007115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_1007115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007115 prefixEnd_1007115 := by exact prefixLift 1007115
  have htrace : WordTrace (prefixWord ++ tailWord_1007115) baseStart_1007115 baseEnd_1007115 := by
    simpa [prefixWord, tailWord_1007115, baseEnd_1007115] using wordTrace_append hprefix tailTrace_1007115
  have hstable : (prefixWord ++ tailWord_1007115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007115).length < 2 ^ (prefixWord ++ tailWord_1007115).sum := by decide
  have hdescent : baseEnd_1007115 < baseStart_1007115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007133 : List Nat := [1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_1007133 : Nat := 118140960795 + 1007133 * 2 ^ 59
def prefixEnd_1007133 : Nat := 4983230072969 + 3 ^ 40 * 1007133 * 2
def baseEnd_1007133 : Nat := 153227648001396539616529

theorem tailTrace_1007133 : CollatzResearch.WordTrace tailWord_1007133 prefixEnd_1007133 153227648001396539616529 := by
  unfold tailWord_1007133
  simp only [CollatzResearch.WordTrace]
  refine ⟨36733158260336620467522053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24488772173557746978348035 36733158260336620467522053)
  ·
    refine ⟨6887467173813116337660385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36733158260336620467522053 6887467173813116337660385)
    ·
      refine ⟨5165600380359837253245289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6887467173813116337660385 5165600380359837253245289)
      ·
        refine ⟨3874200285269877939933967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5165600380359837253245289 3874200285269877939933967)
        ·
          refine ⟨5811300427904816909900951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874200285269877939933967 5811300427904816909900951)
          ·
            refine ⟨8716950641857225364851427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5811300427904816909900951 8716950641857225364851427)
            ·
              refine ⟨13075425962785838047277141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8716950641857225364851427 13075425962785838047277141)
              ·
                refine ⟨153227648001396539616529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13075425962785838047277141 153227648001396539616529)
                ·
                  rfl

theorem cell20_1007133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_1007133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007133 prefixEnd_1007133 := by exact prefixLift 1007133
  have htrace : WordTrace (prefixWord ++ tailWord_1007133) baseStart_1007133 baseEnd_1007133 := by
    simpa [prefixWord, tailWord_1007133, baseEnd_1007133] using wordTrace_append hprefix tailTrace_1007133
  have hstable : (prefixWord ++ tailWord_1007133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007133).length < 2 ^ (prefixWord ++ tailWord_1007133).sum := by decide
  have hdescent : baseEnd_1007133 < baseStart_1007133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007157 : List Nat := [1, 3, 3, 1, 1, 3, 1, 4, 3]
def baseStart_1007157 : Nat := 118140960795 + 1007157 * 2 ^ 59
def prefixEnd_1007157 : Nat := 4983230072969 + 3 ^ 40 * 1007157 * 2
def baseEnd_1007157 : Nat := 459693898258152202049489

theorem tailTrace_1007157 : CollatzResearch.WordTrace tailWord_1007157 prefixEnd_1007157 459693898258152202049489 := by
  unfold tailWord_1007157
  simp only [CollatzResearch.WordTrace]
  refine ⟨36734033612249672566395725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24489355741499781710930483 36734033612249672566395725)
  ·
    refine ⟨13775262604593627212398397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36734033612249672566395725 13775262604593627212398397)
    ·
      refine ⟨5165723476722610204649399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13775262604593627212398397 5165723476722610204649399)
      ·
        refine ⟨7748585215083915306974099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165723476722610204649399 7748585215083915306974099)
        ·
          refine ⟨11622877822625872960461149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748585215083915306974099 11622877822625872960461149)
          ·
            refine ⟨4358579183484702360172931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11622877822625872960461149 4358579183484702360172931)
            ·
              refine ⟨6537868775227053540259397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358579183484702360172931 6537868775227053540259397)
              ·
                refine ⟨1225850395355072538798637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6537868775227053540259397 1225850395355072538798637)
                ·
                  refine ⟨459693898258152202049489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225850395355072538798637 459693898258152202049489)
                  ·
                    rfl

theorem cell20_1007157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 3].length) (baseStart_1007157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007157 prefixEnd_1007157 := by exact prefixLift 1007157
  have htrace : WordTrace (prefixWord ++ tailWord_1007157) baseStart_1007157 baseEnd_1007157 := by
    simpa [prefixWord, tailWord_1007157, baseEnd_1007157] using wordTrace_append hprefix tailTrace_1007157
  have hstable : (prefixWord ++ tailWord_1007157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007157).length < 2 ^ (prefixWord ++ tailWord_1007157).sum := by decide
  have hdescent : baseEnd_1007157 < baseStart_1007157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007160 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_1007160 : Nat := 118140960795 + 1007160 * 2 ^ 59
def prefixEnd_1007160 : Nat := 4983230072969 + 3 ^ 40 * 1007160 * 2
def baseEnd_1007160 : Nat := 459695267539897524949477

theorem tailTrace_1007160 : CollatzResearch.WordTrace tailWord_1007160 prefixEnd_1007160 459695267539897524949477 := by
  unfold tailWord_1007160
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367071515619402039377467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24489428687492536052503289 18367071515619402039377467)
  ·
    refine ⟨27550607273429103059066201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18367071515619402039377467 27550607273429103059066201)
    ·
      refine ⟨20662955455071827294299651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27550607273429103059066201 20662955455071827294299651)
      ·
        refine ⟨30994433182607740941449477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20662955455071827294299651 30994433182607740941449477)
        ·
          refine ⟨5811456221738951426521777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30994433182607740941449477 5811456221738951426521777)
          ·
            refine ⟨4358592166304213569891333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5811456221738951426521777 4358592166304213569891333)
            ·
              refine ⟨817236031182040044354625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4358592166304213569891333 817236031182040044354625)
              ·
                refine ⟨612927023386530033265969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817236031182040044354625 612927023386530033265969)
                ·
                  refine ⟨459695267539897524949477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612927023386530033265969 459695267539897524949477)
                  ·
                    rfl

theorem cell20_1007160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_1007160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007160 prefixEnd_1007160 := by exact prefixLift 1007160
  have htrace : WordTrace (prefixWord ++ tailWord_1007160) baseStart_1007160 baseEnd_1007160 := by
    simpa [prefixWord, tailWord_1007160, baseEnd_1007160] using wordTrace_append hprefix tailTrace_1007160
  have hstable : (prefixWord ++ tailWord_1007160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007160).length < 2 ^ (prefixWord ++ tailWord_1007160).sum := by decide
  have hdescent : baseEnd_1007160 < baseStart_1007160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007188 : List Nat := [2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_1007188 : Nat := 118140960795 + 1007188 * 2 ^ 59
def prefixEnd_1007188 : Nat := 4983230072969 + 3 ^ 40 * 1007188 * 2
def baseEnd_1007188 : Nat := 153236015834284624005343

theorem tailTrace_1007188 : CollatzResearch.WordTrace tailWord_1007188 prefixEnd_1007188 153236015834284624005343 := by
  unfold tailWord_1007188
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367582137568682430387109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24490109516758243240516145 18367582137568682430387109)
  ·
    refine ⟨3443921650794127955697583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18367582137568682430387109 3443921650794127955697583)
    ·
      refine ⟨5165882476191191933546375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3443921650794127955697583 5165882476191191933546375)
      ·
        refine ⟨7748823714286787900319563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165882476191191933546375 7748823714286787900319563)
        ·
          refine ⟨11623235571430181850479345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7748823714286787900319563 11623235571430181850479345)
          ·
            refine ⟨8717426678572636387859509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11623235571430181850479345 8717426678572636387859509)
            ·
              refine ⟨817258751116184661361829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8717426678572636387859509 817258751116184661361829)
              ·
                refine ⟨153236015834284624005343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817258751116184661361829 153236015834284624005343)
                ·
                  rfl

theorem cell20_1007188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_1007188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007188 prefixEnd_1007188 := by exact prefixLift 1007188
  have htrace : WordTrace (prefixWord ++ tailWord_1007188) baseStart_1007188 baseEnd_1007188 := by
    simpa [prefixWord, tailWord_1007188, baseEnd_1007188] using wordTrace_append hprefix tailTrace_1007188
  have hstable : (prefixWord ++ tailWord_1007188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007188).length < 2 ^ (prefixWord ++ tailWord_1007188).sum := by decide
  have hdescent : baseEnd_1007188 < baseStart_1007188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007325 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 2]
def baseStart_1007325 : Nat := 118140960795 + 1007325 * 2 ^ 59
def prefixEnd_1007325 : Nat := 4983230072969 + 3 ^ 40 * 1007325 * 2
def baseEnd_1007325 : Nat := 459770578035890284448803

theorem tailTrace_1007325 : CollatzResearch.WordTrace tailWord_1007325 prefixEnd_1007325 459770578035890284448803 := by
  unfold tailWord_1007325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740161075641037258511429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24493440717094024839007619 36740161075641037258511429)
  ·
    refine ⟨6888780201682694485970893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36740161075641037258511429 6888780201682694485970893)
    ·
      refine ⟨2583292575631010432239085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6888780201682694485970893 2583292575631010432239085)
      ·
        refine ⟨968734715861628912089657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2583292575631010432239085 968734715861628912089657)
        ·
          refine ⟨726551036896221684067243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968734715861628912089657 726551036896221684067243)
          ·
            refine ⟨1089826555344332526100865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726551036896221684067243 1089826555344332526100865)
            ·
              refine ⟨817369916508249394575649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089826555344332526100865 817369916508249394575649)
              ·
                refine ⟨613027437381187045931737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817369916508249394575649 613027437381187045931737)
                ·
                  refine ⟨459770578035890284448803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613027437381187045931737 459770578035890284448803)
                  ·
                    rfl

theorem cell20_1007325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_1007325 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007325 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007325 prefixEnd_1007325 := by exact prefixLift 1007325
  have htrace : WordTrace (prefixWord ++ tailWord_1007325) baseStart_1007325 baseEnd_1007325 := by
    simpa [prefixWord, tailWord_1007325, baseEnd_1007325] using wordTrace_append hprefix tailTrace_1007325
  have hstable : (prefixWord ++ tailWord_1007325).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007325).length < 2 ^ (prefixWord ++ tailWord_1007325).sum := by decide
  have hdescent : baseEnd_1007325 < baseStart_1007325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007329 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 2]
def baseStart_1007329 : Nat := 118140960795 + 1007329 * 2 ^ 59
def prefixEnd_1007329 : Nat := 4983230072969 + 3 ^ 40 * 1007329 * 2
def baseEnd_1007329 : Nat := 459772403744884048315453

theorem tailTrace_1007329 : CollatzResearch.WordTrace tailWord_1007329 prefixEnd_1007329 459772403744884048315453 := by
  unfold tailWord_1007329
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740306967626545941657041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24493537978417697294438027 36740306967626545941657041)
  ·
    refine ⟨27555230225719909456242781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36740306967626545941657041 27555230225719909456242781)
    ·
      refine ⟨10333211334644966046091043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27555230225719909456242781 10333211334644966046091043)
      ·
        refine ⟨15499817001967449069136565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10333211334644966046091043 15499817001967449069136565)
        ·
          refine ⟨1453107843934448350231553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15499817001967449069136565 1453107843934448350231553)
          ·
            refine ⟨1089830882950836262673665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453107843934448350231553 1089830882950836262673665)
            ·
              refine ⟨817373162213127197005249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089830882950836262673665 817373162213127197005249)
              ·
                refine ⟨613029871659845397753937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817373162213127197005249 613029871659845397753937)
                ·
                  refine ⟨459772403744884048315453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613029871659845397753937 459772403744884048315453)
                  ·
                    rfl

theorem cell20_1007329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_1007329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007329 prefixEnd_1007329 := by exact prefixLift 1007329
  have htrace : WordTrace (prefixWord ++ tailWord_1007329) baseStart_1007329 baseEnd_1007329 := by
    simpa [prefixWord, tailWord_1007329, baseEnd_1007329] using wordTrace_append hprefix tailTrace_1007329
  have hstable : (prefixWord ++ tailWord_1007329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007329).length < 2 ^ (prefixWord ++ tailWord_1007329).sum := by decide
  have hdescent : baseEnd_1007329 < baseStart_1007329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007333 : List Nat := [1, 3, 1, 4, 1, 1, 3, 4, 2]
def baseStart_1007333 : Nat := 118140960795 + 1007333 * 2 ^ 59
def prefixEnd_1007333 : Nat := 4983230072969 + 3 ^ 40 * 1007333 * 2
def baseEnd_1007333 : Nat := 459774229453877812182103

theorem tailTrace_1007333 : CollatzResearch.WordTrace tailWord_1007333 prefixEnd_1007333 459774229453877812182103 := by
  unfold tailWord_1007333
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740452859612054624802653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24493635239741369749868435 36740452859612054624802653)
  ·
    refine ⟨13777669822354520484300995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36740452859612054624802653 13777669822354520484300995)
    ·
      refine ⟨20666504733531780726451493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13777669822354520484300995 20666504733531780726451493)
      ·
        refine ⟨3874969637537208886209655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20666504733531780726451493 3874969637537208886209655)
        ·
          refine ⟨5812454456305813329314483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874969637537208886209655 5812454456305813329314483)
          ·
            refine ⟨8718681684458719993971725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812454456305813329314483 8718681684458719993971725)
            ·
              refine ⟨3269505631672019997739397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8718681684458719993971725 3269505631672019997739397)
              ·
                refine ⟨613032305938503749576137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3269505631672019997739397 613032305938503749576137)
                ·
                  refine ⟨459774229453877812182103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613032305938503749576137 459774229453877812182103)
                  ·
                    rfl

theorem cell20_1007333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_1007333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007333 prefixEnd_1007333 := by exact prefixLift 1007333
  have htrace : WordTrace (prefixWord ++ tailWord_1007333) baseStart_1007333 baseEnd_1007333 := by
    simpa [prefixWord, tailWord_1007333, baseEnd_1007333] using wordTrace_append hprefix tailTrace_1007333
  have hstable : (prefixWord ++ tailWord_1007333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007333).length < 2 ^ (prefixWord ++ tailWord_1007333).sum := by decide
  have hdescent : baseEnd_1007333 < baseStart_1007333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007337 : List Nat := [1, 2, 1, 1, 1, 2, 3, 5, 4]
def baseStart_1007337 : Nat := 118140960795 + 1007337 * 2 ^ 59
def prefixEnd_1007337 : Nat := 4983230072969 + 3 ^ 40 * 1007337 * 2
def baseEnd_1007337 : Nat := 459776055162871576048753

theorem tailTrace_1007337 : CollatzResearch.WordTrace tailWord_1007337 prefixEnd_1007337 459776055162871576048753 := by
  unfold tailWord_1007337
  simp only [CollatzResearch.WordTrace]
  refine ⟨36740598751597563307948265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24493732501065042205298843 36740598751597563307948265)
  ·
    refine ⟨27555449063698172480961199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36740598751597563307948265 27555449063698172480961199)
    ·
      refine ⟨41333173595547258721441799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27555449063698172480961199 41333173595547258721441799)
      ·
        refine ⟨61999760393320888082162699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41333173595547258721441799 61999760393320888082162699)
        ·
          refine ⟨92999640589981332123244049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61999760393320888082162699 92999640589981332123244049)
          ·
            refine ⟨69749730442485999092433037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92999640589981332123244049 69749730442485999092433037)
            ·
              refine ⟨26156148915932249659662389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69749730442485999092433037 26156148915932249659662389)
              ·
                refine ⟨2452138960868648405593349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26156148915932249659662389 2452138960868648405593349)
                ·
                  refine ⟨459776055162871576048753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452138960868648405593349 459776055162871576048753)
                  ·
                    rfl

theorem cell20_1007337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 4].length) (baseStart_1007337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007337 prefixEnd_1007337 := by exact prefixLift 1007337
  have htrace : WordTrace (prefixWord ++ tailWord_1007337) baseStart_1007337 baseEnd_1007337 := by
    simpa [prefixWord, tailWord_1007337, baseEnd_1007337] using wordTrace_append hprefix tailTrace_1007337
  have hstable : (prefixWord ++ tailWord_1007337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007337).length < 2 ^ (prefixWord ++ tailWord_1007337).sum := by decide
  have hdescent : baseEnd_1007337 < baseStart_1007337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007344 : List Nat := [2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_1007344 : Nat := 118140960795 + 1007344 * 2 ^ 59
def prefixEnd_1007344 : Nat := 4983230072969 + 3 ^ 40 * 1007344 * 2
def baseEnd_1007344 : Nat := 153259750051203554271797

theorem tailTrace_1007344 : CollatzResearch.WordTrace tailWord_1007344 prefixEnd_1007344 153259750051203554271797 := by
  unfold tailWord_1007344
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370427031286101751726543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24493902708381469002302057 18370427031286101751726543)
  ·
    refine ⟨27555640546929152627589815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18370427031286101751726543 27555640546929152627589815)
    ·
      refine ⟨41333460820393728941384723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27555640546929152627589815 41333460820393728941384723)
      ·
        refine ⟨62000191230590593412077085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41333460820393728941384723 62000191230590593412077085)
        ·
          refine ⟨23250071711471472529528907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62000191230590593412077085 23250071711471472529528907)
          ·
            refine ⟨34875107567207208794293361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23250071711471472529528907 34875107567207208794293361)
            ·
              refine ⟨26156330675405406595720021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34875107567207208794293361 26156330675405406595720021)
              ·
                refine ⟨153259750051203554271797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26156330675405406595720021 153259750051203554271797)
                ·
                  rfl

theorem cell20_1007344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_1007344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007344 prefixEnd_1007344 := by exact prefixLift 1007344
  have htrace : WordTrace (prefixWord ++ tailWord_1007344) baseStart_1007344 baseEnd_1007344 := by
    simpa [prefixWord, tailWord_1007344, baseEnd_1007344] using wordTrace_append hprefix tailTrace_1007344
  have hstable : (prefixWord ++ tailWord_1007344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007344).length < 2 ^ (prefixWord ++ tailWord_1007344).sum := by decide
  have hdescent : baseEnd_1007344 < baseStart_1007344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007368 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1007368 : Nat := 118140960795 + 1007368 * 2 ^ 59
def prefixEnd_1007368 : Nat := 4983230072969 + 3 ^ 40 * 1007368 * 2
def baseEnd_1007368 : Nat := 459790204407573246015293

theorem tailTrace_1007368 : CollatzResearch.WordTrace tailWord_1007368 prefixEnd_1007368 459790204407573246015293 := by
  unfold tailWord_1007368
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370864707242627801163379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24494486276323503734884505 18370864707242627801163379)
  ·
    refine ⟨27556297060863941701745069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18370864707242627801163379 27556297060863941701745069)
    ·
      refine ⟨10333611397823978138154401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27556297060863941701745069 10333611397823978138154401)
      ·
        refine ⟨7750208548367983603615801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10333611397823978138154401 7750208548367983603615801)
        ·
          refine ⟨5812656411275987702711851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7750208548367983603615801 5812656411275987702711851)
          ·
            refine ⟨8718984616913981554067777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812656411275987702711851 8718984616913981554067777)
            ·
              refine ⟨6539238462685486165550833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8718984616913981554067777 6539238462685486165550833)
              ·
                refine ⟨4904428847014114624163125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6539238462685486165550833 4904428847014114624163125)
                ·
                  refine ⟨459790204407573246015293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4904428847014114624163125 459790204407573246015293)
                  ·
                    rfl

theorem cell20_1007368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1007368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007368 prefixEnd_1007368 := by exact prefixLift 1007368
  have htrace : WordTrace (prefixWord ++ tailWord_1007368) baseStart_1007368 baseEnd_1007368 := by
    simpa [prefixWord, tailWord_1007368, baseEnd_1007368] using wordTrace_append hprefix tailTrace_1007368
  have hstable : (prefixWord ++ tailWord_1007368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007368).length < 2 ^ (prefixWord ++ tailWord_1007368).sum := by decide
  have hdescent : baseEnd_1007368 < baseStart_1007368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007378 : List Nat := [3, 2, 4, 1, 1, 2, 7]
def baseStart_1007378 : Nat := 118140960795 + 1007378 * 2 ^ 59
def prefixEnd_1007378 : Nat := 4983230072969 + 3 ^ 40 * 1007378 * 2
def baseEnd_1007378 : Nat := 51088307631117517297991

theorem tailTrace_1007378 : CollatzResearch.WordTrace tailWord_1007378 prefixEnd_1007378 51088307631117517297991 := by
  unfold tailWord_1007378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9185523536112256827547697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24494729429632684873460525 9185523536112256827547697)
  ·
    refine ⟨6889142652084192620660773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9185523536112256827547697 6889142652084192620660773)
    ·
      refine ⟨1291714247265786116373895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6889142652084192620660773 1291714247265786116373895)
      ·
        refine ⟨1937571370898679174560843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291714247265786116373895 1937571370898679174560843)
        ·
          refine ⟨2906357056348018761841265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1937571370898679174560843 2906357056348018761841265)
          ·
            refine ⟨2179767792261014071380949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2906357056348018761841265 2179767792261014071380949)
            ·
              refine ⟨51088307631117517297991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2179767792261014071380949 51088307631117517297991)
              ·
                rfl

theorem cell20_1007378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_1007378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007378 prefixEnd_1007378 := by exact prefixLift 1007378
  have htrace : WordTrace (prefixWord ++ tailWord_1007378) baseStart_1007378 baseEnd_1007378 := by
    simpa [prefixWord, tailWord_1007378, baseEnd_1007378] using wordTrace_append hprefix tailTrace_1007378
  have hstable : (prefixWord ++ tailWord_1007378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007378).length < 2 ^ (prefixWord ++ tailWord_1007378).sum := by decide
  have hdescent : baseEnd_1007378 < baseStart_1007378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007392 : List Nat := [2, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1007392 : Nat := 118140960795 + 1007392 * 2 ^ 59
def prefixEnd_1007392 : Nat := 4983230072969 + 3 ^ 40 * 1007392 * 2
def baseEnd_1007392 : Nat := 459801158661535829215195

theorem tailTrace_1007392 : CollatzResearch.WordTrace tailWord_1007392 prefixEnd_1007392 459801158661535829215195 := by
  unfold tailWord_1007392
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371302383199153850600215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24495069844265538467466953 18371302383199153850600215)
  ·
    refine ⟨27556953574798730775900323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18371302383199153850600215 27556953574798730775900323)
    ·
      refine ⟨41335430362198096163850485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27556953574798730775900323 41335430362198096163850485)
      ·
        refine ⟨3875196596456071515360983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41335430362198096163850485 3875196596456071515360983)
        ·
          refine ⟨5812794894684107273041475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3875196596456071515360983 5812794894684107273041475)
          ·
            refine ⟨8719192342026160909562213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812794894684107273041475 8719192342026160909562213)
            ·
              refine ⟨1634848564129905170542915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8719192342026160909562213 1634848564129905170542915)
              ·
                refine ⟨2452272846194857755814373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634848564129905170542915 2452272846194857755814373)
                ·
                  refine ⟨459801158661535829215195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452272846194857755814373 459801158661535829215195)
                  ·
                    rfl

theorem cell20_1007392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1007392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007392 prefixEnd_1007392 := by exact prefixLift 1007392
  have htrace : WordTrace (prefixWord ++ tailWord_1007392) baseStart_1007392 baseEnd_1007392 := by
    simpa [prefixWord, tailWord_1007392, baseEnd_1007392] using wordTrace_append hprefix tailTrace_1007392
  have hstable : (prefixWord ++ tailWord_1007392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007392).length < 2 ^ (prefixWord ++ tailWord_1007392).sum := by decide
  have hdescent : baseEnd_1007392 < baseStart_1007392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007416 : List Nat := [2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_1007416 : Nat := 118140960795 + 1007416 * 2 ^ 59
def prefixEnd_1007416 : Nat := 4983230072969 + 3 ^ 40 * 1007416 * 2
def baseEnd_1007416 : Nat := 153270704305166137471699

theorem tailTrace_1007416 : CollatzResearch.WordTrace tailWord_1007416 prefixEnd_1007416 153270704305166137471699 := by
  unfold tailWord_1007416
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371740059155679900037051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24495653412207573200049401 18371740059155679900037051)
  ·
    refine ⟨27557610088733519850055577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18371740059155679900037051 27557610088733519850055577)
    ·
      refine ⟨20668207566550139887541683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27557610088733519850055577 20668207566550139887541683)
      ·
        refine ⟨31002311349825209831312525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20668207566550139887541683 31002311349825209831312525)
        ·
          refine ⟨11625866756184453686742197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31002311349825209831312525 11625866756184453686742197)
          ·
            refine ⟨1089925008392292533132081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11625866756184453686742197 1089925008392292533132081)
            ·
              refine ⟨817443756294219399849061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1089925008392292533132081 817443756294219399849061)
              ·
                refine ⟨153270704305166137471699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 817443756294219399849061 153270704305166137471699)
                ·
                  rfl

theorem cell20_1007416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_1007416 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007416 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007416 prefixEnd_1007416 := by exact prefixLift 1007416
  have htrace : WordTrace (prefixWord ++ tailWord_1007416) baseStart_1007416 baseEnd_1007416 := by
    simpa [prefixWord, tailWord_1007416, baseEnd_1007416] using wordTrace_append hprefix tailTrace_1007416
  have hstable : (prefixWord ++ tailWord_1007416).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007416).length < 2 ^ (prefixWord ++ tailWord_1007416).sum := by decide
  have hdescent : baseEnd_1007416 < baseStart_1007416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007447 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 4]
def baseStart_1007447 : Nat := 118140960795 + 1007447 * 2 ^ 59
def prefixEnd_1007447 : Nat := 4983230072969 + 3 ^ 40 * 1007447 * 2
def baseEnd_1007447 : Nat := 459826262160200082381637

theorem tailTrace_1007447 : CollatzResearch.WordTrace tailWord_1007447 prefixEnd_1007447 459826262160200082381637 := by
  unfold tailWord_1007447
  simp only [CollatzResearch.WordTrace]
  refine ⟨36744610781199052094452595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24496407187466034729635063 36744610781199052094452595)
  ·
    refine ⟨55116916171798578141678893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36744610781199052094452595 55116916171798578141678893)
    ·
      refine ⟨20668843564424466803129585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55116916171798578141678893 20668843564424466803129585)
      ·
        refine ⟨15501632673318350102347189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20668843564424466803129585 15501632673318350102347189)
        ·
          refine ⟨1453278063123595322095049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15501632673318350102347189 1453278063123595322095049)
          ·
            refine ⟨1089958547342696491571287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453278063123595322095049 1089958547342696491571287)
            ·
              refine ⟨1634937821014044737356931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089958547342696491571287 1634937821014044737356931)
              ·
                refine ⟨2452406731521067106035397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634937821014044737356931 2452406731521067106035397)
                ·
                  refine ⟨459826262160200082381637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452406731521067106035397 459826262160200082381637)
                  ·
                    rfl

theorem cell20_1007447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 4].length) (baseStart_1007447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007447 prefixEnd_1007447 := by exact prefixLift 1007447
  have htrace : WordTrace (prefixWord ++ tailWord_1007447) baseStart_1007447 baseEnd_1007447 := by
    simpa [prefixWord, tailWord_1007447, baseEnd_1007447] using wordTrace_append hprefix tailTrace_1007447
  have hstable : (prefixWord ++ tailWord_1007447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007447).length < 2 ^ (prefixWord ++ tailWord_1007447).sum := by decide
  have hdescent : baseEnd_1007447 < baseStart_1007447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007496 : List Nat := [2, 1, 3, 3, 11]
def baseStart_1007496 : Nat := 118140960795 + 1007496 * 2 ^ 59
def prefixEnd_1007496 : Nat := 4983230072969 + 3 ^ 40 * 1007496 * 2
def baseEnd_1007496 : Nat := 5677143544387329503063

theorem tailTrace_1007496 : CollatzResearch.WordTrace tailWord_1007496 prefixEnd_1007496 5677143544387329503063 := by
  unfold tailWord_1007496
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373198979010766731493171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24497598638681022308657561 18373198979010766731493171)
  ·
    refine ⟨27559798468516150097239757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373198979010766731493171 27559798468516150097239757)
    ·
      refine ⟨10334924425693556286464909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27559798468516150097239757 10334924425693556286464909)
      ·
        refine ⟨3875596659635083607424341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10334924425693556286464909 3875596659635083607424341)
        ·
          refine ⟨5677143544387329503063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3875596659635083607424341 5677143544387329503063)
          ·
            rfl

theorem cell20_1007496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 11].length) (baseStart_1007496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007496 prefixEnd_1007496 := by exact prefixLift 1007496
  have htrace : WordTrace (prefixWord ++ tailWord_1007496) baseStart_1007496 baseEnd_1007496 := by
    simpa [prefixWord, tailWord_1007496, baseEnd_1007496] using wordTrace_append hprefix tailTrace_1007496
  have hstable : (prefixWord ++ tailWord_1007496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007496).length < 2 ^ (prefixWord ++ tailWord_1007496).sum := by decide
  have hdescent : baseEnd_1007496 < baseStart_1007496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007498 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 2]
def baseStart_1007498 : Nat := 118140960795 + 1007498 * 2 ^ 59
def prefixEnd_1007498 : Nat := 4983230072969 + 3 ^ 40 * 1007498 * 2
def baseEnd_1007498 : Nat := 459849539949870571681429

theorem tailTrace_1007498 : CollatzResearch.WordTrace tailWord_1007498 prefixEnd_1007498 459849539949870571681429 := by
  unfold tailWord_1007498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9186617726003571951139787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24497647269342858536372765 9186617726003571951139787)
  ·
    refine ⟨13779926589005357926709681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9186617726003571951139787 13779926589005357926709681)
    ·
      refine ⟨10334944941754018445032261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13779926589005357926709681 10334944941754018445032261)
      ·
        refine ⟨1937802176578878458443549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10334944941754018445032261 1937802176578878458443549)
        ·
          refine ⟨726675816217079421916331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1937802176578878458443549 726675816217079421916331)
          ·
            refine ⟨1090013724325619132874497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726675816217079421916331 1090013724325619132874497)
            ·
              refine ⟨817510293244214349655873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090013724325619132874497 817510293244214349655873)
              ·
                refine ⟨613132719933160762241905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817510293244214349655873 613132719933160762241905)
                ·
                  refine ⟨459849539949870571681429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613132719933160762241905 459849539949870571681429)
                  ·
                    rfl

theorem cell20_1007498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 2].length) (baseStart_1007498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007498 prefixEnd_1007498 := by exact prefixLift 1007498
  have htrace : WordTrace (prefixWord ++ tailWord_1007498) baseStart_1007498 baseEnd_1007498 := by
    simpa [prefixWord, tailWord_1007498, baseEnd_1007498] using wordTrace_append hprefix tailTrace_1007498
  have hstable : (prefixWord ++ tailWord_1007498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007498).length < 2 ^ (prefixWord ++ tailWord_1007498).sum := by decide
  have hdescent : baseEnd_1007498 < baseStart_1007498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007503 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1007503 : Nat := 118140960795 + 1007503 * 2 ^ 59
def prefixEnd_1007503 : Nat := 4983230072969 + 3 ^ 40 * 1007503 * 2
def baseEnd_1007503 : Nat := 459851822086112776514741

theorem tailTrace_1007503 : CollatzResearch.WordTrace tailWord_1007503 prefixEnd_1007503 459851822086112776514741 := by
  unfold tailWord_1007503
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746653268996173658491163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24497768845997449105660775 36746653268996173658491163)
  ·
    refine ⟨55119979903494260487736745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36746653268996173658491163 55119979903494260487736745)
    ·
      refine ⟨41339984927620695365802559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55119979903494260487736745 41339984927620695365802559)
      ·
        refine ⟨62009977391431043048703839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41339984927620695365802559 62009977391431043048703839)
        ·
          refine ⟨93014966087146564573055759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62009977391431043048703839 93014966087146564573055759)
          ·
            refine ⟨139522449130719846859583639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93014966087146564573055759 139522449130719846859583639)
            ·
              refine ⟨209283673696079770289375459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139522449130719846859583639 209283673696079770289375459)
              ·
                refine ⟨313925510544119655434063189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209283673696079770289375459 313925510544119655434063189)
                ·
                  refine ⟨459851822086112776514741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 313925510544119655434063189 459851822086112776514741)
                  ·
                    rfl

theorem cell20_1007503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1007503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007503 prefixEnd_1007503 := by exact prefixLift 1007503
  have htrace : WordTrace (prefixWord ++ tailWord_1007503) baseStart_1007503 baseEnd_1007503 := by
    simpa [prefixWord, tailWord_1007503, baseEnd_1007503] using wordTrace_append hprefix tailTrace_1007503
  have hstable : (prefixWord ++ tailWord_1007503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007503).length < 2 ^ (prefixWord ++ tailWord_1007503).sum := by decide
  have hdescent : baseEnd_1007503 < baseStart_1007503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007575 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 3]
def baseStart_1007575 : Nat := 118140960795 + 1007575 * 2 ^ 59
def prefixEnd_1007575 : Nat := 4983230072969 + 3 ^ 40 * 1007575 * 2
def baseEnd_1007575 : Nat := 459884684848000526114447

theorem tailTrace_1007575 : CollatzResearch.WordTrace tailWord_1007575 prefixEnd_1007575 459884684848000526114447 := by
  unfold tailWord_1007575
  simp only [CollatzResearch.WordTrace]
  refine ⟨36749279324735329955112179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24499519549823553303408119 36749279324735329955112179)
  ·
    refine ⟨55123918987102994932668269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36749279324735329955112179 55123918987102994932668269)
    ·
      refine ⟨20671469620163623099750601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55123918987102994932668269 20671469620163623099750601)
      ·
        refine ⟨15503602215122717324812951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20671469620163623099750601 15503602215122717324812951)
        ·
          refine ⟨23255403322684075987219427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503602215122717324812951 23255403322684075987219427)
          ·
            refine ⟨34883104984026113980829141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255403322684075987219427 34883104984026113980829141)
            ·
              refine ⟨817572773063112046425683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34883104984026113980829141 817572773063112046425683)
              ·
                refine ⟨1226359159594668069638525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817572773063112046425683 1226359159594668069638525)
                ·
                  refine ⟨459884684848000526114447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226359159594668069638525 459884684848000526114447)
                  ·
                    rfl

theorem cell20_1007575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_1007575 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007575 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007575 prefixEnd_1007575 := by exact prefixLift 1007575
  have htrace : WordTrace (prefixWord ++ tailWord_1007575) baseStart_1007575 baseEnd_1007575 := by
    simpa [prefixWord, tailWord_1007575, baseEnd_1007575] using wordTrace_append hprefix tailTrace_1007575
  have hstable : (prefixWord ++ tailWord_1007575).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007575).length < 2 ^ (prefixWord ++ tailWord_1007575).sum := by decide
  have hdescent : baseEnd_1007575 < baseStart_1007575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007606 : List Nat := [5, 1, 1, 1, 4, 2, 6]
def baseStart_1007606 : Nat := 118140960795 + 1007606 * 2 ^ 59
def prefixEnd_1007606 : Nat := 4983230072969 + 3 ^ 40 * 1007606 * 2
def baseEnd_1007606 : Nat := 51099870454744688453443

theorem tailTrace_1007606 : CollatzResearch.WordTrace tailWord_1007606 prefixEnd_1007606 51099870454744688453443 := by
  unfold tailWord_1007606
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296900624226438890593167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24500273325082014832993781 2296900624226438890593167)
  ·
    refine ⟨3445350936339658335889751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296900624226438890593167 3445350936339658335889751)
    ·
      refine ⟨5168026404509487503834627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445350936339658335889751 5168026404509487503834627)
      ·
        refine ⟨7752039606764231255751941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168026404509487503834627 7752039606764231255751941)
        ·
          refine ⟨1453507426268293360453489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7752039606764231255751941 1453507426268293360453489)
          ·
            refine ⟨1090130569701220020340117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453507426268293360453489 1090130569701220020340117)
            ·
              refine ⟨51099870454744688453443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1090130569701220020340117 51099870454744688453443)
              ·
                rfl

theorem cell20_1007606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 6].length) (baseStart_1007606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007606 prefixEnd_1007606 := by exact prefixLift 1007606
  have htrace : WordTrace (prefixWord ++ tailWord_1007606) baseStart_1007606 baseEnd_1007606 := by
    simpa [prefixWord, tailWord_1007606, baseEnd_1007606] using wordTrace_append hprefix tailTrace_1007606
  have hstable : (prefixWord ++ tailWord_1007606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007606).length < 2 ^ (prefixWord ++ tailWord_1007606).sum := by decide
  have hdescent : baseEnd_1007606 < baseStart_1007606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007622 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1007622 : Nat := 118140960795 + 1007622 * 2 ^ 59
def prefixEnd_1007622 : Nat := 4983230072969 + 3 ^ 40 * 1007622 * 2
def baseEnd_1007622 : Nat := 459906136928677251547589

theorem tailTrace_1007622 : CollatzResearch.WordTrace tailWord_1007622 prefixEnd_1007622 459906136928677251547589 := by
  unfold tailWord_1007622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148468548611408030689785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24500662370376704654715413 1148468548611408030689785)
  ·
    refine ⟨861351411458556023017339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1148468548611408030689785 861351411458556023017339)
    ·
      refine ⟨1292027117187834034526009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861351411458556023017339 1292027117187834034526009)
      ·
        refine ⟨969020337890875525894507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292027117187834034526009 969020337890875525894507)
        ·
          refine ⟨1453530506836313288841761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969020337890875525894507 1453530506836313288841761)
          ·
            refine ⟨1090147880127234966631321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453530506836313288841761 1090147880127234966631321)
            ·
              refine ⟨817610910095426224973491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090147880127234966631321 817610910095426224973491)
              ·
                refine ⟨1226416365143139337460237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817610910095426224973491 1226416365143139337460237)
                ·
                  refine ⟨459906136928677251547589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226416365143139337460237 459906136928677251547589)
                  ·
                    rfl

theorem cell20_1007622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1007622 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007622 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007622 prefixEnd_1007622 := by exact prefixLift 1007622
  have htrace : WordTrace (prefixWord ++ tailWord_1007622) baseStart_1007622 baseEnd_1007622 := by
    simpa [prefixWord, tailWord_1007622, baseEnd_1007622] using wordTrace_append hprefix tailTrace_1007622
  have hstable : (prefixWord ++ tailWord_1007622).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007622).length < 2 ^ (prefixWord ++ tailWord_1007622).sum := by decide
  have hdescent : baseEnd_1007622 < baseStart_1007622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007724 : List Nat := [2, 2, 1, 1, 3, 4, 7]
def baseStart_1007724 : Nat := 118140960795 + 1007724 * 2 ^ 59
def prefixEnd_1007724 : Nat := 4983230072969 + 3 ^ 40 * 1007724 * 2
def baseEnd_1007724 : Nat := 51105854723113136683019

theorem tailTrace_1007724 : CollatzResearch.WordTrace tailWord_1007724 prefixEnd_1007724 51105854723113136683019 := by
  unfold tailWord_1007724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18377356900597764201143113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24503142534130352268190817 18377356900597764201143113)
  ·
    refine ⟨13783017675448323150857335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18377356900597764201143113 13783017675448323150857335)
    ·
      refine ⟨20674526513172484726286003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13783017675448323150857335 20674526513172484726286003)
      ·
        refine ⟨31011789769758727089429005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20674526513172484726286003 31011789769758727089429005)
        ·
          refine ⟨11629421163659522658535877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31011789769758727089429005 11629421163659522658535877)
          ·
            refine ⟨2180516468186160498475477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11629421163659522658535877 2180516468186160498475477)
            ·
              refine ⟨51105854723113136683019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2180516468186160498475477 51105854723113136683019)
              ·
                rfl

theorem cell20_1007724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 7].length) (baseStart_1007724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007724 prefixEnd_1007724 := by exact prefixLift 1007724
  have htrace : WordTrace (prefixWord ++ tailWord_1007724) baseStart_1007724 baseEnd_1007724 := by
    simpa [prefixWord, tailWord_1007724, baseEnd_1007724] using wordTrace_append hprefix tailTrace_1007724
  have hstable : (prefixWord ++ tailWord_1007724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007724).length < 2 ^ (prefixWord ++ tailWord_1007724).sum := by decide
  have hdescent : baseEnd_1007724 < baseStart_1007724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007727 : List Nat := [1, 1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_1007727 : Nat := 118140960795 + 1007727 * 2 ^ 59
def prefixEnd_1007727 : Nat := 4983230072969 + 3 ^ 40 * 1007727 * 2
def baseEnd_1007727 : Nat := 459954061789763553047159

theorem tailTrace_1007727 : CollatzResearch.WordTrace tailWord_1007727 prefixEnd_1007727 459954061789763553047159 := by
  unfold tailWord_1007727
  simp only [CollatzResearch.WordTrace]
  refine ⟨36754823220184659914645435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24503215480123106609763623 36754823220184659914645435)
  ·
    refine ⟨55132234830276989871968153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36754823220184659914645435 55132234830276989871968153)
    ·
      refine ⟨41349176122707742403976115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55132234830276989871968153 41349176122707742403976115)
      ·
        refine ⟨62023764184061613605964173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41349176122707742403976115 62023764184061613605964173)
        ·
          refine ⟨23258911569023105102236565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62023764184061613605964173 23258911569023105102236565)
          ·
            refine ⟨1090261479797958051667339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23258911569023105102236565 1090261479797958051667339)
            ·
              refine ⟨1635392219696937077501009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090261479797958051667339 1635392219696937077501009)
              ·
                refine ⟨1226544164772702808125757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635392219696937077501009 1226544164772702808125757)
                ·
                  refine ⟨459954061789763553047159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226544164772702808125757 459954061789763553047159)
                  ·
                    rfl

theorem cell20_1007727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_1007727 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007727 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007727 prefixEnd_1007727 := by exact prefixLift 1007727
  have htrace : WordTrace (prefixWord ++ tailWord_1007727) baseStart_1007727 baseEnd_1007727 := by
    simpa [prefixWord, tailWord_1007727, baseEnd_1007727] using wordTrace_append hprefix tailTrace_1007727
  have hstable : (prefixWord ++ tailWord_1007727).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007727).length < 2 ^ (prefixWord ++ tailWord_1007727).sum := by decide
  have hdescent : baseEnd_1007727 < baseStart_1007727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007734 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1007734 : Nat := 118140960795 + 1007734 * 2 ^ 59
def prefixEnd_1007734 : Nat := 4983230072969 + 3 ^ 40 * 1007734 * 2
def baseEnd_1007734 : Nat := 459957256780502639813797

theorem tailTrace_1007734 : CollatzResearch.WordTrace tailWord_1007734 prefixEnd_1007734 459957256780502639813797 := by
  unfold tailWord_1007734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297192408197456256884391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24503385687439533406766837 2297192408197456256884391)
  ·
    refine ⟨3445788612296184385326587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297192408197456256884391 3445788612296184385326587)
    ·
      refine ⟨5168682918444276577989881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445788612296184385326587 5168682918444276577989881)
      ·
        refine ⟨3876512188833207433492411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5168682918444276577989881 3876512188833207433492411)
        ·
          refine ⟨5814768283249811150238617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3876512188833207433492411 5814768283249811150238617)
          ·
            refine ⟨4361076212437358362678963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5814768283249811150238617 4361076212437358362678963)
            ·
              refine ⟨6541614318656037544018445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4361076212437358362678963 6541614318656037544018445)
              ·
                refine ⟨2453105369496014079006917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6541614318656037544018445 2453105369496014079006917)
                ·
                  refine ⟨459957256780502639813797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453105369496014079006917 459957256780502639813797)
                  ·
                    rfl

theorem cell20_1007734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1007734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007734 prefixEnd_1007734 := by exact prefixLift 1007734
  have htrace : WordTrace (prefixWord ++ tailWord_1007734) baseStart_1007734 baseEnd_1007734 := by
    simpa [prefixWord, tailWord_1007734, baseEnd_1007734] using wordTrace_append hprefix tailTrace_1007734
  have hstable : (prefixWord ++ tailWord_1007734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007734).length < 2 ^ (prefixWord ++ tailWord_1007734).sum := by decide
  have hdescent : baseEnd_1007734 < baseStart_1007734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007764 : List Nat := [2, 4, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1007764 : Nat := 118140960795 + 1007764 * 2 ^ 59
def prefixEnd_1007764 : Nat := 4983230072969 + 3 ^ 40 * 1007764 * 2
def baseEnd_1007764 : Nat := 459970949597955868813675

theorem tailTrace_1007764 : CollatzResearch.WordTrace tailWord_1007764 prefixEnd_1007764 459970949597955868813675 := by
  unfold tailWord_1007764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378086360525307616871173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24504115147367076822494897 18378086360525307616871173)
  ·
    refine ⟨3445891192598495178163345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18378086360525307616871173 3445891192598495178163345)
    ·
      refine ⟨2584418394448871383622509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3445891192598495178163345 2584418394448871383622509)
      ·
        refine ⟨969156897918326768858441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2584418394448871383622509 969156897918326768858441)
        ·
          refine ⟨726867673438745076643831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969156897918326768858441 726867673438745076643831)
          ·
            refine ⟨1090301510158117614965747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726867673438745076643831 1090301510158117614965747)
            ·
              refine ⟨1635452265237176422448621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090301510158117614965747 1635452265237176422448621)
              ·
                refine ⟨613294599463941158418233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635452265237176422448621 613294599463941158418233)
                ·
                  refine ⟨459970949597955868813675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613294599463941158418233 459970949597955868813675)
                  ·
                    rfl

theorem cell20_1007764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1007764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007764 prefixEnd_1007764 := by exact prefixLift 1007764
  have htrace : WordTrace (prefixWord ++ tailWord_1007764) baseStart_1007764 baseEnd_1007764 := by
    simpa [prefixWord, tailWord_1007764, baseEnd_1007764] using wordTrace_append hprefix tailTrace_1007764
  have hstable : (prefixWord ++ tailWord_1007764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007764).length < 2 ^ (prefixWord ++ tailWord_1007764).sum := by decide
  have hdescent : baseEnd_1007764 < baseStart_1007764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007768 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 2]
def baseStart_1007768 : Nat := 118140960795 + 1007768 * 2 ^ 59
def prefixEnd_1007768 : Nat := 4983230072969 + 3 ^ 40 * 1007768 * 2
def baseEnd_1007768 : Nat := 459972775306949632680325

theorem tailTrace_1007768 : CollatzResearch.WordTrace tailWord_1007768 prefixEnd_1007768 459972775306949632680325 := by
  unfold tailWord_1007768
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378159306518061958443979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24504212408690749277925305 18378159306518061958443979)
  ·
    refine ⟨27567238959777092937665969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378159306518061958443979 27567238959777092937665969)
    ·
      refine ⟨20675429219832819703249477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27567238959777092937665969 20675429219832819703249477)
      ·
        refine ⟨3876642978718653694359277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20675429219832819703249477 3876642978718653694359277)
        ·
          refine ⟨1453741117019495135384729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3876642978718653694359277 1453741117019495135384729)
          ·
            refine ⟨1090305837764621351538547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1453741117019495135384729 1090305837764621351538547)
            ·
              refine ⟨1635458756646932027307821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090305837764621351538547 1635458756646932027307821)
              ·
                refine ⟨613297033742599510240433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635458756646932027307821 613297033742599510240433)
                ·
                  refine ⟨459972775306949632680325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613297033742599510240433 459972775306949632680325)
                  ·
                    rfl

theorem cell20_1007768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 2].length) (baseStart_1007768 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007768 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007768 prefixEnd_1007768 := by exact prefixLift 1007768
  have htrace : WordTrace (prefixWord ++ tailWord_1007768) baseStart_1007768 baseEnd_1007768 := by
    simpa [prefixWord, tailWord_1007768, baseEnd_1007768] using wordTrace_append hprefix tailTrace_1007768
  have hstable : (prefixWord ++ tailWord_1007768).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007768).length < 2 ^ (prefixWord ++ tailWord_1007768).sum := by decide
  have hdescent : baseEnd_1007768 < baseStart_1007768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007789 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1007789 : Nat := 118140960795 + 1007789 * 2 ^ 59
def prefixEnd_1007789 : Nat := 4983230072969 + 3 ^ 40 * 1007789 * 2
def baseEnd_1007789 : Nat := 459982360279166892980239

theorem tailTrace_1007789 : CollatzResearch.WordTrace tailWord_1007789 prefixEnd_1007789 459982360279166892980239 := by
  unfold tailWord_1007789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36757084545960044503402421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24504723030640029668934947 36757084545960044503402421)
  ·
    refine ⟨3445976676183754172193977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36757084545960044503402421 3445976676183754172193977)
    ·
      refine ⟨2584482507137815629145483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3445976676183754172193977 2584482507137815629145483)
      ·
        refine ⟨3876723760706723443718225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584482507137815629145483 3876723760706723443718225)
        ·
          refine ⟨2907542820530042582788669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876723760706723443718225 2907542820530042582788669)
          ·
            refine ⟨1090328557698765968545751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2907542820530042582788669 1090328557698765968545751)
            ·
              refine ⟨1635492836548148952818627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090328557698765968545751 1635492836548148952818627)
              ·
                refine ⟨2453239254822223429227941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635492836548148952818627 2453239254822223429227941)
                ·
                  refine ⟨459982360279166892980239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453239254822223429227941 459982360279166892980239)
                  ·
                    rfl

theorem cell20_1007789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1007789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007789 prefixEnd_1007789 := by exact prefixLift 1007789
  have htrace : WordTrace (prefixWord ++ tailWord_1007789) baseStart_1007789 baseEnd_1007789 := by
    simpa [prefixWord, tailWord_1007789, baseEnd_1007789] using wordTrace_append hprefix tailTrace_1007789
  have hstable : (prefixWord ++ tailWord_1007789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007789).length < 2 ^ (prefixWord ++ tailWord_1007789).sum := by decide
  have hdescent : baseEnd_1007789 < baseStart_1007789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007800 : List Nat := [2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1007800 : Nat := 118140960795 + 1007800 * 2 ^ 59
def prefixEnd_1007800 : Nat := 4983230072969 + 3 ^ 40 * 1007800 * 2
def baseEnd_1007800 : Nat := 153329126992966581204509

theorem tailTrace_1007800 : CollatzResearch.WordTrace tailWord_1007800 prefixEnd_1007800 153329126992966581204509 := by
  unfold tailWord_1007800
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378742874460096691026427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24504990499280128921368569 18378742874460096691026427)
  ·
    refine ⟨27568114311690145036539641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378742874460096691026427 27568114311690145036539641)
    ·
      refine ⟨20676085733767608777404731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27568114311690145036539641 20676085733767608777404731)
      ·
        refine ⟨31014128600651413166107097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20676085733767608777404731 31014128600651413166107097)
        ·
          refine ⟨23260596450488559874580323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31014128600651413166107097 23260596450488559874580323)
          ·
            refine ⟨34890894675732839811870485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23260596450488559874580323 34890894675732839811870485)
            ·
              refine ⟨1635510687924976866181429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34890894675732839811870485 1635510687924976866181429)
              ·
                refine ⟨153329126992966581204509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1635510687924976866181429 153329126992966581204509)
                ·
                  rfl

theorem cell20_1007800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1007800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007800 prefixEnd_1007800 := by exact prefixLift 1007800
  have htrace : WordTrace (prefixWord ++ tailWord_1007800) baseStart_1007800 baseEnd_1007800 := by
    simpa [prefixWord, tailWord_1007800, baseEnd_1007800] using wordTrace_append hprefix tailTrace_1007800
  have hstable : (prefixWord ++ tailWord_1007800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007800).length < 2 ^ (prefixWord ++ tailWord_1007800).sum := by decide
  have hdescent : baseEnd_1007800 < baseStart_1007800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007855 : List Nat := [1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_1007855 : Nat := 118140960795 + 1007855 * 2 ^ 59
def prefixEnd_1007855 : Nat := 4983230072969 + 3 ^ 40 * 1007855 * 2
def baseEnd_1007855 : Nat := 153337494825854665593323

theorem tailTrace_1007855 : CollatzResearch.WordTrace tailWord_1007855 prefixEnd_1007855 153337494825854665593323 := by
  unfold tailWord_1007855
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759491763720937775305019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24506327842480625183536679 36759491763720937775305019)
  ·
    refine ⟨55139237645581406662957529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36759491763720937775305019 55139237645581406662957529)
    ·
      refine ⟨41354428234186054997218147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55139237645581406662957529 41354428234186054997218147)
      ·
        refine ⟨62031642351279082495827221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41354428234186054997218147 62031642351279082495827221)
        ·
          refine ⟨2907733235216206991991901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62031642351279082495827221 2907733235216206991991901)
          ·
            refine ⟨1090399963206077621996963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2907733235216206991991901 1090399963206077621996963)
            ·
              refine ⟨1635599944809116432995445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090399963206077621996963 1635599944809116432995445)
              ·
                refine ⟨153337494825854665593323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1635599944809116432995445 153337494825854665593323)
                ·
                  rfl

theorem cell20_1007855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_1007855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007855 prefixEnd_1007855 := by exact prefixLift 1007855
  have htrace : WordTrace (prefixWord ++ tailWord_1007855) baseStart_1007855 baseEnd_1007855 := by
    simpa [prefixWord, tailWord_1007855, baseEnd_1007855] using wordTrace_append hprefix tailTrace_1007855
  have hstable : (prefixWord ++ tailWord_1007855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007855).length < 2 ^ (prefixWord ++ tailWord_1007855).sum := by decide
  have hdescent : baseEnd_1007855 < baseStart_1007855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007883 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 5]
def baseStart_1007883 : Nat := 118140960795 + 1007883 * 2 ^ 59
def prefixEnd_1007883 : Nat := 4983230072969 + 3 ^ 40 * 1007883 * 2
def baseEnd_1007883 : Nat := 460025264440520343846521

theorem tailTrace_1007883 : CollatzResearch.WordTrace tailWord_1007883 prefixEnd_1007883 460025264440520343846521 := by
  unfold tailWord_1007883
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760513007619498557324303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24507008671746332371549535 36760513007619498557324303)
  ·
    refine ⟨55140769511429247835986455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36760513007619498557324303 55140769511429247835986455)
    ·
      refine ⟨82711154267143871753979683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55140769511429247835986455 82711154267143871753979683)
      ·
        refine ⟨124066731400715807630969525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82711154267143871753979683 124066731400715807630969525)
        ·
          refine ⟨11631256068817106965403393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124066731400715807630969525 11631256068817106965403393)
          ·
            refine ⟨8723442051612830224052545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631256068817106965403393 8723442051612830224052545)
            ·
              refine ⟨6542581538709622668039409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8723442051612830224052545 6542581538709622668039409)
              ·
                refine ⟨4906936154032217001029557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6542581538709622668039409 4906936154032217001029557)
                ·
                  refine ⟨460025264440520343846521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4906936154032217001029557 460025264440520343846521)
                  ·
                    rfl

theorem cell20_1007883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 5].length) (baseStart_1007883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007883 prefixEnd_1007883 := by exact prefixLift 1007883
  have htrace : WordTrace (prefixWord ++ tailWord_1007883) baseStart_1007883 baseEnd_1007883 := by
    simpa [prefixWord, tailWord_1007883, baseEnd_1007883] using wordTrace_append hprefix tailTrace_1007883
  have hstable : (prefixWord ++ tailWord_1007883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007883).length < 2 ^ (prefixWord ++ tailWord_1007883).sum := by decide
  have hdescent : baseEnd_1007883 < baseStart_1007883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007907 : List Nat := [1, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_1007907 : Nat := 118140960795 + 1007907 * 2 ^ 59
def prefixEnd_1007907 : Nat := 4983230072969 + 3 ^ 40 * 1007907 * 2
def baseEnd_1007907 : Nat := 460036218694482927046423

theorem tailTrace_1007907 : CollatzResearch.WordTrace tailWord_1007907 prefixEnd_1007907 460036218694482927046423 := by
  unfold tailWord_1007907
  simp only [CollatzResearch.WordTrace]
  refine ⟨36761388359532550656197975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24507592239688367104131983 36761388359532550656197975)
  ·
    refine ⟨55142082539298825984296963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36761388359532550656197975 55142082539298825984296963)
    ·
      refine ⟨82713123808948238976445445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55142082539298825984296963 82713123808948238976445445)
      ·
        refine ⟨15508710714177794808083521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82713123808948238976445445 15508710714177794808083521)
        ·
          refine ⟨11631533035633346106062641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15508710714177794808083521 11631533035633346106062641)
          ·
            refine ⟨8723649776725009579546981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631533035633346106062641 8723649776725009579546981)
            ·
              refine ⟨1635684333135939296165059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8723649776725009579546981 1635684333135939296165059)
              ·
                refine ⟨2453526499703908944247589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635684333135939296165059 2453526499703908944247589)
                ·
                  refine ⟨460036218694482927046423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453526499703908944247589 460036218694482927046423)
                  ·
                    rfl

theorem cell20_1007907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_1007907 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007907 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007907 prefixEnd_1007907 := by exact prefixLift 1007907
  have htrace : WordTrace (prefixWord ++ tailWord_1007907) baseStart_1007907 baseEnd_1007907 := by
    simpa [prefixWord, tailWord_1007907, baseEnd_1007907] using wordTrace_append hprefix tailTrace_1007907
  have hstable : (prefixWord ++ tailWord_1007907).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007907).length < 2 ^ (prefixWord ++ tailWord_1007907).sum := by decide
  have hdescent : baseEnd_1007907 < baseStart_1007907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007924 : List Nat := [2, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_1007924 : Nat := 118140960795 + 1007924 * 2 ^ 59
def prefixEnd_1007924 : Nat := 4983230072969 + 3 ^ 40 * 1007924 * 2
def baseEnd_1007924 : Nat := 460043977957706423479687

theorem tailTrace_1007924 : CollatzResearch.WordTrace tailWord_1007924 prefixEnd_1007924 460043977957706423479687 := by
  unfold tailWord_1007924
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381004200235481279783413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24508005600313975039711217 18381004200235481279783413)
  ·
    refine ⟨1723219143772076369979695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18381004200235481279783413 1723219143772076369979695)
    ·
      refine ⟨2584828715658114554969543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723219143772076369979695 2584828715658114554969543)
      ·
        refine ⟨3877243073487171832454315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584828715658114554969543 3877243073487171832454315)
        ·
          refine ⟨5815864610230757748681473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877243073487171832454315 5815864610230757748681473)
          ·
            refine ⟨4361898457673068311511105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5815864610230757748681473 4361898457673068311511105)
            ·
              refine ⟨3271423843254801233633329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4361898457673068311511105 3271423843254801233633329)
              ·
                refine ⟨2453567882441100925224997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3271423843254801233633329 2453567882441100925224997)
                ·
                  refine ⟨460043977957706423479687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453567882441100925224997 460043977957706423479687)
                  ·
                    rfl

theorem cell20_1007924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_1007924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007924 prefixEnd_1007924 := by exact prefixLift 1007924
  have htrace : WordTrace (prefixWord ++ tailWord_1007924) baseStart_1007924 baseEnd_1007924 := by
    simpa [prefixWord, tailWord_1007924, baseEnd_1007924] using wordTrace_append hprefix tailTrace_1007924
  have hstable : (prefixWord ++ tailWord_1007924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007924).length < 2 ^ (prefixWord ++ tailWord_1007924).sum := by decide
  have hdescent : baseEnd_1007924 < baseStart_1007924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007937 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 2]
def baseStart_1007937 : Nat := 118140960795 + 1007937 * 2 ^ 59
def prefixEnd_1007937 : Nat := 4983230072969 + 3 ^ 40 * 1007937 * 2
def baseEnd_1007937 : Nat := 460049911511936156046301

theorem tailTrace_1007937 : CollatzResearch.WordTrace tailWord_1007937 prefixEnd_1007937 460049911511936156046301 := by
  unfold tailWord_1007937
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762482549423865779790065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24508321699615910519860043 36762482549423865779790065)
  ·
    refine ⟨27571861912067899334842549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36762482549423865779790065 27571861912067899334842549)
    ·
      refine ⟨2584862054256365562641489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27571861912067899334842549 2584862054256365562641489)
      ·
        refine ⟨1938646540692274171981117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2584862054256365562641489 1938646540692274171981117)
        ·
          refine ⟨726992452759602814492919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1938646540692274171981117 726992452759602814492919)
          ·
            refine ⟨1090488679139404221739379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726992452759602814492919 1090488679139404221739379)
            ·
              refine ⟨1635733018709106332609069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090488679139404221739379 1635733018709106332609069)
              ·
                refine ⟨613399882015914874728401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635733018709106332609069 613399882015914874728401)
                ·
                  refine ⟨460049911511936156046301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613399882015914874728401 460049911511936156046301)
                  ·
                    rfl

theorem cell20_1007937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 2].length) (baseStart_1007937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007937 prefixEnd_1007937 := by exact prefixLift 1007937
  have htrace : WordTrace (prefixWord ++ tailWord_1007937) baseStart_1007937 baseEnd_1007937 := by
    simpa [prefixWord, tailWord_1007937, baseEnd_1007937] using wordTrace_append hprefix tailTrace_1007937
  have hstable : (prefixWord ++ tailWord_1007937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007937).length < 2 ^ (prefixWord ++ tailWord_1007937).sum := by decide
  have hdescent : baseEnd_1007937 < baseStart_1007937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007952 : List Nat := [2, 1, 1, 1, 1, 8, 6]
def baseStart_1007952 : Nat := 118140960795 + 1007952 * 2 ^ 59
def prefixEnd_1007952 : Nat := 4983230072969 + 3 ^ 40 * 1007952 * 2
def baseEnd_1007952 : Nat := 51117417546740307838471

theorem tailTrace_1007952 : CollatzResearch.WordTrace tailWord_1007952 prefixEnd_1007952 51117417546740307838471 := by
  unfold tailWord_1007952
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381514822184761670793055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24508686429579682227724073 18381514822184761670793055)
  ·
    refine ⟨27572272233277142506189583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381514822184761670793055 27572272233277142506189583)
    ·
      refine ⟨41358408349915713759284375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27572272233277142506189583 41358408349915713759284375)
      ·
        refine ⟨62037612524873570638926563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41358408349915713759284375 62037612524873570638926563)
        ·
          refine ⟨93056418787310355958389845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62037612524873570638926563 93056418787310355958389845)
          ·
            refine ⟨1090504907663793233887381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 93056418787310355958389845 1090504907663793233887381)
            ·
              refine ⟨51117417546740307838471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1090504907663793233887381 51117417546740307838471)
              ·
                rfl

theorem cell20_1007952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_1007952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007952 prefixEnd_1007952 := by exact prefixLift 1007952
  have htrace : WordTrace (prefixWord ++ tailWord_1007952) baseStart_1007952 baseEnd_1007952 := by
    simpa [prefixWord, tailWord_1007952, baseEnd_1007952] using wordTrace_append hprefix tailTrace_1007952
  have hstable : (prefixWord ++ tailWord_1007952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007952).length < 2 ^ (prefixWord ++ tailWord_1007952).sum := by decide
  have hdescent : baseEnd_1007952 < baseStart_1007952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1007959 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_1007959 : Nat := 118140960795 + 1007959 * 2 ^ 59
def prefixEnd_1007959 : Nat := 4983230072969 + 3 ^ 40 * 1007959 * 2
def baseEnd_1007959 : Nat := 460059952911401857312877

theorem tailTrace_1007959 : CollatzResearch.WordTrace tailWord_1007959 prefixEnd_1007959 460059952911401857312877 := by
  unfold tailWord_1007959
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763284955344163537090931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24508856636896109024727287 36763284955344163537090931)
  ·
    refine ⟨55144927433016245305636397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763284955344163537090931 55144927433016245305636397)
    ·
      refine ⟨20679347787381091989613649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55144927433016245305636397 20679347787381091989613649)
      ·
        refine ⟨15509510840535818992210237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20679347787381091989613649 15509510840535818992210237)
        ·
          refine ⟨5816066565200932122078839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15509510840535818992210237 5816066565200932122078839)
          ·
            refine ⟨8724099847801398183118259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816066565200932122078839 8724099847801398183118259)
            ·
              refine ⟨13086149771702097274677389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724099847801398183118259 13086149771702097274677389)
              ·
                refine ⟨4907306164388286478004021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13086149771702097274677389 4907306164388286478004021)
                ·
                  refine ⟨460059952911401857312877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907306164388286478004021 460059952911401857312877)
                  ·
                    rfl

theorem cell20_1007959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_1007959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1007959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1007959 prefixEnd_1007959 := by exact prefixLift 1007959
  have htrace : WordTrace (prefixWord ++ tailWord_1007959) baseStart_1007959 baseEnd_1007959 := by
    simpa [prefixWord, tailWord_1007959, baseEnd_1007959] using wordTrace_append hprefix tailTrace_1007959
  have hstable : (prefixWord ++ tailWord_1007959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1007959).length < 2 ^ (prefixWord ++ tailWord_1007959).sum := by decide
  have hdescent : baseEnd_1007959 < baseStart_1007959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1007959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008010 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_1008010 : Nat := 118140960795 + 1008010 * 2 ^ 59
def prefixEnd_1008010 : Nat := 4983230072969 + 3 ^ 40 * 1008010 * 2
def baseEnd_1008010 : Nat := 460083230701072346612669

theorem tailTrace_1008010 : CollatzResearch.WordTrace tailWord_1008010 prefixEnd_1008010 460083230701072346612669 := by
  unfold tailWord_1008010
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191286269539849811799371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24510096718772932831464989 9191286269539849811799371)
  ·
    refine ⟨13786929404309774717699057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9191286269539849811799371 13786929404309774717699057)
    ·
      refine ⟨10340197053232331038274293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13786929404309774717699057 10340197053232331038274293)
      ·
        refine ⟨969393473740531034838215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10340197053232331038274293 969393473740531034838215)
        ·
          refine ⟨1454090210610796552257323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969393473740531034838215 1454090210610796552257323)
          ·
            refine ⟨2181135315916194828385985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454090210610796552257323 2181135315916194828385985)
            ·
              refine ⟨1635851486937146121289489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181135315916194828385985 1635851486937146121289489)
              ·
                refine ⟨1226888615202859590967117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1635851486937146121289489 1226888615202859590967117)
                ·
                  refine ⟨460083230701072346612669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226888615202859590967117 460083230701072346612669)
                  ·
                    rfl

theorem cell20_1008010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_1008010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008010 prefixEnd_1008010 := by exact prefixLift 1008010
  have htrace : WordTrace (prefixWord ++ tailWord_1008010) baseStart_1008010 baseEnd_1008010 := by
    simpa [prefixWord, tailWord_1008010, baseEnd_1008010] using wordTrace_append hprefix tailTrace_1008010
  have hstable : (prefixWord ++ tailWord_1008010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008010).length < 2 ^ (prefixWord ++ tailWord_1008010).sum := by decide
  have hdescent : baseEnd_1008010 < baseStart_1008010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008011 : List Nat := [1, 1, 1, 1, 4, 12]
def baseStart_1008011 : Nat := 118140960795 + 1008011 * 2 ^ 59
def prefixEnd_1008011 : Nat := 4983230072969 + 3 ^ 40 * 1008011 * 2
def baseEnd_1008011 : Nat := 17040136560308177317753

theorem tailTrace_1008011 : CollatzResearch.WordTrace tailWord_1008011 prefixEnd_1008011 17040136560308177317753 := by
  unfold tailWord_1008011
  simp only [CollatzResearch.WordTrace]
  refine ⟨36765181551155776417983887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24510121034103850945322591 36765181551155776417983887)
  ·
    refine ⟨55147772326733664626975831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36765181551155776417983887 55147772326733664626975831)
    ·
      refine ⟨82721658490100496940463747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55147772326733664626975831 82721658490100496940463747)
      ·
        refine ⟨124082487735150745410695621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82721658490100496940463747 124082487735150745410695621)
        ·
          refine ⟨23265466450340764764505429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124082487735150745410695621 23265466450340764764505429)
          ·
            refine ⟨17040136560308177317753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23265466450340764764505429 17040136560308177317753)
            ·
              rfl

theorem cell20_1008011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 12].length) (baseStart_1008011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008011 prefixEnd_1008011 := by exact prefixLift 1008011
  have htrace : WordTrace (prefixWord ++ tailWord_1008011) baseStart_1008011 baseEnd_1008011 := by
    simpa [prefixWord, tailWord_1008011, baseEnd_1008011] using wordTrace_append hprefix tailTrace_1008011
  have hstable : (prefixWord ++ tailWord_1008011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008011).length < 2 ^ (prefixWord ++ tailWord_1008011).sum := by decide
  have hdescent : baseEnd_1008011 < baseStart_1008011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008076 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1008076 : Nat := 118140960795 + 1008076 * 2 ^ 59
def prefixEnd_1008076 : Nat := 4983230072969 + 3 ^ 40 * 1008076 * 2
def baseEnd_1008076 : Nat := 460113354899469450412399

theorem tailTrace_1008076 : CollatzResearch.WordTrace tailWord_1008076 prefixEnd_1008076 460113354899469450412399 := by
  unfold tailWord_1008076
  simp only [CollatzResearch.WordTrace]
  refine ⟨18383776147960146259550041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24511701530613528346066721 18383776147960146259550041)
  ·
    refine ⟨13787832110970109694662531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18383776147960146259550041 13787832110970109694662531)
    ·
      refine ⟨20681748166455164541993797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787832110970109694662531 20681748166455164541993797)
      ·
        refine ⟨3877827781210343351623837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20681748166455164541993797 3877827781210343351623837)
        ·
          refine ⟨1454185417953878756858939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3877827781210343351623837 1454185417953878756858939)
          ·
            refine ⟨2181278126930818135288409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454185417953878756858939 2181278126930818135288409)
            ·
              refine ⟨1635958595198113601466307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181278126930818135288409 1635958595198113601466307)
              ·
                refine ⟨2453937892797170402199461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635958595198113601466307 2453937892797170402199461)
                ·
                  refine ⟨460113354899469450412399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2453937892797170402199461 460113354899469450412399)
                  ·
                    rfl

theorem cell20_1008076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1008076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008076 prefixEnd_1008076 := by exact prefixLift 1008076
  have htrace : WordTrace (prefixWord ++ tailWord_1008076) baseStart_1008076 baseEnd_1008076 := by
    simpa [prefixWord, tailWord_1008076, baseEnd_1008076] using wordTrace_append hprefix tailTrace_1008076
  have hstable : (prefixWord ++ tailWord_1008076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008076).length < 2 ^ (prefixWord ++ tailWord_1008076).sum := by decide
  have hdescent : baseEnd_1008076 < baseStart_1008076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008086 : List Nat := [5, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1008086 : Nat := 118140960795 + 1008086 * 2 ^ 59
def prefixEnd_1008086 : Nat := 4983230072969 + 3 ^ 40 * 1008086 * 2
def baseEnd_1008086 : Nat := 460117919171953860079025

theorem tailTrace_1008086 : CollatzResearch.WordTrace tailWord_1008086 prefixEnd_1008086 460117919171953860079025 := by
  unfold tailWord_1008086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297994814117754014185257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24511944683922709484642741 2297994814117754014185257)
  ·
    refine ⟨1723496110588315510638943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2297994814117754014185257 1723496110588315510638943)
    ·
      refine ⟨2585244165882473265958415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723496110588315510638943 2585244165882473265958415)
      ·
        refine ⟨3877866248823709898937623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2585244165882473265958415 3877866248823709898937623)
        ·
          refine ⟨5816799373235564848406435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877866248823709898937623 5816799373235564848406435)
          ·
            refine ⟨8725199059853347272609653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816799373235564848406435 8725199059853347272609653)
            ·
              refine ⟨817987411861251306807155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8725199059853347272609653 817987411861251306807155)
              ·
                refine ⟨1226981117791876960210733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817987411861251306807155 1226981117791876960210733)
                ·
                  refine ⟨460117919171953860079025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1226981117791876960210733 460117919171953860079025)
                  ·
                    rfl

theorem cell20_1008086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1008086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008086 prefixEnd_1008086 := by exact prefixLift 1008086
  have htrace : WordTrace (prefixWord ++ tailWord_1008086) baseStart_1008086 baseEnd_1008086 := by
    simpa [prefixWord, tailWord_1008086, baseEnd_1008086] using wordTrace_append hprefix tailTrace_1008086
  have hstable : (prefixWord ++ tailWord_1008086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008086).length < 2 ^ (prefixWord ++ tailWord_1008086).sum := by decide
  have hdescent : baseEnd_1008086 < baseStart_1008086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008104 : List Nat := [2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_1008104 : Nat := 118140960795 + 1008104 * 2 ^ 59
def prefixEnd_1008104 : Nat := 4983230072969 + 3 ^ 40 * 1008104 * 2
def baseEnd_1008104 : Nat := 153375378287475265826317

theorem tailTrace_1008104 : CollatzResearch.WordTrace tailWord_1008104 prefixEnd_1008104 153375378287475265826317 := by
  unfold tailWord_1008104
  simp only [CollatzResearch.WordTrace]
  refine ⟨18384286769909426650559683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24512382359879235534079577 18384286769909426650559683)
  ·
    refine ⟨27576430154864139975839525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18384286769909426650559683 27576430154864139975839525)
    ·
      refine ⟨5170580654037026245469911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27576430154864139975839525 5170580654037026245469911)
      ·
        refine ⟨7755870981055539368204867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170580654037026245469911 7755870981055539368204867)
        ·
          refine ⟨11633806471583309052307301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755870981055539368204867 11633806471583309052307301)
          ·
            refine ⟨2181338713421870447307619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11633806471583309052307301 2181338713421870447307619)
            ·
              refine ⟨3272008070132805670961429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181338713421870447307619 3272008070132805670961429)
              ·
                refine ⟨153375378287475265826317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3272008070132805670961429 153375378287475265826317)
                ·
                  rfl

theorem cell20_1008104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_1008104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008104 prefixEnd_1008104 := by exact prefixLift 1008104
  have htrace : WordTrace (prefixWord ++ tailWord_1008104) baseStart_1008104 baseEnd_1008104 := by
    simpa [prefixWord, tailWord_1008104, baseEnd_1008104] using wordTrace_append hprefix tailTrace_1008104
  have hstable : (prefixWord ++ tailWord_1008104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008104).length < 2 ^ (prefixWord ++ tailWord_1008104).sum := by decide
  have hdescent : baseEnd_1008104 < baseStart_1008104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008141 : List Nat := [1, 7, 1, 1, 1, 1, 4, 1, 3]
def baseStart_1008141 : Nat := 118140960795 + 1008141 * 2 ^ 59
def prefixEnd_1008141 : Nat := 4983230072969 + 3 ^ 40 * 1008141 * 2
def baseEnd_1008141 : Nat := 460143022670618113245467

theorem tailTrace_1008141 : CollatzResearch.WordTrace tailWord_1008141 prefixEnd_1008141 460143022670618113245467 := by
  unfold tailWord_1008141
  simp only [CollatzResearch.WordTrace]
  refine ⟨36769923040684808620216277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24513282027123205746810851 36769923040684808620216277)
  ·
    refine ⟨861795071266050202036319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 36769923040684808620216277 861795071266050202036319)
    ·
      refine ⟨1292692606899075303054479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 861795071266050202036319 1292692606899075303054479)
      ·
        refine ⟨1939038910348612954581719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292692606899075303054479 1939038910348612954581719)
        ·
          refine ⟨2908558365522919431872579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939038910348612954581719 2908558365522919431872579)
          ·
            refine ⟨4362837548284379147808869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908558365522919431872579 4362837548284379147808869)
            ·
              refine ⟨818032040303321090214163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4362837548284379147808869 818032040303321090214163)
              ·
                refine ⟨1227048060454981635321245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818032040303321090214163 1227048060454981635321245)
                ·
                  refine ⟨460143022670618113245467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227048060454981635321245 460143022670618113245467)
                  ·
                    rfl

theorem cell20_1008141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_1008141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008141 prefixEnd_1008141 := by exact prefixLift 1008141
  have htrace : WordTrace (prefixWord ++ tailWord_1008141) baseStart_1008141 baseEnd_1008141 := by
    simpa [prefixWord, tailWord_1008141, baseEnd_1008141] using wordTrace_append hprefix tailTrace_1008141
  have hstable : (prefixWord ++ tailWord_1008141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008141).length < 2 ^ (prefixWord ++ tailWord_1008141).sum := by decide
  have hdescent : baseEnd_1008141 < baseStart_1008141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008142 : List Nat := [4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1008142 : Nat := 118140960795 + 1008142 * 2 ^ 59
def prefixEnd_1008142 : Nat := 4983230072969 + 3 ^ 40 * 1008142 * 2
def baseEnd_1008142 : Nat := 153381159699288851404043

theorem tailTrace_1008142 : CollatzResearch.WordTrace tailWord_1008142 prefixEnd_1008142 153381159699288851404043 := by
  unfold tailWord_1008142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4596244939210148223875335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24513306342454123860668453 4596244939210148223875335)
  ·
    refine ⟨6894367408815222335813003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4596244939210148223875335 6894367408815222335813003)
    ·
      refine ⟨10341551113222833503719505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894367408815222335813003 10341551113222833503719505)
      ·
        refine ⟨7756163334917125127789629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10341551113222833503719505 7756163334917125127789629)
        ·
          refine ⟨2908561250593921922921111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7756163334917125127789629 2908561250593921922921111)
          ·
            refine ⟨4362841875890882884381667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2908561250593921922921111 4362841875890882884381667)
            ·
              refine ⟨6544262813836324326572501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4362841875890882884381667 6544262813836324326572501)
              ·
                refine ⟨153381159699288851404043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6544262813836324326572501 153381159699288851404043)
                ·
                  rfl

theorem cell20_1008142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1008142 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008142 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008142 prefixEnd_1008142 := by exact prefixLift 1008142
  have htrace : WordTrace (prefixWord ++ tailWord_1008142) baseStart_1008142 baseEnd_1008142 := by
    simpa [prefixWord, tailWord_1008142, baseEnd_1008142] using wordTrace_append hprefix tailTrace_1008142
  have hstable : (prefixWord ++ tailWord_1008142).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008142).length < 2 ^ (prefixWord ++ tailWord_1008142).sum := by decide
  have hdescent : baseEnd_1008142 < baseStart_1008142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008228 : List Nat := [2, 3, 1, 1, 2, 2, 4, 3, 2]
def baseStart_1008228 : Nat := 118140960795 + 1008228 * 2 ^ 59
def prefixEnd_1008228 : Nat := 4983230072969 + 3 ^ 40 * 1008228 * 2
def baseEnd_1008228 : Nat := 460182731841232477345111

theorem tailTrace_1008228 : CollatzResearch.WordTrace tailWord_1008228 prefixEnd_1008228 460182731841232477345111 := by
  unfold tailWord_1008228
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386548095684811239316669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24515397460913081652422225 18386548095684811239316669)
  ·
    refine ⟨6894955535881804214743751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18386548095684811239316669 6894955535881804214743751)
    ·
      refine ⟨10342433303822706322115627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6894955535881804214743751 10342433303822706322115627)
      ·
        refine ⟨15513649955734059483173441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10342433303822706322115627 15513649955734059483173441)
        ·
          refine ⟨11635237466800544612380081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15513649955734059483173441 11635237466800544612380081)
          ·
            refine ⟨8726428100100408459285061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11635237466800544612380081 8726428100100408459285061)
            ·
              refine ⟨1636205268768826586115949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8726428100100408459285061 1636205268768826586115949)
              ·
                refine ⟨613576975788309969793481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1636205268768826586115949 613576975788309969793481)
                ·
                  refine ⟨460182731841232477345111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613576975788309969793481 460182731841232477345111)
                  ·
                    rfl

theorem cell20_1008228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_1008228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008228 prefixEnd_1008228 := by exact prefixLift 1008228
  have htrace : WordTrace (prefixWord ++ tailWord_1008228) baseStart_1008228 baseEnd_1008228 := by
    simpa [prefixWord, tailWord_1008228, baseEnd_1008228] using wordTrace_append hprefix tailTrace_1008228
  have hstable : (prefixWord ++ tailWord_1008228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008228).length < 2 ^ (prefixWord ++ tailWord_1008228).sum := by decide
  have hdescent : baseEnd_1008228 < baseStart_1008228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008242 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1008242 : Nat := 118140960795 + 1008242 * 2 ^ 59
def prefixEnd_1008242 : Nat := 4983230072969 + 3 ^ 40 * 1008242 * 2
def baseEnd_1008242 : Nat := 460189121822710650878387

theorem tailTrace_1008242 : CollatzResearch.WordTrace tailWord_1008242 prefixEnd_1008242 460189121822710650878387 := by
  unfold tailWord_1008242
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193401703329725717410745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24515737875545935246428653 9193401703329725717410745)
  ·
    refine ⟨6895051277497294288058059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9193401703329725717410745 6895051277497294288058059)
    ·
      refine ⟨10342576916245941432087089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895051277497294288058059 10342576916245941432087089)
      ·
        refine ⟨7756932687184456074065317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10342576916245941432087089 7756932687184456074065317)
        ·
          refine ⟨1454424878847085513887247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7756932687184456074065317 1454424878847085513887247)
          ·
            refine ⟨2181637318270628270830871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454424878847085513887247 2181637318270628270830871)
            ·
              refine ⟨3272455977405942406246307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181637318270628270830871 3272455977405942406246307)
              ·
                refine ⟨4908683966108913609369461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272455977405942406246307 4908683966108913609369461)
                ·
                  refine ⟨460189121822710650878387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908683966108913609369461 460189121822710650878387)
                  ·
                    rfl

theorem cell20_1008242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1008242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008242 prefixEnd_1008242 := by exact prefixLift 1008242
  have htrace : WordTrace (prefixWord ++ tailWord_1008242) baseStart_1008242 baseEnd_1008242 := by
    simpa [prefixWord, tailWord_1008242, baseEnd_1008242] using wordTrace_append hprefix tailTrace_1008242
  have hstable : (prefixWord ++ tailWord_1008242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008242).length < 2 ^ (prefixWord ++ tailWord_1008242).sum := by decide
  have hdescent : baseEnd_1008242 < baseStart_1008242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008249 : List Nat := [1, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_1008249 : Nat := 118140960795 + 1008249 * 2 ^ 59
def prefixEnd_1008249 : Nat := 4983230072969 + 3 ^ 40 * 1008249 * 2
def baseEnd_1008249 : Nat := 460192316813449737645025

theorem tailTrace_1008249 : CollatzResearch.WordTrace tailWord_1008249 prefixEnd_1008249 460192316813449737645025 := by
  unfold tailWord_1008249
  simp only [CollatzResearch.WordTrace]
  refine ⟨36773862124293543065147801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24515908082862362043431867 36773862124293543065147801)
  ·
    refine ⟨27580396593220157298860851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36773862124293543065147801 27580396593220157298860851)
    ·
      refine ⟨41370594889830235948291277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27580396593220157298860851 41370594889830235948291277)
      ·
        refine ⟨15513973083686338480609229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41370594889830235948291277 15513973083686338480609229)
        ·
          refine ⟨5817739906382376930228461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15513973083686338480609229 5817739906382376930228461)
          ·
            refine ⟨2181652464893391348835673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5817739906382376930228461 2181652464893391348835673)
            ·
              refine ⟨1636239348670043511626755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181652464893391348835673 1636239348670043511626755)
              ·
                refine ⟨2454359023005065267440133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636239348670043511626755 2454359023005065267440133)
                ·
                  refine ⟨460192316813449737645025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454359023005065267440133 460192316813449737645025)
                  ·
                    rfl

theorem cell20_1008249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_1008249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008249 prefixEnd_1008249 := by exact prefixLift 1008249
  have htrace : WordTrace (prefixWord ++ tailWord_1008249) baseStart_1008249 baseEnd_1008249 := by
    simpa [prefixWord, tailWord_1008249, baseEnd_1008249] using wordTrace_append hprefix tailTrace_1008249
  have hstable : (prefixWord ++ tailWord_1008249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008249).length < 2 ^ (prefixWord ++ tailWord_1008249).sum := by decide
  have hdescent : baseEnd_1008249 < baseStart_1008249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008310 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_1008310 : Nat := 118140960795 + 1008310 * 2 ^ 59
def prefixEnd_1008310 : Nat := 4983230072969 + 3 ^ 40 * 1008310 * 2
def baseEnd_1008310 : Nat := 460220158875604636611443

theorem tailTrace_1008310 : CollatzResearch.WordTrace tailWord_1008310 prefixEnd_1008310 460220158875604636611443 := by
  unfold tailWord_1008310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298505436067034405194899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24517391318048366988745589 2298505436067034405194899)
  ·
    refine ⟨3447758154100551607792349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2298505436067034405194899 3447758154100551607792349)
    ·
      refine ⟨1292909307787706852922131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3447758154100551607792349 1292909307787706852922131)
      ·
        refine ⟨1939363961681560279383197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292909307787706852922131 1939363961681560279383197)
        ·
          refine ⟨727261485630585104768699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1939363961681560279383197 727261485630585104768699)
          ·
            refine ⟨1090892228445877657153049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727261485630585104768699 1090892228445877657153049)
            ·
              refine ⟨818169171334408242864787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090892228445877657153049 818169171334408242864787)
              ·
                refine ⟨1227253757001612364297181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818169171334408242864787 1227253757001612364297181)
                ·
                  refine ⟨460220158875604636611443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227253757001612364297181 460220158875604636611443)
                  ·
                    rfl

theorem cell20_1008310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_1008310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008310 prefixEnd_1008310 := by exact prefixLift 1008310
  have htrace : WordTrace (prefixWord ++ tailWord_1008310) baseStart_1008310 baseEnd_1008310 := by
    simpa [prefixWord, tailWord_1008310, baseEnd_1008310] using wordTrace_append hprefix tailTrace_1008310
  have hstable : (prefixWord ++ tailWord_1008310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008310).length < 2 ^ (prefixWord ++ tailWord_1008310).sum := by decide
  have hdescent : baseEnd_1008310 < baseStart_1008310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008318 : List Nat := [4, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1008318 : Nat := 118140960795 + 1008318 * 2 ^ 59
def prefixEnd_1008318 : Nat := 4983230072969 + 3 ^ 40 * 1008318 * 2
def baseEnd_1008318 : Nat := 460223810293592164344743

theorem tailTrace_1008318 : CollatzResearch.WordTrace tailWord_1008318 prefixEnd_1008318 460223810293592164344743 := by
  unfold tailWord_1008318
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597047345130445981176201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24517585840695711899606405 4597047345130445981176201)
  ·
    refine ⟨3447785508847834485882151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4597047345130445981176201 3447785508847834485882151)
    ·
      refine ⟨5171678263271751728823227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3447785508847834485882151 5171678263271751728823227)
      ·
        refine ⟨7757517394907627593234841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171678263271751728823227 7757517394907627593234841)
        ·
          refine ⟨5818138046180720694926131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7757517394907627593234841 5818138046180720694926131)
          ·
            refine ⟨8727207069271081042389197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5818138046180720694926131 8727207069271081042389197)
            ·
              refine ⟨3272702650976655390895949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8727207069271081042389197 3272702650976655390895949)
              ·
                refine ⟨1227263494116245771585981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3272702650976655390895949 1227263494116245771585981)
                ·
                  refine ⟨460223810293592164344743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227263494116245771585981 460223810293592164344743)
                  ·
                    rfl

theorem cell20_1008318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1008318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008318 prefixEnd_1008318 := by exact prefixLift 1008318
  have htrace : WordTrace (prefixWord ++ tailWord_1008318) baseStart_1008318 baseEnd_1008318 := by
    simpa [prefixWord, tailWord_1008318, baseEnd_1008318] using wordTrace_append hprefix tailTrace_1008318
  have hstable : (prefixWord ++ tailWord_1008318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008318).length < 2 ^ (prefixWord ++ tailWord_1008318).sum := by decide
  have hdescent : baseEnd_1008318 < baseStart_1008318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008332 : List Nat := [2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_1008332 : Nat := 118140960795 + 1008332 * 2 ^ 59
def prefixEnd_1008332 : Nat := 4983230072969 + 3 ^ 40 * 1008332 * 2
def baseEnd_1008332 : Nat := 153410066758356779292673

theorem tailTrace_1008332 : CollatzResearch.WordTrace tailWord_1008332 prefixEnd_1008332 153410066758356779292673 := by
  unfold tailWord_1008332
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388444691496424120209625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24517926255328565493612833 18388444691496424120209625)
  ·
    refine ⟨13791333518622318090157219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18388444691496424120209625 13791333518622318090157219)
    ·
      refine ⟨20687000277933477135235829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13791333518622318090157219 20687000277933477135235829)
      ·
        refine ⟨1939406276056263481428359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20687000277933477135235829 1939406276056263481428359)
        ·
          refine ⟨2909109414084395222142539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939406276056263481428359 2909109414084395222142539)
          ·
            refine ⟨4363664121126592833213809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909109414084395222142539 4363664121126592833213809)
            ·
              refine ⟨3272748090844944624910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363664121126592833213809 3272748090844944624910357)
              ·
                refine ⟨153410066758356779292673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3272748090844944624910357 153410066758356779292673)
                ·
                  rfl

theorem cell20_1008332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_1008332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008332 prefixEnd_1008332 := by exact prefixLift 1008332
  have htrace : WordTrace (prefixWord ++ tailWord_1008332) baseStart_1008332 baseEnd_1008332 := by
    simpa [prefixWord, tailWord_1008332, baseEnd_1008332] using wordTrace_append hprefix tailTrace_1008332
  have hstable : (prefixWord ++ tailWord_1008332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008332).length < 2 ^ (prefixWord ++ tailWord_1008332).sum := by decide
  have hdescent : baseEnd_1008332 < baseStart_1008332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008353 : List Nat := [1, 2, 3, 1, 4, 9]
def baseStart_1008353 : Nat := 118140960795 + 1008353 * 2 ^ 59
def prefixEnd_1008353 : Nat := 4983230072969 + 3 ^ 40 * 1008353 * 2
def baseEnd_1008353 : Nat := 17045917972121762895479

theorem tailTrace_1008353 : CollatzResearch.WordTrace tailWord_1008353 prefixEnd_1008353 17045917972121762895479 := by
  unfold tailWord_1008353
  simp only [CollatzResearch.WordTrace]
  refine ⟨36777655315916768826933713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24518436877277845884622475 36777655315916768826933713)
  ·
    refine ⟨27583241486937576620200285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36777655315916768826933713 27583241486937576620200285)
    ·
      refine ⟨10343715557601591232575107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27583241486937576620200285 10343715557601591232575107)
      ·
        refine ⟨15515573336402386848862661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343715557601591232575107 15515573336402386848862661)
        ·
          refine ⟨2909170000575447534161749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15515573336402386848862661 2909170000575447534161749)
          ·
            refine ⟨17045917972121762895479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2909170000575447534161749 17045917972121762895479)
            ·
              rfl

theorem cell20_1008353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 9].length) (baseStart_1008353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008353 prefixEnd_1008353 := by exact prefixLift 1008353
  have htrace : WordTrace (prefixWord ++ tailWord_1008353) baseStart_1008353 baseEnd_1008353 := by
    simpa [prefixWord, tailWord_1008353, baseEnd_1008353] using wordTrace_append hprefix tailTrace_1008353
  have hstable : (prefixWord ++ tailWord_1008353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008353).length < 2 ^ (prefixWord ++ tailWord_1008353).sum := by decide
  have hdescent : baseEnd_1008353 < baseStart_1008353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008356 : List Nat := [2, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_1008356 : Nat := 118140960795 + 1008356 * 2 ^ 59
def prefixEnd_1008356 : Nat := 4983230072969 + 3 ^ 40 * 1008356 * 2
def baseEnd_1008356 : Nat := 460241154529032921077921

theorem tailTrace_1008356 : CollatzResearch.WordTrace tailWord_1008356 prefixEnd_1008356 460241154529032921077921 := by
  unfold tailWord_1008356
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388882367452950169646461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24518509823270600226195281 18388882367452950169646461)
  ·
    refine ⟨6895830887794856313617423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18388882367452950169646461 6895830887794856313617423)
    ·
      refine ⟨10343746331692284470426135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895830887794856313617423 10343746331692284470426135)
      ·
        refine ⟨15515619497538426705639203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10343746331692284470426135 15515619497538426705639203)
        ·
          refine ⟨23273429246307640058458805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15515619497538426705639203 23273429246307640058458805)
          ·
            refine ⟨2181883991841341255480513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23273429246307640058458805 2181883991841341255480513)
            ·
              refine ⟨1636412993881005941610385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2181883991841341255480513 1636412993881005941610385)
              ·
                refine ⟨1227309745410754456207789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636412993881005941610385 1227309745410754456207789)
                ·
                  refine ⟨460241154529032921077921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227309745410754456207789 460241154529032921077921)
                  ·
                    rfl

theorem cell20_1008356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_1008356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008356 prefixEnd_1008356 := by exact prefixLift 1008356
  have htrace : WordTrace (prefixWord ++ tailWord_1008356) baseStart_1008356 baseEnd_1008356 := by
    simpa [prefixWord, tailWord_1008356, baseEnd_1008356] using wordTrace_append hprefix tailTrace_1008356
  have hstable : (prefixWord ++ tailWord_1008356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008356).length < 2 ^ (prefixWord ++ tailWord_1008356).sum := by decide
  have hdescent : baseEnd_1008356 < baseStart_1008356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008370 : List Nat := [3, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1008370 : Nat := 118140960795 + 1008370 * 2 ^ 59
def prefixEnd_1008370 : Nat := 4983230072969 + 3 ^ 40 * 1008370 * 2
def baseEnd_1008370 : Nat := 153415848170170364870399

theorem tailTrace_1008370 : CollatzResearch.WordTrace tailWord_1008370 prefixEnd_1008370 153415848170170364870399 := by
  unfold tailWord_1008370
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194568839213795182575641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24518850237903453820201709 9194568839213795182575641)
  ·
    refine ⟨6895926629410346386931731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9194568839213795182575641 6895926629410346386931731)
    ·
      refine ⟨10343889944115519580397597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6895926629410346386931731 10343889944115519580397597)
      ·
        refine ⟨3878958729043319842649099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10343889944115519580397597 3878958729043319842649099)
        ·
          refine ⟨5818438093564979763973649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3878958729043319842649099 5818438093564979763973649)
          ·
            refine ⟨4363828570173734822980237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5818438093564979763973649 4363828570173734822980237)
            ·
              refine ⟨1636435713815150558617589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4363828570173734822980237 1636435713815150558617589)
              ·
                refine ⟨153415848170170364870399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1636435713815150558617589 153415848170170364870399)
                ·
                  rfl

theorem cell20_1008370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1008370 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008370 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008370 prefixEnd_1008370 := by exact prefixLift 1008370
  have htrace : WordTrace (prefixWord ++ tailWord_1008370) baseStart_1008370 baseEnd_1008370 := by
    simpa [prefixWord, tailWord_1008370, baseEnd_1008370] using wordTrace_append hprefix tailTrace_1008370
  have hstable : (prefixWord ++ tailWord_1008370).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008370).length < 2 ^ (prefixWord ++ tailWord_1008370).sum := by decide
  have hdescent : baseEnd_1008370 < baseStart_1008370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008401 : List Nat := [1, 2, 2, 1, 1, 3, 3, 5, 2]
def baseStart_1008401 : Nat := 118140960795 + 1008401 * 2 ^ 59
def prefixEnd_1008401 : Nat := 4983230072969 + 3 ^ 40 * 1008401 * 2
def baseEnd_1008401 : Nat := 460261693755212764577737

theorem tailTrace_1008401 : CollatzResearch.WordTrace tailWord_1008401 prefixEnd_1008401 460261693755212764577737 := by
  unfold tailWord_1008401
  simp only [CollatzResearch.WordTrace]
  refine ⟨36779406019742873024681057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24519604013161915349787371 36779406019742873024681057)
  ·
    refine ⟨27584554514807154768510793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36779406019742873024681057 27584554514807154768510793)
    ·
      refine ⟨20688415886105366076383095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27584554514807154768510793 20688415886105366076383095)
      ·
        refine ⟨31032623829158049114574643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20688415886105366076383095 31032623829158049114574643)
        ·
          refine ⟨46548935743737073671861965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31032623829158049114574643 46548935743737073671861965)
          ·
            refine ⟨17455850903901402626948237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46548935743737073671861965 17455850903901402626948237)
            ·
              refine ⟨6545944088963025985105589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17455850903901402626948237 6545944088963025985105589)
              ·
                refine ⟨613682258340283686103649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6545944088963025985105589 613682258340283686103649)
                ·
                  refine ⟨460261693755212764577737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613682258340283686103649 460261693755212764577737)
                  ·
                    rfl

theorem cell20_1008401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_1008401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008401 prefixEnd_1008401 := by exact prefixLift 1008401
  have htrace : WordTrace (prefixWord ++ tailWord_1008401) baseStart_1008401 baseEnd_1008401 := by
    simpa [prefixWord, tailWord_1008401, baseEnd_1008401] using wordTrace_append hprefix tailTrace_1008401
  have hstable : (prefixWord ++ tailWord_1008401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008401).length < 2 ^ (prefixWord ++ tailWord_1008401).sum := by decide
  have hdescent : baseEnd_1008401 < baseStart_1008401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008415 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 5]
def baseStart_1008415 : Nat := 118140960795 + 1008415 * 2 ^ 59
def prefixEnd_1008415 : Nat := 4983230072969 + 3 ^ 40 * 1008415 * 2
def baseEnd_1008415 : Nat := 460268083736690938111013

theorem tailTrace_1008415 : CollatzResearch.WordTrace tailWord_1008415 prefixEnd_1008415 460268083736690938111013 := by
  unfold tailWord_1008415
  simp only [CollatzResearch.WordTrace]
  refine ⟨36779916641692153415690699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24519944427794768943793799 36779916641692153415690699)
  ·
    refine ⟨55169874962538230123536049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36779916641692153415690699 55169874962538230123536049)
    ·
      refine ⟨41377406221903672592652037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55169874962538230123536049 41377406221903672592652037)
      ·
        refine ⟨7758263666606938611122257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41377406221903672592652037 7758263666606938611122257)
        ·
          refine ⟨5818697749955203958341693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758263666606938611122257 5818697749955203958341693)
          ·
            refine ⟨2182011656233201484378135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5818697749955203958341693 2182011656233201484378135)
            ·
              refine ⟨3273017484349802226567203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182011656233201484378135 3273017484349802226567203)
              ·
                refine ⟨4909526226524703339850805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3273017484349802226567203 4909526226524703339850805)
                ·
                  refine ⟨460268083736690938111013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909526226524703339850805 460268083736690938111013)
                  ·
                    rfl

theorem cell20_1008415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_1008415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008415 prefixEnd_1008415 := by exact prefixLift 1008415
  have htrace : WordTrace (prefixWord ++ tailWord_1008415) baseStart_1008415 baseEnd_1008415 := by
    simpa [prefixWord, tailWord_1008415, baseEnd_1008415] using wordTrace_append hprefix tailTrace_1008415
  have hstable : (prefixWord ++ tailWord_1008415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008415).length < 2 ^ (prefixWord ++ tailWord_1008415).sum := by decide
  have hdescent : baseEnd_1008415 < baseStart_1008415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008418 : List Nat := [3, 3, 1, 1, 2, 2, 2, 4, 2]
def baseStart_1008418 : Nat := 118140960795 + 1008418 * 2 ^ 59
def prefixEnd_1008418 : Nat := 4983230072969 + 3 ^ 40 * 1008418 * 2
def baseEnd_1008418 : Nat := 460269453018436261011001

theorem tailTrace_1008418 : CollatzResearch.WordTrace tailWord_1008418 prefixEnd_1008418 460269453018436261011001 := by
  unfold tailWord_1008418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195006515170321232012477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24520017373787523285366605 9195006515170321232012477)
  ·
    refine ⟨3448127443188870462004679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9195006515170321232012477 3448127443188870462004679)
    ·
      refine ⟨5172191164783305693007019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448127443188870462004679 5172191164783305693007019)
      ·
        refine ⟨7758286747174958539510529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172191164783305693007019 7758286747174958539510529)
        ·
          refine ⟨5818715060381218904632897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758286747174958539510529 5818715060381218904632897)
          ·
            refine ⟨4364036295285914178474673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5818715060381218904632897 4364036295285914178474673)
            ·
              refine ⟨3273027221464435633856005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364036295285914178474673 3273027221464435633856005)
              ·
                refine ⟨613692604024581681348001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3273027221464435633856005 613692604024581681348001)
                ·
                  refine ⟨460269453018436261011001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613692604024581681348001 460269453018436261011001)
                  ·
                    rfl

theorem cell20_1008418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_1008418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008418 prefixEnd_1008418 := by exact prefixLift 1008418
  have htrace : WordTrace (prefixWord ++ tailWord_1008418) baseStart_1008418 baseEnd_1008418 := by
    simpa [prefixWord, tailWord_1008418, baseEnd_1008418] using wordTrace_append hprefix tailTrace_1008418
  have hstable : (prefixWord ++ tailWord_1008418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008418).length < 2 ^ (prefixWord ++ tailWord_1008418).sum := by decide
  have hdescent : baseEnd_1008418 < baseStart_1008418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008442 : List Nat := [3, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1008442 : Nat := 118140960795 + 1008442 * 2 ^ 59
def prefixEnd_1008442 : Nat := 4983230072969 + 3 ^ 40 * 1008442 * 2
def baseEnd_1008442 : Nat := 153426802424132948070301

theorem tailTrace_1008442 : CollatzResearch.WordTrace tailWord_1008442 prefixEnd_1008442 153426802424132948070301 := by
  unfold tailWord_1008442
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195225353148584256730895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24520600941729558017949053 9195225353148584256730895)
  ·
    refine ⟨13792838029722876385096343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195225353148584256730895 13792838029722876385096343)
    ·
      refine ⟨20689257044584314577644515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13792838029722876385096343 20689257044584314577644515)
      ·
        refine ⟨31033885566876471866466773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20689257044584314577644515 31033885566876471866466773)
        ·
          refine ⟨727356692973667309370315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31033885566876471866466773 727356692973667309370315)
          ·
            refine ⟨1091035039460500964055473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727356692973667309370315 1091035039460500964055473)
            ·
              refine ⟨818276279595375723041605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091035039460500964055473 818276279595375723041605)
              ·
                refine ⟨153426802424132948070301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 818276279595375723041605 153426802424132948070301)
                ·
                  rfl

theorem cell20_1008442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1008442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008442 prefixEnd_1008442 := by exact prefixLift 1008442
  have htrace : WordTrace (prefixWord ++ tailWord_1008442) baseStart_1008442 baseEnd_1008442 := by
    simpa [prefixWord, tailWord_1008442, baseEnd_1008442] using wordTrace_append hprefix tailTrace_1008442
  have hstable : (prefixWord ++ tailWord_1008442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008442).length < 2 ^ (prefixWord ++ tailWord_1008442).sum := by decide
  have hdescent : baseEnd_1008442 < baseStart_1008442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008484 : List Nat := [2, 3, 1, 1, 4, 2, 2, 5]
def baseStart_1008484 : Nat := 118140960795 + 1008484 * 2 ^ 59
def prefixEnd_1008484 : Nat := 4983230072969 + 3 ^ 40 * 1008484 * 2
def baseEnd_1008484 : Nat := 153433192405611121603577

theorem tailTrace_1008484 : CollatzResearch.WordTrace tailWord_1008484 prefixEnd_1008484 153433192405611121603577 := by
  unfold tailWord_1008484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18391216639221089099976253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24521622185628118799968337 18391216639221089099976253)
  ·
    refine ⟨6896706239707908412491095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18391216639221089099976253 6896706239707908412491095)
    ·
      refine ⟨10345059359561862618736643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896706239707908412491095 10345059359561862618736643)
      ·
        refine ⟨15517589039342793928104965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10345059359561862618736643 15517589039342793928104965)
        ·
          refine ⟨2909547944876773861519681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15517589039342793928104965 2909547944876773861519681)
          ·
            refine ⟨2182160958657580396139761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2909547944876773861519681 2182160958657580396139761)
            ·
              refine ⟨1636620718993185297104821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182160958657580396139761 1636620718993185297104821)
              ·
                refine ⟨153433192405611121603577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1636620718993185297104821 153433192405611121603577)
                ·
                  rfl

theorem cell20_1008484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_1008484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008484 prefixEnd_1008484 := by exact prefixLift 1008484
  have htrace : WordTrace (prefixWord ++ tailWord_1008484) baseStart_1008484 baseEnd_1008484 := by
    simpa [prefixWord, tailWord_1008484, baseEnd_1008484] using wordTrace_append hprefix tailTrace_1008484
  have hstable : (prefixWord ++ tailWord_1008484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008484).length < 2 ^ (prefixWord ++ tailWord_1008484).sum := by decide
  have hdescent : baseEnd_1008484 < baseStart_1008484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008487 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 3]
def baseStart_1008487 : Nat := 118140960795 + 1008487 * 2 ^ 59
def prefixEnd_1008487 : Nat := 4983230072969 + 3 ^ 40 * 1008487 * 2
def baseEnd_1008487 : Nat := 460300946498578687710719

theorem tailTrace_1008487 : CollatzResearch.WordTrace tailWord_1008487 prefixEnd_1008487 460300946498578687710719 := by
  unfold tailWord_1008487
  simp only [CollatzResearch.WordTrace]
  refine ⟨36782542697431309712311715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24521695131620873141541143 36782542697431309712311715)
  ·
    refine ⟨55173814046146964568467573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36782542697431309712311715 55173814046146964568467573)
    ·
      refine ⟨5172545066826277928293835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55173814046146964568467573 5172545066826277928293835)
      ·
        refine ⟨7758817600239416892440753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172545066826277928293835 7758817600239416892440753)
        ·
          refine ⟨5819113200179562669330565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7758817600239416892440753 5819113200179562669330565)
          ·
            refine ⟨1091083725033668000499481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5819113200179562669330565 1091083725033668000499481)
            ·
              refine ⟨818312793775251000374611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091083725033668000499481 818312793775251000374611)
              ·
                refine ⟨1227469190662876500561917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818312793775251000374611 1227469190662876500561917)
                ·
                  refine ⟨460300946498578687710719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227469190662876500561917 460300946498578687710719)
                  ·
                    rfl

theorem cell20_1008487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_1008487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008487 prefixEnd_1008487 := by exact prefixLift 1008487
  have htrace : WordTrace (prefixWord ++ tailWord_1008487) baseStart_1008487 baseEnd_1008487 := by
    simpa [prefixWord, tailWord_1008487, baseEnd_1008487] using wordTrace_append hprefix tailTrace_1008487
  have hstable : (prefixWord ++ tailWord_1008487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008487).length < 2 ^ (prefixWord ++ tailWord_1008487).sum := by decide
  have hdescent : baseEnd_1008487 < baseStart_1008487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008498 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_1008498 : Nat := 118140960795 + 1008498 * 2 ^ 59
def prefixEnd_1008498 : Nat := 4983230072969 + 3 ^ 40 * 1008498 * 2
def baseEnd_1008498 : Nat := 460305967198311538344007

theorem tailTrace_1008498 : CollatzResearch.WordTrace tailWord_1008498 prefixEnd_1008498 460305967198311538344007 := by
  unfold tailWord_1008498
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195735975097864647740537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24521962600260972393974765 9195735975097864647740537)
  ·
    refine ⟨6896801981323398485805403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9195735975097864647740537 6896801981323398485805403)
    ·
      refine ⟨10345202971985097728708105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6896801981323398485805403 10345202971985097728708105)
      ·
        refine ⟨7758902228988823296531079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10345202971985097728708105 7758902228988823296531079)
        ·
          refine ⟨11638353343483234944796619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7758902228988823296531079 11638353343483234944796619)
          ·
            refine ⟨17457530015224852417194929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11638353343483234944796619 17457530015224852417194929)
            ·
              refine ⟨13093147511418639312896197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17457530015224852417194929 13093147511418639312896197)
              ·
                refine ⟨2454965158390994871168037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13093147511418639312896197 2454965158390994871168037)
                ·
                  refine ⟨460305967198311538344007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2454965158390994871168037 460305967198311538344007)
                  ·
                    rfl

theorem cell20_1008498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_1008498 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008498 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008498 prefixEnd_1008498 := by exact prefixLift 1008498
  have htrace : WordTrace (prefixWord ++ tailWord_1008498) baseStart_1008498 baseEnd_1008498 := by
    simpa [prefixWord, tailWord_1008498, baseEnd_1008498] using wordTrace_append hprefix tailTrace_1008498
  have hstable : (prefixWord ++ tailWord_1008498).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008498).length < 2 ^ (prefixWord ++ tailWord_1008498).sum := by decide
  have hdescent : baseEnd_1008498 < baseStart_1008498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008505 : List Nat := [1, 2, 1, 3, 2, 3, 2, 6]
def baseStart_1008505 : Nat := 118140960795 + 1008505 * 2 ^ 59
def prefixEnd_1008505 : Nat := 4983230072969 + 3 ^ 40 * 1008505 * 2
def baseEnd_1008505 : Nat := 153436387396350208370215

theorem tailTrace_1008505 : CollatzResearch.WordTrace tailWord_1008505 prefixEnd_1008505 153436387396350208370215 := by
  unfold tailWord_1008505
  simp only [CollatzResearch.WordTrace]
  refine ⟨36783199211366098786466969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24522132807577399190977979 36783199211366098786466969)
  ·
    refine ⟨27587399408524574089850227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36783199211366098786466969 27587399408524574089850227)
    ·
      refine ⟨41381099112786861134775341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27587399408524574089850227 41381099112786861134775341)
      ·
        refine ⟨15517912167295072925540753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41381099112786861134775341 15517912167295072925540753)
        ·
          refine ⟨11638434125471304694155565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15517912167295072925540753 11638434125471304694155565)
          ·
            refine ⟨4364412797051739260308337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11638434125471304694155565 4364412797051739260308337)
            ·
              refine ⟨3273309597788804445231253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364412797051739260308337 3273309597788804445231253)
              ·
                refine ⟨153436387396350208370215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3273309597788804445231253 153436387396350208370215)
                ·
                  rfl

theorem cell20_1008505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 6].length) (baseStart_1008505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008505 prefixEnd_1008505 := by exact prefixLift 1008505
  have htrace : WordTrace (prefixWord ++ tailWord_1008505) baseStart_1008505 baseEnd_1008505 := by
    simpa [prefixWord, tailWord_1008505, baseEnd_1008505] using wordTrace_append hprefix tailTrace_1008505
  have hstable : (prefixWord ++ tailWord_1008505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008505).length < 2 ^ (prefixWord ++ tailWord_1008505).sum := by decide
  have hdescent : baseEnd_1008505 < baseStart_1008505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008512 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_1008512 : Nat := 118140960795 + 1008512 * 2 ^ 59
def prefixEnd_1008512 : Nat := 4983230072969 + 3 ^ 40 * 1008512 * 2
def baseEnd_1008512 : Nat := 460312357179789711877283

theorem tailTrace_1008512 : CollatzResearch.WordTrace tailWord_1008512 prefixEnd_1008512 460312357179789711877283 := by
  unfold tailWord_1008512
  simp only [CollatzResearch.WordTrace]
  refine ⟨18391727261170369490985895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24522303014893825987981193 18391727261170369490985895)
  ·
    refine ⟨27587590891755554236478843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18391727261170369490985895 27587590891755554236478843)
    ·
      refine ⟨41381386337633331354718265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27587590891755554236478843 41381386337633331354718265)
      ·
        refine ⟨31036039753224998516038699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41381386337633331354718265 31036039753224998516038699)
        ·
          refine ⟨46554059629837497774058049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31036039753224998516038699 46554059629837497774058049)
          ·
            refine ⟨34915544722378123330543537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46554059629837497774058049 34915544722378123330543537)
            ·
              refine ⟨26186658541783592497907653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34915544722378123330543537 26186658541783592497907653)
              ·
                refine ⟨4909998476584423593357685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26186658541783592497907653 4909998476584423593357685)
                ·
                  refine ⟨460312357179789711877283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4909998476584423593357685 460312357179789711877283)
                  ·
                    rfl

theorem cell20_1008512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_1008512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008512 prefixEnd_1008512 := by exact prefixLift 1008512
  have htrace : WordTrace (prefixWord ++ tailWord_1008512) baseStart_1008512 baseEnd_1008512 := by
    simpa [prefixWord, tailWord_1008512, baseEnd_1008512] using wordTrace_append hprefix tailTrace_1008512
  have hstable : (prefixWord ++ tailWord_1008512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008512).length < 2 ^ (prefixWord ++ tailWord_1008512).sum := by decide
  have hdescent : baseEnd_1008512 < baseStart_1008512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008515 : List Nat := [1, 1, 1, 3, 4, 1, 2, 5, 2]
def baseStart_1008515 : Nat := 118140960795 + 1008515 * 2 ^ 59
def prefixEnd_1008515 : Nat := 4983230072969 + 3 ^ 40 * 1008515 * 2
def baseEnd_1008515 : Nat := 460313726461535034777271

theorem tailTrace_1008515 : CollatzResearch.WordTrace tailWord_1008515 prefixEnd_1008515 460313726461535034777271 := by
  unfold tailWord_1008515
  simp only [CollatzResearch.WordTrace]
  refine ⟨36783563941329870494330999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24522375960886580329553999 36783563941329870494330999)
  ·
    refine ⟨55175345911994805741496499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36783563941329870494330999 55175345911994805741496499)
    ·
      refine ⟨82763018867992208612244749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55175345911994805741496499 82763018867992208612244749)
      ·
        refine ⟨31036132075497078229591781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82763018867992208612244749 31036132075497078229591781)
        ·
          refine ⟨5819274764155702168048459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31036132075497078229591781 5819274764155702168048459)
          ·
            refine ⟨8728912146233553252072689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819274764155702168048459 8728912146233553252072689)
            ·
              refine ⟨6546684109675164939054517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8728912146233553252072689 6546684109675164939054517)
              ·
                refine ⟨613751635282046713036361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6546684109675164939054517 613751635282046713036361)
                ·
                  refine ⟨460313726461535034777271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613751635282046713036361 460313726461535034777271)
                  ·
                    rfl

theorem cell20_1008515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 5, 2].length) (baseStart_1008515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008515 prefixEnd_1008515 := by exact prefixLift 1008515
  have htrace : WordTrace (prefixWord ++ tailWord_1008515) baseStart_1008515 baseEnd_1008515 := by
    simpa [prefixWord, tailWord_1008515, baseEnd_1008515] using wordTrace_append hprefix tailTrace_1008515
  have hstable : (prefixWord ++ tailWord_1008515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008515).length < 2 ^ (prefixWord ++ tailWord_1008515).sum := by decide
  have hdescent : baseEnd_1008515 < baseStart_1008515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008532 : List Nat := [2, 4, 2, 1, 1, 1, 3, 4, 2]
def baseStart_1008532 : Nat := 118140960795 + 1008532 * 2 ^ 59
def prefixEnd_1008532 : Nat := 4983230072969 + 3 ^ 40 * 1008532 * 2
def baseEnd_1008532 : Nat := 460321485724758531210535

theorem tailTrace_1008532 : CollatzResearch.WordTrace tailWord_1008532 prefixEnd_1008532 460321485724758531210535 := by
  unfold tailWord_1008532
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392091991134141198849925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24522789321512188265133233 18392091991134141198849925)
  ·
    refine ⟨3448517248337651474784361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18392091991134141198849925 3448517248337651474784361)
    ·
      refine ⟨2586387936253238606088271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3448517248337651474784361 2586387936253238606088271)
      ·
        refine ⟨3879581904379857909132407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586387936253238606088271 3879581904379857909132407)
        ·
          refine ⟨5819372856569786863698611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879581904379857909132407 5819372856569786863698611)
          ·
            refine ⟨8729059284854680295547917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5819372856569786863698611 8729059284854680295547917)
            ·
              refine ⟨3273397231820505110830469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8729059284854680295547917 3273397231820505110830469)
              ·
                refine ⟨613761980966344708280713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3273397231820505110830469 613761980966344708280713)
                ·
                  refine ⟨460321485724758531210535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613761980966344708280713 460321485724758531210535)
                  ·
                    rfl

theorem cell20_1008532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_1008532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008532 prefixEnd_1008532 := by exact prefixLift 1008532
  have htrace : WordTrace (prefixWord ++ tailWord_1008532) baseStart_1008532 baseEnd_1008532 := by
    simpa [prefixWord, tailWord_1008532, baseEnd_1008532] using wordTrace_append hprefix tailTrace_1008532
  have hstable : (prefixWord ++ tailWord_1008532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008532).length < 2 ^ (prefixWord ++ tailWord_1008532).sum := by decide
  have hdescent : baseEnd_1008532 < baseStart_1008532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008546 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_1008546 : Nat := 118140960795 + 1008546 * 2 ^ 59
def prefixEnd_1008546 : Nat := 4983230072969 + 3 ^ 40 * 1008546 * 2
def baseEnd_1008546 : Nat := 460327875706236704743811

theorem tailTrace_1008546 : CollatzResearch.WordTrace tailWord_1008546 prefixEnd_1008546 460327875706236704743811 := by
  unfold tailWord_1008546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196173651054390697177373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24523129736145041859139661 9196173651054390697177373)
  ·
    refine ⟨3448565119145396511441515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9196173651054390697177373 3448565119145396511441515)
    ·
      refine ⟨5172847678718094767162273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448565119145396511441515 5172847678718094767162273)
      ·
        refine ⟨3879635759038571075371705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5172847678718094767162273 3879635759038571075371705)
        ·
          refine ⟨2909726819278928306528779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3879635759038571075371705 2909726819278928306528779)
          ·
            refine ⟨4364590228918392459793169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909726819278928306528779 4364590228918392459793169)
            ·
              refine ⟨3273442671688794344844877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364590228918392459793169 3273442671688794344844877)
              ·
                refine ⟨1227541001883297879316829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3273442671688794344844877 1227541001883297879316829)
                ·
                  refine ⟨460327875706236704743811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227541001883297879316829 460327875706236704743811)
                  ·
                    rfl

theorem cell20_1008546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_1008546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008546 prefixEnd_1008546 := by exact prefixLift 1008546
  have htrace : WordTrace (prefixWord ++ tailWord_1008546) baseStart_1008546 baseEnd_1008546 := by
    simpa [prefixWord, tailWord_1008546, baseEnd_1008546] using wordTrace_append hprefix tailTrace_1008546
  have hstable : (prefixWord ++ tailWord_1008546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008546).length < 2 ^ (prefixWord ++ tailWord_1008546).sum := by decide
  have hdescent : baseEnd_1008546 < baseStart_1008546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008574 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1008574 : Nat := 118140960795 + 1008574 * 2 ^ 59
def prefixEnd_1008574 : Nat := 4983230072969 + 3 ^ 40 * 1008574 * 2
def baseEnd_1008574 : Nat := 460340655669193051810363

theorem tailTrace_1008574 : CollatzResearch.WordTrace tailWord_1008574 prefixEnd_1008574 460340655669193051810363 := by
  unfold tailWord_1008574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598214481014515446341097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24523810565410749047152517 4598214481014515446341097)
  ·
    refine ⟨3448660860760886584755823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4598214481014515446341097 3448660860760886584755823)
    ·
      refine ⟨5172991291141329877133735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3448660860760886584755823 5172991291141329877133735)
      ·
        refine ⟨7759486936711994815700603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5172991291141329877133735 7759486936711994815700603)
        ·
          refine ⟨11639230405067992223550905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759486936711994815700603 11639230405067992223550905)
          ·
            refine ⟨8729422803800994167663179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11639230405067992223550905 8729422803800994167663179)
            ·
              refine ⟨13094134205701491251494769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8729422803800994167663179 13094134205701491251494769)
              ·
                refine ⟨9820600654276118438621077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13094134205701491251494769 9820600654276118438621077)
                ·
                  refine ⟨460340655669193051810363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9820600654276118438621077 460340655669193051810363)
                  ·
                    rfl

theorem cell20_1008574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1008574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008574 prefixEnd_1008574 := by exact prefixLift 1008574
  have htrace : WordTrace (prefixWord ++ tailWord_1008574) baseStart_1008574 baseEnd_1008574 := by
    simpa [prefixWord, tailWord_1008574, baseEnd_1008574] using wordTrace_append hprefix tailTrace_1008574
  have hstable : (prefixWord ++ tailWord_1008574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008574).length < 2 ^ (prefixWord ++ tailWord_1008574).sum := by decide
  have hdescent : baseEnd_1008574 < baseStart_1008574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008580 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 3]
def baseStart_1008580 : Nat := 118140960795 + 1008580 * 2 ^ 59
def prefixEnd_1008580 : Nat := 4983230072969 + 3 ^ 40 * 1008580 * 2
def baseEnd_1008580 : Nat := 460343394232683697610339

theorem tailTrace_1008580 : CollatzResearch.WordTrace tailWord_1008580 prefixEnd_1008580 460343394232683697610339 := by
  unfold tailWord_1008580
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392967343047193297723597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24523956457396257730298129 18392967343047193297723597)
  ·
    refine ⟨6897362753642697486646349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18392967343047193297723597 6897362753642697486646349)
    ·
      refine ⟨2586511032616011557492381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6897362753642697486646349 2586511032616011557492381)
      ·
        refine ⟨969941637231004334059643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2586511032616011557492381 969941637231004334059643)
        ·
          refine ⟨1454912455846506501089465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969941637231004334059643 1454912455846506501089465)
          ·
            refine ⟨1091184341884879875817099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454912455846506501089465 1091184341884879875817099)
            ·
              refine ⟨1636776512827319813725649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091184341884879875817099 1636776512827319813725649)
              ·
                refine ⟨1227582384620489860294237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1636776512827319813725649 1227582384620489860294237)
                ·
                  refine ⟨460343394232683697610339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1227582384620489860294237 460343394232683697610339)
                  ·
                    rfl

theorem cell20_1008580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_1008580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008580 prefixEnd_1008580 := by exact prefixLift 1008580
  have htrace : WordTrace (prefixWord ++ tailWord_1008580) baseStart_1008580 baseEnd_1008580 := by
    simpa [prefixWord, tailWord_1008580, baseEnd_1008580] using wordTrace_append hprefix tailTrace_1008580
  have hstable : (prefixWord ++ tailWord_1008580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008580).length < 2 ^ (prefixWord ++ tailWord_1008580).sum := by decide
  have hdescent : baseEnd_1008580 < baseStart_1008580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008591 : List Nat := [1, 1, 2, 1, 1, 6, 2, 4, 2]
def baseStart_1008591 : Nat := 118140960795 + 1008591 * 2 ^ 59
def prefixEnd_1008591 : Nat := 4983230072969 + 3 ^ 40 * 1008591 * 2
def baseEnd_1008591 : Nat := 460348414932416548243627

theorem tailTrace_1008591 : CollatzResearch.WordTrace tailWord_1008591 prefixEnd_1008591 460348414932416548243627 := by
  unfold tailWord_1008591
  simp only [CollatzResearch.WordTrace]
  refine ⟨36786335889054535474097627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24524223926036356982731751 36786335889054535474097627)
  ·
    refine ⟨55179503833581803211146441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36786335889054535474097627 55179503833581803211146441)
    ·
      refine ⟨41384627875186352408359831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55179503833581803211146441 41384627875186352408359831)
      ·
        refine ⟨62076941812779528612539747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41384627875186352408359831 62076941812779528612539747)
        ·
          refine ⟨93115412719169292918809621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62076941812779528612539747 93115412719169292918809621)
          ·
            refine ⟨4364784971211060605569201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93115412719169292918809621 4364784971211060605569201)
            ·
              refine ⟨3273588728408295454176901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4364784971211060605569201 3273588728408295454176901)
              ·
                refine ⟨613797886576555397658169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3273588728408295454176901 613797886576555397658169)
                ·
                  refine ⟨460348414932416548243627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613797886576555397658169 460348414932416548243627)
                  ·
                    rfl

theorem cell20_1008591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2].length) (baseStart_1008591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008591 prefixEnd_1008591 := by exact prefixLift 1008591
  have htrace : WordTrace (prefixWord ++ tailWord_1008591) baseStart_1008591 baseEnd_1008591 := by
    simpa [prefixWord, tailWord_1008591, baseEnd_1008591] using wordTrace_append hprefix tailTrace_1008591
  have hstable : (prefixWord ++ tailWord_1008591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008591).length < 2 ^ (prefixWord ++ tailWord_1008591).sum := by decide
  have hdescent : baseEnd_1008591 < baseStart_1008591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008615 : List Nat := [1, 1, 5, 2, 2, 3, 2, 4]
def baseStart_1008615 : Nat := 118140960795 + 1008615 * 2 ^ 59
def prefixEnd_1008615 : Nat := 4983230072969 + 3 ^ 40 * 1008615 * 2
def baseEnd_1008615 : Nat := 153453123062126377147843

theorem tailTrace_1008615 : CollatzResearch.WordTrace tailWord_1008615 prefixEnd_1008615 153453123062126377147843 := by
  unfold tailWord_1008615
  simp only [CollatzResearch.WordTrace]
  refine ⟨36787211240967587572971299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24524807493978391715314199 36787211240967587572971299)
  ·
    refine ⟨55180816861451381359456949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36787211240967587572971299 55180816861451381359456949)
    ·
      refine ⟨5173201580761067002449089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55180816861451381359456949 5173201580761067002449089)
      ·
        refine ⟨3879901185570800251836817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5173201580761067002449089 3879901185570800251836817)
        ·
          refine ⟨2909925889178100188877613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3879901185570800251836817 2909925889178100188877613)
          ·
            refine ⟨1091222208441787570829105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2909925889178100188877613 1091222208441787570829105)
            ·
              refine ⟨818416656331340678121829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091222208441787570829105 818416656331340678121829)
              ·
                refine ⟨153453123062126377147843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 818416656331340678121829 153453123062126377147843)
                ·
                  rfl

theorem cell20_1008615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 4].length) (baseStart_1008615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008615 prefixEnd_1008615 := by exact prefixLift 1008615
  have htrace : WordTrace (prefixWord ++ tailWord_1008615) baseStart_1008615 baseEnd_1008615 := by
    simpa [prefixWord, tailWord_1008615, baseEnd_1008615] using wordTrace_append hprefix tailTrace_1008615
  have hstable : (prefixWord ++ tailWord_1008615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008615).length < 2 ^ (prefixWord ++ tailWord_1008615).sum := by decide
  have hdescent : baseEnd_1008615 < baseStart_1008615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008628 : List Nat := [2, 6, 2, 1, 2, 1, 6]
def baseStart_1008628 : Nat := 118140960795 + 1008628 * 2 ^ 59
def prefixEnd_1008628 : Nat := 4983230072969 + 3 ^ 40 * 1008628 * 2
def baseEnd_1008628 : Nat := 51151700304512096001127

theorem tailTrace_1008628 : CollatzResearch.WordTrace tailWord_1008628 prefixEnd_1008628 51151700304512096001127 := by
  unfold tailWord_1008628
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393842694960245396597269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24525123593280327195463025 18393842694960245396597269)
  ·
    refine ⟨862211376326261502965497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18393842694960245396597269 862211376326261502965497)
    ·
      refine ⟨646658532244696127224123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 862211376326261502965497 646658532244696127224123)
      ·
        refine ⟨969987798367044190836185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646658532244696127224123 969987798367044190836185)
        ·
          refine ⟨727490848775283143127139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 969987798367044190836185 727490848775283143127139)
          ·
            refine ⟨1091236273162924714690709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727490848775283143127139 1091236273162924714690709)
            ·
              refine ⟨51151700304512096001127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1091236273162924714690709 51151700304512096001127)
              ·
                rfl

theorem cell20_1008628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 6].length) (baseStart_1008628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008628 prefixEnd_1008628 := by exact prefixLift 1008628
  have htrace : WordTrace (prefixWord ++ tailWord_1008628) baseStart_1008628 baseEnd_1008628 := by
    simpa [prefixWord, tailWord_1008628, baseEnd_1008628] using wordTrace_append hprefix tailTrace_1008628
  have hstable : (prefixWord ++ tailWord_1008628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008628).length < 2 ^ (prefixWord ++ tailWord_1008628).sum := by decide
  have hdescent : baseEnd_1008628 < baseStart_1008628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008642 : List Nat := [3, 4, 1, 3, 2, 1, 1, 1, 4]
def baseStart_1008642 : Nat := 118140960795 + 1008642 * 2 ^ 59
def prefixEnd_1008642 : Nat := 4983230072969 + 3 ^ 40 * 1008642 * 2
def baseEnd_1008642 : Nat := 460371692722087037543419

theorem tailTrace_1008642 : CollatzResearch.WordTrace tailWord_1008642 prefixEnd_1008642 460371692722087037543419 := by
  unfold tailWord_1008642
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197049002967442796051045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24525464007913180789469453 9197049002967442796051045)
  ·
    refine ⟨1724446688056395524259571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9197049002967442796051045 1724446688056395524259571)
    ·
      refine ⟨2586670032084593286389357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724446688056395524259571 2586670032084593286389357)
      ·
        refine ⟨970001262031722482396009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2586670032084593286389357 970001262031722482396009)
        ·
          refine ⟨727500946523791861797007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 970001262031722482396009 727500946523791861797007)
          ·
            refine ⟨1091251419785687792695511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727500946523791861797007 1091251419785687792695511)
            ·
              refine ⟨1636877129678531689043267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091251419785687792695511 1636877129678531689043267)
              ·
                refine ⟨2455315694517797533564901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636877129678531689043267 2455315694517797533564901)
                ·
                  refine ⟨460371692722087037543419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455315694517797533564901 460371692722087037543419)
                  ·
                    rfl

theorem cell20_1008642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_1008642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008642 prefixEnd_1008642 := by exact prefixLift 1008642
  have htrace : WordTrace (prefixWord ++ tailWord_1008642) baseStart_1008642 baseEnd_1008642 := by
    simpa [prefixWord, tailWord_1008642, baseEnd_1008642] using wordTrace_append hprefix tailTrace_1008642
  have hstable : (prefixWord ++ tailWord_1008642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008642).length < 2 ^ (prefixWord ++ tailWord_1008642).sum := by decide
  have hdescent : baseEnd_1008642 < baseStart_1008642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008701 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 2]
def baseStart_1008701 : Nat := 118140960795 + 1008701 * 2 ^ 59
def prefixEnd_1008701 : Nat := 4983230072969 + 3 ^ 40 * 1008701 * 2
def baseEnd_1008701 : Nat := 460398621929745054576511

theorem tailTrace_1008701 : CollatzResearch.WordTrace tailWord_1008701 prefixEnd_1008701 460398621929745054576511 := by
  unfold tailWord_1008701
  simp only [CollatzResearch.WordTrace]
  refine ⟨36790347918656024260601957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24526898612437349507067971 36790347918656024260601957)
  ·
    refine ⟨6898190234748004548862867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36790347918656024260601957 6898190234748004548862867)
    ·
      refine ⟨10347285352122006823294301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898190234748004548862867 10347285352122006823294301)
      ·
        refine ⟨3880232007045752558735363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10347285352122006823294301 3880232007045752558735363)
        ·
          refine ⟨5820348010568628838103045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880232007045752558735363 5820348010568628838103045)
          ·
            refine ⟨1091315251981617907144321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5820348010568628838103045 1091315251981617907144321)
            ·
              refine ⟨818486438986213430358241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091315251981617907144321 818486438986213430358241)
              ·
                refine ⟨613864829239660072768681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818486438986213430358241 613864829239660072768681)
                ·
                  refine ⟨460398621929745054576511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613864829239660072768681 460398621929745054576511)
                  ·
                    rfl

theorem cell20_1008701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_1008701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008701 prefixEnd_1008701 := by exact prefixLift 1008701
  have htrace : WordTrace (prefixWord ++ tailWord_1008701) baseStart_1008701 baseEnd_1008701 := by
    simpa [prefixWord, tailWord_1008701, baseEnd_1008701] using wordTrace_append hprefix tailTrace_1008701
  have hstable : (prefixWord ++ tailWord_1008701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008701).length < 2 ^ (prefixWord ++ tailWord_1008701).sum := by decide
  have hdescent : baseEnd_1008701 < baseStart_1008701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008740 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_1008740 : Nat := 118140960795 + 1008740 * 2 ^ 59
def prefixEnd_1008740 : Nat := 4983230072969 + 3 ^ 40 * 1008740 * 2
def baseEnd_1008740 : Nat := 460416422592434252276351

theorem tailTrace_1008740 : CollatzResearch.WordTrace tailWord_1008740 prefixEnd_1008740 460416422592434252276351 := by
  unfold tailWord_1008740
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395885182757366960635837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24527846910343155947514449 18395885182757366960635837)
  ·
    refine ⟨6898456943534012610238439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18395885182757366960635837 6898456943534012610238439)
    ·
      refine ⟨10347685415301018915357659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6898456943534012610238439 10347685415301018915357659)
      ·
        refine ⟨15521528122951528373036489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10347685415301018915357659 15521528122951528373036489)
        ·
          refine ⟨11641146092213646279777367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15521528122951528373036489 11641146092213646279777367)
          ·
            refine ⟨17461719138320469419666051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11641146092213646279777367 17461719138320469419666051)
            ·
              refine ⟨26192578707480704129499077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17461719138320469419666051 26192578707480704129499077)
              ·
                refine ⟨4911108507652632024281077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26192578707480704129499077 4911108507652632024281077)
                ·
                  refine ⟨460416422592434252276351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4911108507652632024281077 460416422592434252276351)
                  ·
                    rfl

theorem cell20_1008740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_1008740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008740 prefixEnd_1008740 := by exact prefixLift 1008740
  have htrace : WordTrace (prefixWord ++ tailWord_1008740) baseStart_1008740 baseEnd_1008740 := by
    simpa [prefixWord, tailWord_1008740, baseEnd_1008740] using wordTrace_append hprefix tailTrace_1008740
  have hstable : (prefixWord ++ tailWord_1008740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008740).length < 2 ^ (prefixWord ++ tailWord_1008740).sum := by decide
  have hdescent : baseEnd_1008740 < baseStart_1008740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008743 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 2]
def baseStart_1008743 : Nat := 118140960795 + 1008743 * 2 ^ 59
def prefixEnd_1008743 : Nat := 4983230072969 + 3 ^ 40 * 1008743 * 2
def baseEnd_1008743 : Nat := 460417791874179575176339

theorem tailTrace_1008743 : CollatzResearch.WordTrace tailWord_1008743 prefixEnd_1008743 460417791874179575176339 := by
  unfold tailWord_1008743
  simp only [CollatzResearch.WordTrace]
  refine ⟨36791879784503865433630883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24527919856335910289087255 36791879784503865433630883)
  ·
    refine ⟨55187819676755798150446325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36791879784503865433630883 55187819676755798150446325)
    ·
      refine ⟨5173858094695856076604343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55187819676755798150446325 5173858094695856076604343)
      ·
        refine ⟨7760787142043784114906515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5173858094695856076604343 7760787142043784114906515)
        ·
          refine ⟨11641180713065676172359773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7760787142043784114906515 11641180713065676172359773)
          ·
            refine ⟨4365442767399628564634915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11641180713065676172359773 4365442767399628564634915)
            ·
              refine ⟨6548164151099442846952373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4365442767399628564634915 6548164151099442846952373)
              ·
                refine ⟨613890389165572766901785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6548164151099442846952373 613890389165572766901785)
                ·
                  refine ⟨460417791874179575176339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613890389165572766901785 460417791874179575176339)
                  ·
                    rfl

theorem cell20_1008743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 2].length) (baseStart_1008743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008743 prefixEnd_1008743 := by exact prefixLift 1008743
  have htrace : WordTrace (prefixWord ++ tailWord_1008743) baseStart_1008743 baseEnd_1008743 := by
    simpa [prefixWord, tailWord_1008743, baseEnd_1008743] using wordTrace_append hprefix tailTrace_1008743
  have hstable : (prefixWord ++ tailWord_1008743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008743).length < 2 ^ (prefixWord ++ tailWord_1008743).sum := by decide
  have hdescent : baseEnd_1008743 < baseStart_1008743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008764 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_1008764 : Nat := 118140960795 + 1008764 * 2 ^ 59
def prefixEnd_1008764 : Nat := 4983230072969 + 3 ^ 40 * 1008764 * 2
def baseEnd_1008764 : Nat := 460427376846396835476253

theorem tailTrace_1008764 : CollatzResearch.WordTrace tailWord_1008764 prefixEnd_1008764 460427376846396835476253 := by
  unfold tailWord_1008764
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396322858713893010072673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24528430478285190680096897 18396322858713893010072673)
  ·
    refine ⟨13797242144035419757554505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18396322858713893010072673 13797242144035419757554505)
    ·
      refine ⟨10347931608026564818165879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13797242144035419757554505 10347931608026564818165879)
      ·
        refine ⟨15521897412039847227248819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10347931608026564818165879 15521897412039847227248819)
        ·
          refine ⟨23282846118059770840873229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15521897412039847227248819 23282846118059770840873229)
          ·
            refine ⟨8731067294272414065327461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23282846118059770840873229 8731067294272414065327461)
            ·
              refine ⟨1637075117676077637248899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8731067294272414065327461 1637075117676077637248899)
              ·
                refine ⟨2455612676514116455873349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637075117676077637248899 2455612676514116455873349)
                ·
                  refine ⟨460427376846396835476253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2455612676514116455873349 460427376846396835476253)
                  ·
                    rfl

theorem cell20_1008764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_1008764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008764 prefixEnd_1008764 := by exact prefixLift 1008764
  have htrace : WordTrace (prefixWord ++ tailWord_1008764) baseStart_1008764 baseEnd_1008764 := by
    simpa [prefixWord, tailWord_1008764, baseEnd_1008764] using wordTrace_append hprefix tailTrace_1008764
  have hstable : (prefixWord ++ tailWord_1008764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008764).length < 2 ^ (prefixWord ++ tailWord_1008764).sum := by decide
  have hdescent : baseEnd_1008764 < baseStart_1008764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008822 : List Nat := [5, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1008822 : Nat := 118140960795 + 1008822 * 2 ^ 59
def prefixEnd_1008822 : Nat := 4983230072969 + 3 ^ 40 * 1008822 * 2
def baseEnd_1008822 : Nat := 153484616542268803847561

theorem tailTrace_1008822 : CollatzResearch.WordTrace tailWord_1008822 prefixEnd_1008822 153484616542268803847561 := by
  unfold tailWord_1008822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299672571951103870359795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24529840767478441283837813 2299672571951103870359795)
  ·
    refine ⟨3449508857926655805539693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299672571951103870359795 3449508857926655805539693)
    ·
      refine ⟨1293565821722495927077385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3449508857926655805539693 1293565821722495927077385)
      ·
        refine ⟨970174366291871945308039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293565821722495927077385 970174366291871945308039)
        ·
          refine ⟨1455261549437807917962059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970174366291871945308039 1455261549437807917962059)
          ·
            refine ⟨2182892324156711876943089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455261549437807917962059 2182892324156711876943089)
            ·
              refine ⟨1637169243117533907707317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182892324156711876943089 1637169243117533907707317)
              ·
                refine ⟨153484616542268803847561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1637169243117533907707317 153484616542268803847561)
                ·
                  rfl

theorem cell20_1008822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1008822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008822 prefixEnd_1008822 := by exact prefixLift 1008822
  have htrace : WordTrace (prefixWord ++ tailWord_1008822) baseStart_1008822 baseEnd_1008822 := by
    simpa [prefixWord, tailWord_1008822, baseEnd_1008822] using wordTrace_append hprefix tailTrace_1008822
  have hstable : (prefixWord ++ tailWord_1008822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008822).length < 2 ^ (prefixWord ++ tailWord_1008822).sum := by decide
  have hdescent : baseEnd_1008822 < baseStart_1008822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008874 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 2]
def baseStart_1008874 : Nat := 118140960795 + 1008874 * 2 ^ 59
def prefixEnd_1008874 : Nat := 4983230072969 + 3 ^ 40 * 1008874 * 2
def baseEnd_1008874 : Nat := 460477583843725341809137

theorem tailTrace_1008874 : CollatzResearch.WordTrace tailWord_1008874 prefixEnd_1008874 460477583843725341809137 := by
  unfold tailWord_1008874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199164436757318701662419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24531105164686183204433117 9199164436757318701662419)
  ·
    refine ⟨13798746655135978052493629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9199164436757318701662419 13798746655135978052493629)
    ·
      refine ⟨5174529995675991769685111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13798746655135978052493629 5174529995675991769685111)
      ·
        refine ⟨7761794993513987654527667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5174529995675991769685111 7761794993513987654527667)
        ·
          refine ⟨11642692490270981481791501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7761794993513987654527667 11642692490270981481791501)
          ·
            refine ⟨4366009683851618055671813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11642692490270981481791501 4366009683851618055671813)
            ·
              refine ⟨818626815722178385438465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4366009683851618055671813 818626815722178385438465)
              ·
                refine ⟨613970111791633789078849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818626815722178385438465 613970111791633789078849)
                ·
                  refine ⟨460477583843725341809137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613970111791633789078849 460477583843725341809137)
                  ·
                    rfl

theorem cell20_1008874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_1008874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008874 prefixEnd_1008874 := by exact prefixLift 1008874
  have htrace : WordTrace (prefixWord ++ tailWord_1008874) baseStart_1008874 baseEnd_1008874 := by
    simpa [prefixWord, tailWord_1008874, baseEnd_1008874] using wordTrace_append hprefix tailTrace_1008874
  have hstable : (prefixWord ++ tailWord_1008874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008874).length < 2 ^ (prefixWord ++ tailWord_1008874).sum := by decide
  have hdescent : baseEnd_1008874 < baseStart_1008874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008899 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_1008899 : Nat := 118140960795 + 1008899 * 2 ^ 59
def prefixEnd_1008899 : Nat := 4983230072969 + 3 ^ 40 * 1008899 * 2
def baseEnd_1008899 : Nat := 460488994524936365975701

theorem tailTrace_1008899 : CollatzResearch.WordTrace tailWord_1008899 prefixEnd_1008899 460488994524936365975701 := by
  unfold tailWord_1008899
  simp only [CollatzResearch.WordTrace]
  refine ⟨36797569571938704076309751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24531713047959136050873167 36797569571938704076309751)
  ·
    refine ⟨55196354357908056114464627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36797569571938704076309751 55196354357908056114464627)
    ·
      refine ⟨82794531536862084171696941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55196354357908056114464627 82794531536862084171696941)
      ·
        refine ⟨31047949326323281564386353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82794531536862084171696941 31047949326323281564386353)
        ·
          refine ⟨23285961994742461173289765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31047949326323281564386353 23285961994742461173289765)
          ·
            refine ⟨4366117874014211469991831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23285961994742461173289765 4366117874014211469991831)
            ·
              refine ⟨6549176811021317204987747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4366117874014211469991831 6549176811021317204987747)
              ·
                refine ⟨9823765216531975807481621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6549176811021317204987747 9823765216531975807481621)
                ·
                  refine ⟨460488994524936365975701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9823765216531975807481621 460488994524936365975701)
                  ·
                    rfl

theorem cell20_1008899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_1008899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008899 prefixEnd_1008899 := by exact prefixLift 1008899
  have htrace : WordTrace (prefixWord ++ tailWord_1008899) baseStart_1008899 baseEnd_1008899 := by
    simpa [prefixWord, tailWord_1008899, baseEnd_1008899] using wordTrace_append hprefix tailTrace_1008899
  have hstable : (prefixWord ++ tailWord_1008899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008899).length < 2 ^ (prefixWord ++ tailWord_1008899).sum := by decide
  have hdescent : baseEnd_1008899 < baseStart_1008899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008933 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 2]
def baseStart_1008933 : Nat := 118140960795 + 1008933 * 2 ^ 59
def prefixEnd_1008933 : Nat := 4983230072969 + 3 ^ 40 * 1008933 * 2
def baseEnd_1008933 : Nat := 460504513051383358842229

theorem tailTrace_1008933 : CollatzResearch.WordTrace tailWord_1008933 prefixEnd_1008933 460504513051383358842229 := by
  unfold tailWord_1008933
  simp only [CollatzResearch.WordTrace]
  refine ⟨36798809653815527883047453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24532539769210351922031635 36798809653815527883047453)
  ·
    refine ⟨13799553620180822956142795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36798809653815527883047453 13799553620180822956142795)
    ·
      refine ⟨20699330430271234434214193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13799553620180822956142795 20699330430271234434214193)
      ·
        refine ⟨15524497822703425825660645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20699330430271234434214193 15524497822703425825660645)
        ·
          refine ⟨2910843341756892342311371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15524497822703425825660645 2910843341756892342311371)
          ·
            refine ⟨4366265012635338513467057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2910843341756892342311371 4366265012635338513467057)
            ·
              refine ⟨3274698759476503885100293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366265012635338513467057 3274698759476503885100293)
              ·
                refine ⟨614006017401844478456305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3274698759476503885100293 614006017401844478456305)
                ·
                  refine ⟨460504513051383358842229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614006017401844478456305 460504513051383358842229)
                  ·
                    rfl

theorem cell20_1008933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_1008933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008933 prefixEnd_1008933 := by exact prefixLift 1008933
  have htrace : WordTrace (prefixWord ++ tailWord_1008933) baseStart_1008933 baseEnd_1008933 := by
    simpa [prefixWord, tailWord_1008933, baseEnd_1008933] using wordTrace_append hprefix tailTrace_1008933
  have hstable : (prefixWord ++ tailWord_1008933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008933).length < 2 ^ (prefixWord ++ tailWord_1008933).sum := by decide
  have hdescent : baseEnd_1008933 < baseStart_1008933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008944 : List Nat := [2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_1008944 : Nat := 118140960795 + 1008944 * 2 ^ 59
def prefixEnd_1008944 : Nat := 4983230072969 + 3 ^ 40 * 1008944 * 2
def baseEnd_1008944 : Nat := 153503177917038736491839

theorem tailTrace_1008944 : CollatzResearch.WordTrace tailWord_1008944 prefixEnd_1008944 153503177917038736491839 := by
  unfold tailWord_1008944
  simp only [CollatzResearch.WordTrace]
  refine ⟨18399605428387838380848943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24532807237850451174465257 18399605428387838380848943)
  ·
    refine ⟨27599408142581757571273415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18399605428387838380848943 27599408142581757571273415)
    ·
      refine ⟨41399112213872636356910123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27599408142581757571273415 41399112213872636356910123)
      ·
        refine ⟨62098668320808954535365185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41399112213872636356910123 62098668320808954535365185)
        ·
          refine ⟨46574001240606715901523889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62098668320808954535365185 46574001240606715901523889)
          ·
            refine ⟨34930500930455036926142917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46574001240606715901523889 34930500930455036926142917)
            ·
              refine ⟨6549468924460319423651797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34930500930455036926142917 6549468924460319423651797)
              ·
                refine ⟨153503177917038736491839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6549468924460319423651797 153503177917038736491839)
                ·
                  rfl

theorem cell20_1008944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_1008944 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008944 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008944 prefixEnd_1008944 := by exact prefixLift 1008944
  have htrace : WordTrace (prefixWord ++ tailWord_1008944) baseStart_1008944 baseEnd_1008944 := by
    simpa [prefixWord, tailWord_1008944, baseEnd_1008944] using wordTrace_append hprefix tailTrace_1008944
  have hstable : (prefixWord ++ tailWord_1008944).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008944).length < 2 ^ (prefixWord ++ tailWord_1008944).sum := by decide
  have hdescent : baseEnd_1008944 < baseStart_1008944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1008992 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 4]
def baseStart_1008992 : Nat := 118140960795 + 1008992 * 2 ^ 59
def prefixEnd_1008992 : Nat := 4983230072969 + 3 ^ 40 * 1008992 * 2
def baseEnd_1008992 : Nat := 460531442259041375875321

theorem tailTrace_1008992 : CollatzResearch.WordTrace tailWord_1008992 prefixEnd_1008992 460531442259041375875321 := by
  unfold tailWord_1008992
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400480780300890479722615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24533974373734520639630153 18400480780300890479722615)
  ·
    refine ⟨27600721170451335719583923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18400480780300890479722615 27600721170451335719583923)
    ·
      refine ⟨41401081755677003579375885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27600721170451335719583923 41401081755677003579375885)
      ·
        refine ⟨15525405658378876342265957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41401081755677003579375885 15525405658378876342265957)
        ·
          refine ⟨2911013560946039314174867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15525405658378876342265957 2911013560946039314174867)
          ·
            refine ⟨4366520341419058971262301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911013560946039314174867 4366520341419058971262301)
            ·
              refine ⟨1637445128032147114223363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4366520341419058971262301 1637445128032147114223363)
              ·
                refine ⟨2456167692048220671335045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637445128032147114223363 2456167692048220671335045)
                ·
                  refine ⟨460531442259041375875321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456167692048220671335045 460531442259041375875321)
                  ·
                    rfl

theorem cell20_1008992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_1008992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1008992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1008992 prefixEnd_1008992 := by exact prefixLift 1008992
  have htrace : WordTrace (prefixWord ++ tailWord_1008992) baseStart_1008992 baseEnd_1008992 := by
    simpa [prefixWord, tailWord_1008992, baseEnd_1008992] using wordTrace_append hprefix tailTrace_1008992
  have hstable : (prefixWord ++ tailWord_1008992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1008992).length < 2 ^ (prefixWord ++ tailWord_1008992).sum := by decide
  have hdescent : baseEnd_1008992 < baseStart_1008992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1008992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009002 : List Nat := [3, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_1009002 : Nat := 118140960795 + 1009002 * 2 ^ 59
def prefixEnd_1009002 : Nat := 4983230072969 + 3 ^ 40 * 1009002 * 2
def baseEnd_1009002 : Nat := 460536006531525785541947

theorem tailTrace_1009002 : CollatzResearch.WordTrace tailWord_1009002 prefixEnd_1009002 460536006531525785541947 := by
  unfold tailWord_1009002
  simp only [CollatzResearch.WordTrace]
  refine ⟨9200331572641388166827315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24534217527043701778206173 9200331572641388166827315)
  ·
    refine ⟨13800497358962082250240973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9200331572641388166827315 13800497358962082250240973)
    ·
      refine ⟨5175186509610780843840365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13800497358962082250240973 5175186509610780843840365)
      ·
        refine ⟨1940694941104042816440137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5175186509610780843840365 1940694941104042816440137)
        ·
          refine ⟨1455521205828032112330103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940694941104042816440137 1455521205828032112330103)
          ·
            refine ⟨2183281808742048168495155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455521205828032112330103 2183281808742048168495155)
            ·
              refine ⟨3274922713113072252742733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183281808742048168495155 3274922713113072252742733)
              ·
                refine ⟨1228096017417402094778525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3274922713113072252742733 1228096017417402094778525)
                ·
                  refine ⟨460536006531525785541947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228096017417402094778525 460536006531525785541947)
                  ·
                    rfl

theorem cell20_1009002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_1009002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009002 prefixEnd_1009002 := by exact prefixLift 1009002
  have htrace : WordTrace (prefixWord ++ tailWord_1009002) baseStart_1009002 baseEnd_1009002 := by
    simpa [prefixWord, tailWord_1009002, baseEnd_1009002] using wordTrace_append hprefix tailTrace_1009002
  have hstable : (prefixWord ++ tailWord_1009002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009002).length < 2 ^ (prefixWord ++ tailWord_1009002).sum := by decide
  have hdescent : baseEnd_1009002 < baseStart_1009002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009020 : List Nat := [2, 2, 2, 1, 1, 1, 3, 8]
def baseStart_1009020 : Nat := 118140960795 + 1009020 * 2 ^ 59
def prefixEnd_1009020 : Nat := 4983230072969 + 3 ^ 40 * 1009020 * 2
def baseEnd_1009020 : Nat := 153514740740665907647291

theorem tailTrace_1009020 : CollatzResearch.WordTrace tailWord_1009020 prefixEnd_1009020 153514740740665907647291 := by
  unfold tailWord_1009020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400991402250170870732257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24534655203000227827643009 18400991402250170870732257)
  ·
    refine ⟨13800743551687628153049193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18400991402250170870732257 13800743551687628153049193)
    ·
      refine ⟨10350557663765721114786895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13800743551687628153049193 10350557663765721114786895)
      ·
        refine ⟨15525836495648581672180343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10350557663765721114786895 15525836495648581672180343)
        ·
          refine ⟨23288754743472872508270515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15525836495648581672180343 23288754743472872508270515)
          ·
            refine ⟨34933132115209308762405773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23288754743472872508270515 34933132115209308762405773)
            ·
              refine ⟨13099924543203490785902165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34933132115209308762405773 13099924543203490785902165)
              ·
                refine ⟨153514740740665907647291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13099924543203490785902165 153514740740665907647291)
                ·
                  rfl

theorem cell20_1009020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_1009020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009020 prefixEnd_1009020 := by exact prefixLift 1009020
  have htrace : WordTrace (prefixWord ++ tailWord_1009020) baseStart_1009020 baseEnd_1009020 := by
    simpa [prefixWord, tailWord_1009020, baseEnd_1009020] using wordTrace_append hprefix tailTrace_1009020
  have hstable : (prefixWord ++ tailWord_1009020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009020).length < 2 ^ (prefixWord ++ tailWord_1009020).sum := by decide
  have hdescent : baseEnd_1009020 < baseStart_1009020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009065 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_1009065 : Nat := 118140960795 + 1009065 * 2 ^ 59
def prefixEnd_1009065 : Nat := 4983230072969 + 3 ^ 40 * 1009065 * 2
def baseEnd_1009065 : Nat := 460564761448177566441689

theorem tailTrace_1009065 : CollatzResearch.WordTrace tailWord_1009065 prefixEnd_1009065 460564761448177566441689 := by
  unfold tailWord_1009065
  simp only [CollatzResearch.WordTrace]
  refine ⟨36803624089337314426852649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24535749392891542951235099 36803624089337314426852649)
  ·
    refine ⟨27602718067002985820139487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36803624089337314426852649 27602718067002985820139487)
    ·
      refine ⟨41404077100504478730209231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27602718067002985820139487 41404077100504478730209231)
      ·
        refine ⟨62106115650756718095313847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41404077100504478730209231 62106115650756718095313847)
        ·
          refine ⟨93159173476135077142970771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62106115650756718095313847 93159173476135077142970771)
          ·
            refine ⟨139738760214202615714456157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93159173476135077142970771 139738760214202615714456157)
            ·
              refine ⟨52402035080325980892921059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139738760214202615714456157 52402035080325980892921059)
              ·
                refine ⟨78603052620488971339381589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52402035080325980892921059 78603052620488971339381589)
                ·
                  refine ⟨460564761448177566441689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78603052620488971339381589 460564761448177566441689)
                  ·
                    rfl

theorem cell20_1009065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_1009065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009065 prefixEnd_1009065 := by exact prefixLift 1009065
  have htrace : WordTrace (prefixWord ++ tailWord_1009065) baseStart_1009065 baseEnd_1009065 := by
    simpa [prefixWord, tailWord_1009065, baseEnd_1009065] using wordTrace_append hprefix tailTrace_1009065
  have hstable : (prefixWord ++ tailWord_1009065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009065).length < 2 ^ (prefixWord ++ tailWord_1009065).sum := by decide
  have hdescent : baseEnd_1009065 < baseStart_1009065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009085 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 2]
def baseStart_1009085 : Nat := 118140960795 + 1009085 * 2 ^ 59
def prefixEnd_1009085 : Nat := 4983230072969 + 3 ^ 40 * 1009085 * 2
def baseEnd_1009085 : Nat := 460573889993146385774941

theorem tailTrace_1009085 : CollatzResearch.WordTrace tailWord_1009085 prefixEnd_1009085 460573889993146385774941 := by
  unfold tailWord_1009085
  simp only [CollatzResearch.WordTrace]
  refine ⟨36804353549264857842580709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24536235699509905228387139 36804353549264857842580709)
  ·
    refine ⟨6900816290487160845483883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36804353549264857842580709 6900816290487160845483883)
    ·
      refine ⟨10351224435730741268225825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6900816290487160845483883 10351224435730741268225825)
      ·
        refine ⟨7763418326798055951169369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10351224435730741268225825 7763418326798055951169369)
        ·
          refine ⟨5822563745098541963377027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7763418326798055951169369 5822563745098541963377027)
          ·
            refine ⟨8733845617647812945065541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822563745098541963377027 8733845617647812945065541)
            ·
              refine ⟨1637596053308964927199789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8733845617647812945065541 1637596053308964927199789)
              ·
                refine ⟨614098519990861847699921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1637596053308964927199789 614098519990861847699921)
                ·
                  refine ⟨460573889993146385774941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614098519990861847699921 460573889993146385774941)
                  ·
                    rfl

theorem cell20_1009085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_1009085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009085 prefixEnd_1009085 := by exact prefixLift 1009085
  have htrace : WordTrace (prefixWord ++ tailWord_1009085) baseStart_1009085 baseEnd_1009085 := by
    simpa [prefixWord, tailWord_1009085, baseEnd_1009085] using wordTrace_append hprefix tailTrace_1009085
  have hstable : (prefixWord ++ tailWord_1009085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009085).length < 2 ^ (prefixWord ++ tailWord_1009085).sum := by decide
  have hdescent : baseEnd_1009085 < baseStart_1009085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009096 : List Nat := [2, 1, 3, 1, 3, 1, 9]
def baseStart_1009096 : Nat := 118140960795 + 1009096 * 2 ^ 59
def prefixEnd_1009096 : Nat := 4983230072969 + 3 ^ 40 * 1009096 * 2
def baseEnd_1009096 : Nat := 51175434521431026267581

theorem tailTrace_1009096 : CollatzResearch.WordTrace tailWord_1009096 prefixEnd_1009096 51175434521431026267581 := by
  unfold tailWord_1009096
  simp only [CollatzResearch.WordTrace]
  refine ⟨18402377376112503360615571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24536503168150004480820761 18402377376112503360615571)
  ·
    refine ⟨27603566064168755040923357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18402377376112503360615571 27603566064168755040923357)
    ·
      refine ⟨10351337274063283140346259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27603566064168755040923357 10351337274063283140346259)
      ·
        refine ⟨15527005911094924710519389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351337274063283140346259 15527005911094924710519389)
        ·
          refine ⟨5822627216660596766444771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15527005911094924710519389 5822627216660596766444771)
          ·
            refine ⟨8733940824990895149667157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822627216660596766444771 8733940824990895149667157)
            ·
              refine ⟨51175434521431026267581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8733940824990895149667157 51175434521431026267581)
              ·
                rfl

theorem cell20_1009096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 9].length) (baseStart_1009096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009096 prefixEnd_1009096 := by exact prefixLift 1009096
  have htrace : WordTrace (prefixWord ++ tailWord_1009096) baseStart_1009096 baseEnd_1009096 := by
    simpa [prefixWord, tailWord_1009096, baseEnd_1009096] using wordTrace_append hprefix tailTrace_1009096
  have hstable : (prefixWord ++ tailWord_1009096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009096).length < 2 ^ (prefixWord ++ tailWord_1009096).sum := by decide
  have hdescent : baseEnd_1009096 < baseStart_1009096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009161 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 2]
def baseStart_1009161 : Nat := 118140960795 + 1009161 * 2 ^ 59
def prefixEnd_1009161 : Nat := 4983230072969 + 3 ^ 40 * 1009161 * 2
def baseEnd_1009161 : Nat := 460608578464027899241297

theorem tailTrace_1009161 : CollatzResearch.WordTrace tailWord_1009161 prefixEnd_1009161 460608578464027899241297 := by
  unfold tailWord_1009161
  simp only [CollatzResearch.WordTrace]
  refine ⟨36807125496989522822347337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24538083664659681881564891 36807125496989522822347337)
  ·
    refine ⟨27605344122742142116760503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36807125496989522822347337 27605344122742142116760503)
    ·
      refine ⟨41408016184113213175140755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27605344122742142116760503 41408016184113213175140755)
      ·
        refine ⟨62112024276169819762711133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41408016184113213175140755 62112024276169819762711133)
        ·
          refine ⟨23292009103563682411016675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62112024276169819762711133 23292009103563682411016675)
          ·
            refine ⟨34938013655345523616525013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23292009103563682411016675 34938013655345523616525013)
            ·
              refine ⟨818859695047160709762305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 34938013655345523616525013 818859695047160709762305)
              ·
                refine ⟨614144771285370532321729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818859695047160709762305 614144771285370532321729)
                ·
                  refine ⟨460608578464027899241297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614144771285370532321729 460608578464027899241297)
                  ·
                    rfl

theorem cell20_1009161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 2].length) (baseStart_1009161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009161 prefixEnd_1009161 := by exact prefixLift 1009161
  have htrace : WordTrace (prefixWord ++ tailWord_1009161) baseStart_1009161 baseEnd_1009161 := by
    simpa [prefixWord, tailWord_1009161, baseEnd_1009161] using wordTrace_append hprefix tailTrace_1009161
  have hstable : (prefixWord ++ tailWord_1009161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009161).length < 2 ^ (prefixWord ++ tailWord_1009161).sum := by decide
  have hdescent : baseEnd_1009161 < baseStart_1009161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009206 : List Nat := [5, 1, 2, 1, 4, 7]
def baseStart_1009206 : Nat := 118140960795 + 1009206 * 2 ^ 59
def prefixEnd_1009206 : Nat := 4983230072969 + 3 ^ 40 * 1009206 * 2
def baseEnd_1009206 : Nat := 17060337692229916397819

theorem tailTrace_1009206 : CollatzResearch.WordTrace tailWord_1009206 prefixEnd_1009206 17060337692229916397819 := by
  unfold tailWord_1009206
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300547923864155969233467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24539177854550997005156981 2300547923864155969233467)
  ·
    refine ⟨3450821885796233953850201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2300547923864155969233467 3450821885796233953850201)
    ·
      refine ⟨2588116414347175465387651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3450821885796233953850201 2588116414347175465387651)
      ·
        refine ⟨3882174621520763198081477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588116414347175465387651 3882174621520763198081477)
        ·
          refine ⟨727907741535143099640277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3882174621520763198081477 727907741535143099640277)
          ·
            refine ⟨17060337692229916397819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 727907741535143099640277 17060337692229916397819)
            ·
              rfl

theorem cell20_1009206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 7].length) (baseStart_1009206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009206 prefixEnd_1009206 := by exact prefixLift 1009206
  have htrace : WordTrace (prefixWord ++ tailWord_1009206) baseStart_1009206 baseEnd_1009206 := by
    simpa [prefixWord, tailWord_1009206, baseEnd_1009206] using wordTrace_append hprefix tailTrace_1009206
  have hstable : (prefixWord ++ tailWord_1009206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009206).length < 2 ^ (prefixWord ++ tailWord_1009206).sum := by decide
  have hdescent : baseEnd_1009206 < baseStart_1009206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009244 : List Nat := [2, 2, 4, 1, 2, 2, 3, 4]
def baseStart_1009244 : Nat := 118140960795 + 1009244 * 2 ^ 59
def prefixEnd_1009244 : Nat := 4983230072969 + 3 ^ 40 * 1009244 * 2
def baseEnd_1009244 : Nat := 153548820641882833158097

theorem tailTrace_1009244 : CollatzResearch.WordTrace tailWord_1009244 prefixEnd_1009244 153548820641882833158097 := by
  unfold tailWord_1009244
  simp only [CollatzResearch.WordTrace]
  refine ⟨18405076377844413998809393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24540101837125885331745857 18405076377844413998809393)
  ·
    refine ⟨13803807283383310499107045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18405076377844413998809393 13803807283383310499107045)
    ·
      refine ⟨2588213865634370718582571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13803807283383310499107045 2588213865634370718582571)
      ·
        refine ⟨3882320798451556077873857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588213865634370718582571 3882320798451556077873857)
        ·
          refine ⟨2911740598838667058405393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882320798451556077873857 2911740598838667058405393)
          ·
            refine ⟨2183805449129000293804045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2911740598838667058405393 2183805449129000293804045)
            ·
              refine ⟨818927043423375110176517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2183805449129000293804045 818927043423375110176517)
              ·
                refine ⟨153548820641882833158097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 818927043423375110176517 153548820641882833158097)
                ·
                  rfl

theorem cell20_1009244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_1009244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009244 prefixEnd_1009244 := by exact prefixLift 1009244
  have htrace : WordTrace (prefixWord ++ tailWord_1009244) baseStart_1009244 baseEnd_1009244 := by
    simpa [prefixWord, tailWord_1009244, baseEnd_1009244] using wordTrace_append hprefix tailTrace_1009244
  have hstable : (prefixWord ++ tailWord_1009244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009244).length < 2 ^ (prefixWord ++ tailWord_1009244).sum := by decide
  have hdescent : baseEnd_1009244 < baseStart_1009244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009303 : List Nat := [1, 1, 3, 3, 2, 2, 4, 4]
def baseStart_1009303 : Nat := 118140960795 + 1009303 * 2 ^ 59
def prefixEnd_1009303 : Nat := 4983230072969 + 3 ^ 40 * 1009303 * 2
def baseEnd_1009303 : Nat := 153557797044435505502461

theorem tailTrace_1009303 : CollatzResearch.WordTrace tailWord_1009303 prefixEnd_1009303 153557797044435505502461 := by
  unfold tailWord_1009303
  simp only [CollatzResearch.WordTrace]
  refine ⟨36812304662475081074016563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24541536441650054049344375 36812304662475081074016563)
  ·
    refine ⟨55218456993712621611024845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36812304662475081074016563 55218456993712621611024845)
    ·
      refine ⟨20706921372642233104134317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55218456993712621611024845 20706921372642233104134317)
      ·
        refine ⟨7765095514740837414050369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20706921372642233104134317 7765095514740837414050369)
        ·
          refine ⟨5823821636055628060537777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7765095514740837414050369 5823821636055628060537777)
          ·
            refine ⟨4367866227041721045403333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5823821636055628060537777 4367866227041721045403333)
            ·
              refine ⟨818974917570322696013125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4367866227041721045403333 818974917570322696013125)
              ·
                refine ⟨153557797044435505502461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 818974917570322696013125 153557797044435505502461)
                ·
                  rfl

theorem cell20_1009303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 4].length) (baseStart_1009303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009303 prefixEnd_1009303 := by exact prefixLift 1009303
  have htrace : WordTrace (prefixWord ++ tailWord_1009303) baseStart_1009303 baseEnd_1009303 := by
    simpa [prefixWord, tailWord_1009303, baseEnd_1009303] using wordTrace_append hprefix tailTrace_1009303
  have hstable : (prefixWord ++ tailWord_1009303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009303).length < 2 ^ (prefixWord ++ tailWord_1009303).sum := by decide
  have hdescent : baseEnd_1009303 < baseStart_1009303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009313 : List Nat := [1, 2, 3, 3, 2, 1, 3, 3, 2]
def baseStart_1009313 : Nat := 118140960795 + 1009313 * 2 ^ 59
def prefixEnd_1009313 : Nat := 4983230072969 + 3 ^ 40 * 1009313 * 2
def baseEnd_1009313 : Nat := 460677955405790926174009

theorem tailTrace_1009313 : CollatzResearch.WordTrace tailWord_1009313 prefixEnd_1009313 460677955405790926174009 := by
  unfold tailWord_1009313
  simp only [CollatzResearch.WordTrace]
  refine ⟨36812669392438852781880593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24541779594959235187920395 36812669392438852781880593)
  ·
    refine ⟨27609502044329139586410445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36812669392438852781880593 27609502044329139586410445)
    ·
      refine ⟨10353563266623427344903917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27609502044329139586410445 10353563266623427344903917)
      ·
        refine ⟨3882586224983785254338969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10353563266623427344903917 3882586224983785254338969)
        ·
          refine ⟨2911939668737838940754227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3882586224983785254338969 2911939668737838940754227)
          ·
            refine ⟨4367909503106758411131341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911939668737838940754227 4367909503106758411131341)
            ·
              refine ⟨1637966063665034404174253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4367909503106758411131341 1637966063665034404174253)
              ·
                refine ⟨614237273874387901565345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1637966063665034404174253 614237273874387901565345)
                ·
                  refine ⟨460677955405790926174009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614237273874387901565345 460677955405790926174009)
                  ·
                    rfl

theorem cell20_1009313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_1009313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009313 prefixEnd_1009313 := by exact prefixLift 1009313
  have htrace : WordTrace (prefixWord ++ tailWord_1009313) baseStart_1009313 baseEnd_1009313 := by
    simpa [prefixWord, tailWord_1009313, baseEnd_1009313] using wordTrace_append hprefix tailTrace_1009313
  have hstable : (prefixWord ++ tailWord_1009313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009313).length < 2 ^ (prefixWord ++ tailWord_1009313).sum := by decide
  have hdescent : baseEnd_1009313 < baseStart_1009313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009331 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_1009331 : Nat := 118140960795 + 1009331 * 2 ^ 59
def prefixEnd_1009331 : Nat := 4983230072969 + 3 ^ 40 * 1009331 * 2
def baseEnd_1009331 : Nat := 460686171096262863573935

theorem tailTrace_1009331 : CollatzResearch.WordTrace tailWord_1009331 prefixEnd_1009331 460686171096262863573935 := by
  unfold tailWord_1009331
  simp only [CollatzResearch.WordTrace]
  refine ⟨36813325906373641856035847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24542217270915761237357231 36813325906373641856035847)
  ·
    refine ⟨55219988859560462784053771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36813325906373641856035847 55219988859560462784053771)
    ·
      refine ⟨82829983289340694176080657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55219988859560462784053771 82829983289340694176080657)
      ·
        refine ⟨62122487467005520632060493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82829983289340694176080657 62122487467005520632060493)
        ·
          refine ⟨23295932800127070237022685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62122487467005520632060493 23295932800127070237022685)
          ·
            refine ⟨8735974800047651338883507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23295932800127070237022685 8735974800047651338883507)
            ·
              refine ⟨13103962200071477008325261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735974800047651338883507 13103962200071477008325261)
              ·
                refine ⟨4913985825026803878121973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13103962200071477008325261 4913985825026803878121973)
                ·
                  refine ⟨460686171096262863573935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913985825026803878121973 460686171096262863573935)
                  ·
                    rfl

theorem cell20_1009331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_1009331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009331 prefixEnd_1009331 := by exact prefixLift 1009331
  have htrace : WordTrace (prefixWord ++ tailWord_1009331) baseStart_1009331 baseEnd_1009331 := by
    simpa [prefixWord, tailWord_1009331, baseEnd_1009331] using wordTrace_append hprefix tailTrace_1009331
  have hstable : (prefixWord ++ tailWord_1009331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009331).length < 2 ^ (prefixWord ++ tailWord_1009331).sum := by decide
  have hdescent : baseEnd_1009331 < baseStart_1009331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009379 : List Nat := [1, 1, 1, 7, 3, 7]
def baseStart_1009379 : Nat := 118140960795 + 1009379 * 2 ^ 59
def prefixEnd_1009379 : Nat := 4983230072969 + 3 ^ 40 * 1009379 * 2
def baseEnd_1009379 : Nat := 17063262207562519628657

theorem tailTrace_1009379 : CollatzResearch.WordTrace tailWord_1009379 prefixEnd_1009379 17063262207562519628657 := by
  unfold tailWord_1009379
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815076610199746053783191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24543384406799830702522127 36815076610199746053783191)
  ·
    refine ⟨55222614915299619080674787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36815076610199746053783191 55222614915299619080674787)
    ·
      refine ⟨82833922372949428621012181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55222614915299619080674787 82833922372949428621012181)
      ·
        refine ⟨1941420055616002233304973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 82833922372949428621012181 1941420055616002233304973)
        ·
          refine ⟨728032520856000837489365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1941420055616002233304973 728032520856000837489365)
          ·
            refine ⟨17063262207562519628657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 728032520856000837489365 17063262207562519628657)
            ·
              rfl

theorem cell20_1009379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 7].length) (baseStart_1009379 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009379 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009379 prefixEnd_1009379 := by exact prefixLift 1009379
  have htrace : WordTrace (prefixWord ++ tailWord_1009379) baseStart_1009379 baseEnd_1009379 := by
    simpa [prefixWord, tailWord_1009379, baseEnd_1009379] using wordTrace_append hprefix tailTrace_1009379
  have hstable : (prefixWord ++ tailWord_1009379).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009379).length < 2 ^ (prefixWord ++ tailWord_1009379).sum := by decide
  have hdescent : baseEnd_1009379 < baseStart_1009379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009386 : List Nat := [3, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_1009386 : Nat := 118140960795 + 1009386 * 2 ^ 59
def prefixEnd_1009386 : Nat := 4983230072969 + 3 ^ 40 * 1009386 * 2
def baseEnd_1009386 : Nat := 460711274594927116740377

theorem tailTrace_1009386 : CollatzResearch.WordTrace tailWord_1009386 prefixEnd_1009386 460711274594927116740377 := by
  unfold tailWord_1009386
  simp only [CollatzResearch.WordTrace]
  refine ⟨9203832980293596562322003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24543554614116257499525341 9203832980293596562322003)
  ·
    refine ⟨13805749470440394843483005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9203832980293596562322003 13805749470440394843483005)
    ·
      refine ⟨5177156051415148066306127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13805749470440394843483005 5177156051415148066306127)
      ·
        refine ⟨7765734077122722099459191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177156051415148066306127 7765734077122722099459191)
        ·
          refine ⟨11648601115684083149188787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765734077122722099459191 11648601115684083149188787)
          ·
            refine ⟨17472901673526124723783181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648601115684083149188787 17472901673526124723783181)
            ·
              refine ⟨6552338127572296771418693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17472901673526124723783181 6552338127572296771418693)
              ·
                refine ⟨1228563398919805644641005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6552338127572296771418693 1228563398919805644641005)
                ·
                  refine ⟨460711274594927116740377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228563398919805644641005 460711274594927116740377)
                  ·
                    rfl

theorem cell20_1009386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_1009386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009386 prefixEnd_1009386 := by exact prefixLift 1009386
  have htrace : WordTrace (prefixWord ++ tailWord_1009386) baseStart_1009386 baseEnd_1009386 := by
    simpa [prefixWord, tailWord_1009386, baseEnd_1009386] using wordTrace_append hprefix tailTrace_1009386
  have hstable : (prefixWord ++ tailWord_1009386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009386).length < 2 ^ (prefixWord ++ tailWord_1009386).sum := by decide
  have hdescent : baseEnd_1009386 < baseStart_1009386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009389 : List Nat := [1, 5, 1, 2, 1, 3, 1, 4, 2]
def baseStart_1009389 : Nat := 118140960795 + 1009389 * 2 ^ 59
def prefixEnd_1009389 : Nat := 4983230072969 + 3 ^ 40 * 1009389 * 2
def baseEnd_1009389 : Nat := 460712643876672439640365

theorem tailTrace_1009389 : CollatzResearch.WordTrace tailWord_1009389 prefixEnd_1009389 460712643876672439640365 := by
  unfold tailWord_1009389
  simp only [CollatzResearch.WordTrace]
  refine ⟨36815441340163517761647221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24543627560109011841098147 36815441340163517761647221)
  ·
    refine ⟨3451447625640329790154427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36815441340163517761647221 3451447625640329790154427)
    ·
      refine ⟨5177171438460494685231641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451447625640329790154427 5177171438460494685231641)
      ·
        refine ⟨3882878578845371013923731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5177171438460494685231641 3882878578845371013923731)
        ·
          refine ⟨5824317868268056520885597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882878578845371013923731 5824317868268056520885597)
          ·
            refine ⟨2184119200600521195332099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5824317868268056520885597 2184119200600521195332099)
            ·
              refine ⟨3276178800900781792998149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184119200600521195332099 3276178800900781792998149)
              ·
                refine ⟨614283525168896586187153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3276178800900781792998149 614283525168896586187153)
                ·
                  refine ⟨460712643876672439640365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614283525168896586187153 460712643876672439640365)
                  ·
                    rfl

theorem cell20_1009389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_1009389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009389 prefixEnd_1009389 := by exact prefixLift 1009389
  have htrace : WordTrace (prefixWord ++ tailWord_1009389) baseStart_1009389 baseEnd_1009389 := by
    simpa [prefixWord, tailWord_1009389, baseEnd_1009389] using wordTrace_append hprefix tailTrace_1009389
  have hstable : (prefixWord ++ tailWord_1009389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009389).length < 2 ^ (prefixWord ++ tailWord_1009389).sum := by decide
  have hdescent : baseEnd_1009389 < baseStart_1009389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009410 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1009410 : Nat := 118140960795 + 1009410 * 2 ^ 59
def prefixEnd_1009410 : Nat := 4983230072969 + 3 ^ 40 * 1009410 * 2
def baseEnd_1009410 : Nat := 460722228848889699940279

theorem tailTrace_1009410 : CollatzResearch.WordTrace tailWord_1009410 prefixEnd_1009410 460722228848889699940279 := by
  unfold tailWord_1009410
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204051818271859587040421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24544138182058292232107789 9204051818271859587040421)
  ·
    refine ⟨1725759715925973672570079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9204051818271859587040421 1725759715925973672570079)
    ·
      refine ⟨2588639573888960508855119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725759715925973672570079 2588639573888960508855119)
      ·
        refine ⟨3882959360833440763282679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588639573888960508855119 3882959360833440763282679)
        ·
          refine ⟨5824439041250161144924019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3882959360833440763282679 5824439041250161144924019)
          ·
            refine ⟨8736658561875241717386029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5824439041250161144924019 8736658561875241717386029)
            ·
              refine ⟨3276246960703215644019761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8736658561875241717386029 3276246960703215644019761)
              ·
                refine ⟨2457185220527411733014821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276246960703215644019761 2457185220527411733014821)
                ·
                  refine ⟨460722228848889699940279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457185220527411733014821 460722228848889699940279)
                  ·
                    rfl

theorem cell20_1009410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1009410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009410 prefixEnd_1009410 := by exact prefixLift 1009410
  have htrace : WordTrace (prefixWord ++ tailWord_1009410) baseStart_1009410 baseEnd_1009410 := by
    simpa [prefixWord, tailWord_1009410, baseEnd_1009410] using wordTrace_append hprefix tailTrace_1009410
  have hstable : (prefixWord ++ tailWord_1009410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009410).length < 2 ^ (prefixWord ++ tailWord_1009410).sum := by decide
  have hdescent : baseEnd_1009410 < baseStart_1009410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009441 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 3]
def baseStart_1009441 : Nat := 118140960795 + 1009441 * 2 ^ 59
def prefixEnd_1009441 : Nat := 4983230072969 + 3 ^ 40 * 1009441 * 2
def baseEnd_1009441 : Nat := 460736378093591369906819

theorem tailTrace_1009441 : CollatzResearch.WordTrace tailWord_1009441 prefixEnd_1009441 460736378093591369906819 := by
  unfold tailWord_1009441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36817337935975130642540177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24544891957316753761693451 36817337935975130642540177)
  ·
    refine ⟨27613003451981347981905133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36817337935975130642540177 27613003451981347981905133)
    ·
      refine ⟨10354876294493005493214425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27613003451981347981905133 10354876294493005493214425)
      ·
        refine ⟨7766157220869754119910819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10354876294493005493214425 7766157220869754119910819)
        ·
          refine ⟨11649235831304631179866229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766157220869754119910819 11649235831304631179866229)
          ·
            refine ⟨1092115859184809173112459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11649235831304631179866229 1092115859184809173112459)
            ·
              refine ⟨1638173788777213759668689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092115859184809173112459 1638173788777213759668689)
              ·
                refine ⟨1228630341582910319751517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638173788777213759668689 1228630341582910319751517)
                ·
                  refine ⟨460736378093591369906819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228630341582910319751517 460736378093591369906819)
                  ·
                    rfl

theorem cell20_1009441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_1009441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009441 prefixEnd_1009441 := by exact prefixLift 1009441
  have htrace : WordTrace (prefixWord ++ tailWord_1009441) baseStart_1009441 baseEnd_1009441 := by
    simpa [prefixWord, tailWord_1009441, baseEnd_1009441] using wordTrace_append hprefix tailTrace_1009441
  have hstable : (prefixWord ++ tailWord_1009441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009441).length < 2 ^ (prefixWord ++ tailWord_1009441).sum := by decide
  have hdescent : baseEnd_1009441 < baseStart_1009441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009448 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_1009448 : Nat := 118140960795 + 1009448 * 2 ^ 59
def prefixEnd_1009448 : Nat := 4983230072969 + 3 ^ 40 * 1009448 * 2
def baseEnd_1009448 : Nat := 460739573084330456673457

theorem tailTrace_1009448 : CollatzResearch.WordTrace tailWord_1009448 prefixEnd_1009448 460739573084330456673457 := by
  unfold tailWord_1009448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18408796623474885419022499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24545062164633180558696665 18408796623474885419022499)
  ·
    refine ⟨27613194935212328128533749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18408796623474885419022499 27613194935212328128533749)
    ·
      refine ⟨2588737025176155762050039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27613194935212328128533749 2588737025176155762050039)
      ·
        refine ⟨3883105537764233643075059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2588737025176155762050039 3883105537764233643075059)
        ·
          refine ⟨5824658306646350464612589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883105537764233643075059 5824658306646350464612589)
          ·
            refine ⟨2184246864992381424229721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5824658306646350464612589 2184246864992381424229721)
            ·
              refine ⟨1638185148744286068172291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184246864992381424229721 1638185148744286068172291)
              ·
                refine ⟨2457277723116429102258437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638185148744286068172291 2457277723116429102258437)
                ·
                  refine ⟨460739573084330456673457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457277723116429102258437 460739573084330456673457)
                  ·
                    rfl

theorem cell20_1009448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_1009448 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009448 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009448 prefixEnd_1009448 := by exact prefixLift 1009448
  have htrace : WordTrace (prefixWord ++ tailWord_1009448) baseStart_1009448 baseEnd_1009448 := by
    simpa [prefixWord, tailWord_1009448, baseEnd_1009448] using wordTrace_append hprefix tailTrace_1009448
  have hstable : (prefixWord ++ tailWord_1009448).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009448).length < 2 ^ (prefixWord ++ tailWord_1009448).sum := by decide
  have hdescent : baseEnd_1009448 < baseStart_1009448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009503 : List Nat := [1, 1, 2, 3, 1, 5, 3, 2, 2]
def baseStart_1009503 : Nat := 118140960795 + 1009503 * 2 ^ 59
def prefixEnd_1009503 : Nat := 4983230072969 + 3 ^ 40 * 1009503 * 2
def baseEnd_1009503 : Nat := 460764676582994709839899

theorem tailTrace_1009503 : CollatzResearch.WordTrace tailWord_1009503 prefixEnd_1009503 460764676582994709839899 := by
  unfold tailWord_1009503
  simp only [CollatzResearch.WordTrace]
  refine ⟨36819599261750515231297163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24546399507833676820864775 36819599261750515231297163)
  ·
    refine ⟨55229398892625772846945745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36819599261750515231297163 55229398892625772846945745)
    ·
      refine ⟨41422049169469329635209309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55229398892625772846945745 41422049169469329635209309)
      ·
        refine ⟨15533268438550998613203491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41422049169469329635209309 15533268438550998613203491)
        ·
          refine ⟨23299902657826497919805237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15533268438550998613203491 23299902657826497919805237)
          ·
            refine ⟨2184365874171234179981741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23299902657826497919805237 2184365874171234179981741)
            ·
              refine ⟨819137202814212817493153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184365874171234179981741 819137202814212817493153)
              ·
                refine ⟨614352902110659613119865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819137202814212817493153 614352902110659613119865)
                ·
                  refine ⟨460764676582994709839899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614352902110659613119865 460764676582994709839899)
                  ·
                    rfl

theorem cell20_1009503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 2, 2].length) (baseStart_1009503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009503 prefixEnd_1009503 := by exact prefixLift 1009503
  have htrace : WordTrace (prefixWord ++ tailWord_1009503) baseStart_1009503 baseEnd_1009503 := by
    simpa [prefixWord, tailWord_1009503, baseEnd_1009503] using wordTrace_append hprefix tailTrace_1009503
  have hstable : (prefixWord ++ tailWord_1009503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009503).length < 2 ^ (prefixWord ++ tailWord_1009503).sum := by decide
  have hdescent : baseEnd_1009503 < baseStart_1009503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009517 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 3]
def baseStart_1009517 : Nat := 118140960795 + 1009517 * 2 ^ 59
def prefixEnd_1009517 : Nat := 4983230072969 + 3 ^ 40 * 1009517 * 2
def baseEnd_1009517 : Nat := 460771066564472883373175

theorem tailTrace_1009517 : CollatzResearch.WordTrace tailWord_1009517 prefixEnd_1009517 460771066564472883373175 := by
  unfold tailWord_1009517
  simp only [CollatzResearch.WordTrace]
  refine ⟨36820109883699795622306805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24546739922466530414871203 36820109883699795622306805)
  ·
    refine ⟨3451885301596855839591263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36820109883699795622306805 3451885301596855839591263)
    ·
      refine ⟨5177827952395283759386895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451885301596855839591263 5177827952395283759386895)
      ·
        refine ⟨7766741928592925639080343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177827952395283759386895 7766741928592925639080343)
        ·
          refine ⟨11650112892889388458620515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766741928592925639080343 11650112892889388458620515)
          ·
            refine ⟨17475169339334082687930773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650112892889388458620515 17475169339334082687930773)
            ·
              refine ⟨819148562781285125996755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17475169339334082687930773 819148562781285125996755)
              ·
                refine ⟨1228722844171927688995133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819148562781285125996755 1228722844171927688995133)
                ·
                  refine ⟨460771066564472883373175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228722844171927688995133 460771066564472883373175)
                  ·
                    rfl

theorem cell20_1009517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_1009517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009517 prefixEnd_1009517 := by exact prefixLift 1009517
  have htrace : WordTrace (prefixWord ++ tailWord_1009517) baseStart_1009517 baseEnd_1009517 := by
    simpa [prefixWord, tailWord_1009517, baseEnd_1009517] using wordTrace_append hprefix tailTrace_1009517
  have hstable : (prefixWord ++ tailWord_1009517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009517).length < 2 ^ (prefixWord ++ tailWord_1009517).sum := by decide
  have hdescent : baseEnd_1009517 < baseStart_1009517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009582 : List Nat := [4, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1009582 : Nat := 118140960795 + 1009582 * 2 ^ 59
def prefixEnd_1009582 : Nat := 4983230072969 + 3 ^ 40 * 1009582 * 2
def baseEnd_1009582 : Nat := 153600244778540515402081

theorem tailTrace_1009582 : CollatzResearch.WordTrace tailWord_1009582 prefixEnd_1009582 153600244778540515402081 := by
  unfold tailWord_1009582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4602810078558038965427875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24548320418976207815615333 4602810078558038965427875)
  ·
    refine ⟨6904215117837058448141813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4602810078558038965427875 6904215117837058448141813)
    ·
      refine ⟨647270167297224229513295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6904215117837058448141813 647270167297224229513295)
      ·
        refine ⟨970905250945836344269943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647270167297224229513295 970905250945836344269943)
        ·
          refine ⟨1456357876418754516404915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970905250945836344269943 1456357876418754516404915)
          ·
            refine ⟨2184536814628131774607373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456357876418754516404915 2184536814628131774607373)
            ·
              refine ⟨819201305485549415477765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184536814628131774607373 819201305485549415477765)
              ·
                refine ⟨153600244778540515402081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 819201305485549415477765 153600244778540515402081)
                ·
                  rfl

theorem cell20_1009582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1009582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009582 prefixEnd_1009582 := by exact prefixLift 1009582
  have htrace : WordTrace (prefixWord ++ tailWord_1009582) baseStart_1009582 baseEnd_1009582 := by
    simpa [prefixWord, tailWord_1009582, baseEnd_1009582] using wordTrace_append hprefix tailTrace_1009582
  have hstable : (prefixWord ++ tailWord_1009582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009582).length < 2 ^ (prefixWord ++ tailWord_1009582).sum := by decide
  have hdescent : baseEnd_1009582 < baseStart_1009582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009596 : List Nat := [2, 2, 2, 5, 1, 1, 2, 3, 2]
def baseStart_1009596 : Nat := 118140960795 + 1009596 * 2 ^ 59
def prefixEnd_1009596 : Nat := 4983230072969 + 3 ^ 40 * 1009596 * 2
def baseEnd_1009596 : Nat := 460807124317099719739519

theorem tailTrace_1009596 : CollatzResearch.WordTrace tailWord_1009596 prefixEnd_1009596 460807124317099719739519 := by
  unfold tailWord_1009596
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411495625206796057216321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24548660833609061409621761 18411495625206796057216321)
  ·
    refine ⟨13808621718905097042912241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18411495625206796057216321 13808621718905097042912241)
    ·
      refine ⟨10356466289178822782184181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13808621718905097042912241 10356466289178822782184181)
      ·
        refine ⟨970918714610514635829767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10356466289178822782184181 970918714610514635829767)
        ·
          refine ⟨1456378071915771953744651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970918714610514635829767 1456378071915771953744651)
          ·
            refine ⟨2184567107873657930616977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456378071915771953744651 2184567107873657930616977)
            ·
              refine ⟨1638425330905243447962733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184567107873657930616977 1638425330905243447962733)
              ·
                refine ⟨614409499089466292986025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638425330905243447962733 614409499089466292986025)
                ·
                  refine ⟨460807124317099719739519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614409499089466292986025 460807124317099719739519)
                  ·
                    rfl

theorem cell20_1009596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 3, 2].length) (baseStart_1009596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009596 prefixEnd_1009596 := by exact prefixLift 1009596
  have htrace : WordTrace (prefixWord ++ tailWord_1009596) baseStart_1009596 baseEnd_1009596 := by
    simpa [prefixWord, tailWord_1009596, baseEnd_1009596] using wordTrace_append hprefix tailTrace_1009596
  have hstable : (prefixWord ++ tailWord_1009596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009596).length < 2 ^ (prefixWord ++ tailWord_1009596).sum := by decide
  have hdescent : baseEnd_1009596 < baseStart_1009596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009600 : List Nat := [2, 1, 1, 2, 3, 2, 4, 3, 2]
def baseStart_1009600 : Nat := 118140960795 + 1009600 * 2 ^ 59
def prefixEnd_1009600 : Nat := 4983230072969 + 3 ^ 40 * 1009600 * 2
def baseEnd_1009600 : Nat := 460808950026093483606169

theorem tailTrace_1009600 : CollatzResearch.WordTrace tailWord_1009600 prefixEnd_1009600 460808950026093483606169 := by
  unfold tailWord_1009600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411568571199550398789127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24548758094932733865052169 18411568571199550398789127)
  ·
    refine ⟨27617352856799325598183691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18411568571199550398789127 27617352856799325598183691)
    ·
      refine ⟨41426029285198988397275537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27617352856799325598183691 41426029285198988397275537)
      ·
        refine ⟨31069521963899241297956653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41426029285198988397275537 31069521963899241297956653)
        ·
          refine ⟨11651070736462215486733745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31069521963899241297956653 11651070736462215486733745)
          ·
            refine ⟨8738303052346661615050309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11651070736462215486733745 8738303052346661615050309)
            ·
              refine ⟨1638431822314999052821933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8738303052346661615050309 1638431822314999052821933)
              ·
                refine ⟨614411933368124644808225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638431822314999052821933 614411933368124644808225)
                ·
                  refine ⟨460808950026093483606169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614411933368124644808225 460808950026093483606169)
                  ·
                    rfl

theorem cell20_1009600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 2].length) (baseStart_1009600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009600 prefixEnd_1009600 := by exact prefixLift 1009600
  have htrace : WordTrace (prefixWord ++ tailWord_1009600) baseStart_1009600 baseEnd_1009600 := by
    simpa [prefixWord, tailWord_1009600, baseEnd_1009600] using wordTrace_append hprefix tailTrace_1009600
  have hstable : (prefixWord ++ tailWord_1009600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009600).length < 2 ^ (prefixWord ++ tailWord_1009600).sum := by decide
  have hdescent : baseEnd_1009600 < baseStart_1009600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009611 : List Nat := [1, 1, 1, 1, 3, 4, 9]
def baseStart_1009611 : Nat := 118140960795 + 1009611 * 2 ^ 59
def prefixEnd_1009611 : Nat := 4983230072969 + 3 ^ 40 * 1009611 * 2
def baseEnd_1009611 : Nat := 51201552302869592693273

theorem tailTrace_1009611 : CollatzResearch.WordTrace tailWord_1009611 prefixEnd_1009611 51201552302869592693273 := by
  unfold tailWord_1009611
  simp only [CollatzResearch.WordTrace]
  refine ⟨36823538345359249676228687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24549025563572833117485791 36823538345359249676228687)
  ·
    refine ⟨55235307518038874514343031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36823538345359249676228687 55235307518038874514343031)
    ·
      refine ⟨82852961277058311771514547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55235307518038874514343031 82852961277058311771514547)
      ·
        refine ⟨124279441915587467657271821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82852961277058311771514547 124279441915587467657271821)
        ·
          refine ⟨46604790718345300371476933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124279441915587467657271821 46604790718345300371476933)
          ·
            refine ⟨8738398259689743819651925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46604790718345300371476933 8738398259689743819651925)
            ·
              refine ⟨51201552302869592693273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8738398259689743819651925 51201552302869592693273)
              ·
                rfl

theorem cell20_1009611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 9].length) (baseStart_1009611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009611 prefixEnd_1009611 := by exact prefixLift 1009611
  have htrace : WordTrace (prefixWord ++ tailWord_1009611) baseStart_1009611 baseEnd_1009611 := by
    simpa [prefixWord, tailWord_1009611, baseEnd_1009611] using wordTrace_append hprefix tailTrace_1009611
  have hstable : (prefixWord ++ tailWord_1009611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009611).length < 2 ^ (prefixWord ++ tailWord_1009611).sum := by decide
  have hdescent : baseEnd_1009611 < baseStart_1009611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009621 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 4]
def baseStart_1009621 : Nat := 118140960795 + 1009621 * 2 ^ 59
def prefixEnd_1009621 : Nat := 4983230072969 + 3 ^ 40 * 1009621 * 2
def baseEnd_1009621 : Nat := 460818534998310743906083

theorem tailTrace_1009621 : CollatzResearch.WordTrace tailWord_1009621 prefixEnd_1009621 460818534998310743906083 := by
  unfold tailWord_1009621
  simp only [CollatzResearch.WordTrace]
  refine ⟨36823903075323021384092717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24549268716882014256061811 36823903075323021384092717)
  ·
    refine ⟨13808963653246133019034769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36823903075323021384092717 13808963653246133019034769)
    ·
      refine ⟨10356722739934599764276077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13808963653246133019034769 10356722739934599764276077)
      ·
        refine ⟨3883771027475474911603529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10356722739934599764276077 3883771027475474911603529)
        ·
          refine ⟨2912828270606606183702647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3883771027475474911603529 2912828270606606183702647)
          ·
            refine ⟨4369242405909909275553971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912828270606606183702647 4369242405909909275553971)
            ·
              refine ⟨6553863608864863913330957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4369242405909909275553971 6553863608864863913330957)
              ·
                refine ⟨2457698853324323967499109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6553863608864863913330957 2457698853324323967499109)
                ·
                  refine ⟨460818534998310743906083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2457698853324323967499109 460818534998310743906083)
                  ·
                    rfl

theorem cell20_1009621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_1009621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009621 prefixEnd_1009621 := by exact prefixLift 1009621
  have htrace : WordTrace (prefixWord ++ tailWord_1009621) baseStart_1009621 baseEnd_1009621 := by
    simpa [prefixWord, tailWord_1009621, baseEnd_1009621] using wordTrace_append hprefix tailTrace_1009621
  have hstable : (prefixWord ++ tailWord_1009621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009621).length < 2 ^ (prefixWord ++ tailWord_1009621).sum := by decide
  have hdescent : baseEnd_1009621 < baseStart_1009621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009631 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 3]
def baseStart_1009631 : Nat := 118140960795 + 1009631 * 2 ^ 59
def prefixEnd_1009631 : Nat := 4983230072969 + 3 ^ 40 * 1009631 * 2
def baseEnd_1009631 : Nat := 460823099270795153572709

theorem tailTrace_1009631 : CollatzResearch.WordTrace tailWord_1009631 prefixEnd_1009631 460823099270795153572709 := by
  unfold tailWord_1009631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36824267805286793091956747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24549511870191195394637831 36824267805286793091956747)
  ·
    refine ⟨55236401707930189637935121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36824267805286793091956747 55236401707930189637935121)
    ·
      refine ⟨41427301280947642228451341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55236401707930189637935121 41427301280947642228451341)
      ·
        refine ⟨15535237980355365835669253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41427301280947642228451341 15535237980355365835669253)
        ·
          refine ⟨2912857121316631094187985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15535237980355365835669253 2912857121316631094187985)
          ·
            refine ⟨2184642840987473320640989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2912857121316631094187985 2184642840987473320640989)
            ·
              refine ⟨819241065370302495240371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2184642840987473320640989 819241065370302495240371)
              ·
                refine ⟨1228861598055453742860557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819241065370302495240371 1228861598055453742860557)
                ·
                  refine ⟨460823099270795153572709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228861598055453742860557 460823099270795153572709)
                  ·
                    rfl

theorem cell20_1009631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 3].length) (baseStart_1009631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009631 prefixEnd_1009631 := by exact prefixLift 1009631
  have htrace : WordTrace (prefixWord ++ tailWord_1009631) baseStart_1009631 baseEnd_1009631 := by
    simpa [prefixWord, tailWord_1009631, baseEnd_1009631] using wordTrace_append hprefix tailTrace_1009631
  have hstable : (prefixWord ++ tailWord_1009631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009631).length < 2 ^ (prefixWord ++ tailWord_1009631).sum := by decide
  have hdescent : baseEnd_1009631 < baseStart_1009631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009690 : List Nat := [3, 1, 1, 3, 1, 4, 1, 3, 3]
def baseStart_1009690 : Nat := 118140960795 + 1009690 * 2 ^ 59
def prefixEnd_1009690 : Nat := 4983230072969 + 3 ^ 40 * 1009690 * 2
def baseEnd_1009690 : Nat := 460850028478453170605801

theorem tailTrace_1009690 : CollatzResearch.WordTrace tailWord_1009690 prefixEnd_1009690 460850028478453170605801 := by
  unfold tailWord_1009690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206604928018261542088631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24550946474715364112236349 9206604928018261542088631)
  ·
    refine ⟨13809907392027392313132947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9206604928018261542088631 13809907392027392313132947)
    ·
      refine ⟨20714861088041088469699421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13809907392027392313132947 20714861088041088469699421)
      ·
        refine ⟨7768072908015408176137283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20714861088041088469699421 7768072908015408176137283)
        ·
          refine ⟨11652109362023112264205925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768072908015408176137283 11652109362023112264205925)
          ·
            refine ⟨2184770505379333549538611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11652109362023112264205925 2184770505379333549538611)
            ·
              refine ⟨3277155758069000324307917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184770505379333549538611 3277155758069000324307917)
              ·
                refine ⟨1228933409275875121615469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3277155758069000324307917 1228933409275875121615469)
                ·
                  refine ⟨460850028478453170605801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228933409275875121615469 460850028478453170605801)
                  ·
                    rfl

theorem cell20_1009690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_1009690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009690 prefixEnd_1009690 := by exact prefixLift 1009690
  have htrace : WordTrace (prefixWord ++ tailWord_1009690) baseStart_1009690 baseEnd_1009690 := by
    simpa [prefixWord, tailWord_1009690, baseEnd_1009690] using wordTrace_append hprefix tailTrace_1009690
  have hstable : (prefixWord ++ tailWord_1009690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009690).length < 2 ^ (prefixWord ++ tailWord_1009690).sum := by decide
  have hdescent : baseEnd_1009690 < baseStart_1009690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009728 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_1009728 : Nat := 118140960795 + 1009728 * 2 ^ 59
def prefixEnd_1009728 : Nat := 4983230072969 + 3 ^ 40 * 1009728 * 2
def baseEnd_1009728 : Nat := 460867372713893927338979

theorem tailTrace_1009728 : CollatzResearch.WordTrace tailWord_1009728 prefixEnd_1009728 460867372713893927338979 := by
  unfold tailWord_1009728
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413902842967689329118919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24551870457290252438825225 18413902842967689329118919)
  ·
    refine ⟨27620854264451533993678379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18413902842967689329118919 27620854264451533993678379)
    ·
      refine ⟨41431281396677300990517569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27620854264451533993678379 41431281396677300990517569)
      ·
        refine ⟨31073461047507975742888177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41431281396677300990517569 31073461047507975742888177)
        ·
          refine ⟨23305095785630981807166133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31073461047507975742888177 23305095785630981807166133)
          ·
            refine ⟨2184852729902904544421825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23305095785630981807166133 2184852729902904544421825)
            ·
              refine ⟨1638639547427178408316369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184852729902904544421825 1638639547427178408316369)
              ·
                refine ⟨1228979660570383806237277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1638639547427178408316369 1228979660570383806237277)
                ·
                  refine ⟨460867372713893927338979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228979660570383806237277 460867372713893927338979)
                  ·
                    rfl

theorem cell20_1009728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_1009728 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009728 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009728 prefixEnd_1009728 := by exact prefixLift 1009728
  have htrace : WordTrace (prefixWord ++ tailWord_1009728) baseStart_1009728 baseEnd_1009728 := by
    simpa [prefixWord, tailWord_1009728, baseEnd_1009728] using wordTrace_append hprefix tailTrace_1009728
  have hstable : (prefixWord ++ tailWord_1009728).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009728).length < 2 ^ (prefixWord ++ tailWord_1009728).sum := by decide
  have hdescent : baseEnd_1009728 < baseStart_1009728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009742 : List Nat := [4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1009742 : Nat := 118140960795 + 1009742 * 2 ^ 59
def prefixEnd_1009742 : Nat := 4983230072969 + 3 ^ 40 * 1009742 * 2
def baseEnd_1009742 : Nat := 153624587565124033624085

theorem tailTrace_1009742 : CollatzResearch.WordTrace tailWord_1009742 prefixEnd_1009742 153624587565124033624085 := by
  unfold tailWord_1009742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603539538485582381155935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24552210871923106032831653 4603539538485582381155935)
  ·
    refine ⟨6905309307728373571733903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4603539538485582381155935 6905309307728373571733903)
    ·
      refine ⟨10357963961592560357600855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6905309307728373571733903 10357963961592560357600855)
      ·
        refine ⟨15536945942388840536401283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357963961592560357600855 15536945942388840536401283)
        ·
          refine ⟨23305418913583260804601925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15536945942388840536401283 23305418913583260804601925)
          ·
            refine ⟨4369766046296861400862861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23305418913583260804601925 4369766046296861400862861)
            ·
              refine ⟨1638662267361323025323573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4369766046296861400862861 1638662267361323025323573)
              ·
                refine ⟨153624587565124033624085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1638662267361323025323573 153624587565124033624085)
                ·
                  rfl

theorem cell20_1009742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1009742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009742 prefixEnd_1009742 := by exact prefixLift 1009742
  have htrace : WordTrace (prefixWord ++ tailWord_1009742) baseStart_1009742 baseEnd_1009742 := by
    simpa [prefixWord, tailWord_1009742, baseEnd_1009742] using wordTrace_append hprefix tailTrace_1009742
  have hstable : (prefixWord ++ tailWord_1009742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009742).length < 2 ^ (prefixWord ++ tailWord_1009742).sum := by decide
  have hdescent : baseEnd_1009742 < baseStart_1009742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009763 : List Nat := [1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_1009763 : Nat := 118140960795 + 1009763 * 2 ^ 59
def prefixEnd_1009763 : Nat := 4983230072969 + 3 ^ 40 * 1009763 * 2
def baseEnd_1009763 : Nat := 153627782555863120390723

theorem tailTrace_1009763 : CollatzResearch.WordTrace tailWord_1009763 prefixEnd_1009763 153627782555863120390723 := by
  unfold tailWord_1009763
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829082240808579635761943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24552721493872386423841295 36829082240808579635761943)
  ·
    refine ⟨55243623361212869453642915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829082240808579635761943 55243623361212869453642915)
    ·
      refine ⟨82865435041819304180464373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55243623361212869453642915 82865435041819304180464373)
      ·
        refine ⟨7768634535170559766918535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82865435041819304180464373 7768634535170559766918535)
        ·
          refine ⟨11652951802755839650377803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768634535170559766918535 11652951802755839650377803)
          ·
            refine ⟨17479427704133759475566705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652951802755839650377803 17479427704133759475566705)
            ·
              refine ⟨13109570778100319606675029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17479427704133759475566705 13109570778100319606675029)
              ·
                refine ⟨153627782555863120390723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13109570778100319606675029 153627782555863120390723)
                ·
                  rfl

theorem cell20_1009763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_1009763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009763 prefixEnd_1009763 := by exact prefixLift 1009763
  have htrace : WordTrace (prefixWord ++ tailWord_1009763) baseStart_1009763 baseEnd_1009763 := by
    simpa [prefixWord, tailWord_1009763, baseEnd_1009763] using wordTrace_append hprefix tailTrace_1009763
  have hstable : (prefixWord ++ tailWord_1009763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009763).length < 2 ^ (prefixWord ++ tailWord_1009763).sum := by decide
  have hdescent : baseEnd_1009763 < baseStart_1009763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009801 : List Nat := [1, 2, 1, 1, 4, 2, 2, 7]
def baseStart_1009801 : Nat := 118140960795 + 1009801 * 2 ^ 59
def prefixEnd_1009801 : Nat := 4983230072969 + 3 ^ 40 * 1009801 * 2
def baseEnd_1009801 : Nat := 153633563967676705968449

theorem tailTrace_1009801 : CollatzResearch.WordTrace tailWord_1009801 prefixEnd_1009801 153633563967676705968449 := by
  unfold tailWord_1009801
  simp only [CollatzResearch.WordTrace]
  refine ⟨36830468214670912125645257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24553645476447274750430171 36830468214670912125645257)
  ·
    refine ⟨27622851161003184094233943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36830468214670912125645257 27622851161003184094233943)
    ·
      refine ⟨41434276741504776141350915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27622851161003184094233943 41434276741504776141350915)
      ·
        refine ⟨62151415112257164212026373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41434276741504776141350915 62151415112257164212026373)
        ·
          refine ⟨11653390333548218289754945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62151415112257164212026373 11653390333548218289754945)
          ·
            refine ⟨8740042750161163717316209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653390333548218289754945 8740042750161163717316209)
            ·
              refine ⟨6555032062620872787987157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8740042750161163717316209 6555032062620872787987157)
              ·
                refine ⟨153633563967676705968449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6555032062620872787987157 153633563967676705968449)
                ·
                  rfl

theorem cell20_1009801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 7].length) (baseStart_1009801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009801 prefixEnd_1009801 := by exact prefixLift 1009801
  have htrace : WordTrace (prefixWord ++ tailWord_1009801) baseStart_1009801 baseEnd_1009801 := by
    simpa [prefixWord, tailWord_1009801, baseEnd_1009801] using wordTrace_append hprefix tailTrace_1009801
  have hstable : (prefixWord ++ tailWord_1009801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009801).length < 2 ^ (prefixWord ++ tailWord_1009801).sum := by decide
  have hdescent : baseEnd_1009801 < baseStart_1009801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009825 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 5]
def baseStart_1009825 : Nat := 118140960795 + 1009825 * 2 ^ 59
def prefixEnd_1009825 : Nat := 4983230072969 + 3 ^ 40 * 1009825 * 2
def baseEnd_1009825 : Nat := 460911646156992701105249

theorem tailTrace_1009825 : CollatzResearch.WordTrace tailWord_1009825 prefixEnd_1009825 460911646156992701105249 := by
  unfold tailWord_1009825
  simp only [CollatzResearch.WordTrace]
  refine ⟨36831343566583964224518929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24554229044389309483012619 36831343566583964224518929)
  ·
    refine ⟨27623507674937973168389197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36831343566583964224518929 27623507674937973168389197)
    ·
      refine ⟨10358815378101739938145949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27623507674937973168389197 10358815378101739938145949)
      ·
        refine ⟨3884555766788152476804731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10358815378101739938145949 3884555766788152476804731)
        ·
          refine ⟨5826833650182228715207097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884555766788152476804731 5826833650182228715207097)
          ·
            refine ⟨4370125237636671536405323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5826833650182228715207097 4370125237636671536405323)
            ·
              refine ⟨6555187856455007304607985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4370125237636671536405323 6555187856455007304607985)
              ·
                refine ⟨4916390892341255478455989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6555187856455007304607985 4916390892341255478455989)
                ·
                  refine ⟨460911646156992701105249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916390892341255478455989 460911646156992701105249)
                  ·
                    rfl

theorem cell20_1009825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_1009825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009825 prefixEnd_1009825 := by exact prefixLift 1009825
  have htrace : WordTrace (prefixWord ++ tailWord_1009825) baseStart_1009825 baseEnd_1009825 := by
    simpa [prefixWord, tailWord_1009825, baseEnd_1009825] using wordTrace_append hprefix tailTrace_1009825
  have hstable : (prefixWord ++ tailWord_1009825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009825).length < 2 ^ (prefixWord ++ tailWord_1009825).sum := by decide
  have hdescent : baseEnd_1009825 < baseStart_1009825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009845 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 4]
def baseStart_1009845 : Nat := 118140960795 + 1009845 * 2 ^ 59
def prefixEnd_1009845 : Nat := 4983230072969 + 3 ^ 40 * 1009845 * 2
def baseEnd_1009845 : Nat := 460920774701961520438501

theorem tailTrace_1009845 : CollatzResearch.WordTrace tailWord_1009845 prefixEnd_1009845 460920774701961520438501 := by
  unfold tailWord_1009845
  simp only [CollatzResearch.WordTrace]
  refine ⟨36832073026511507640246989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24554715351007671760164659 36832073026511507640246989)
  ·
    refine ⟨13812027384941815365092621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36832073026511507640246989 13812027384941815365092621)
    ·
      refine ⟨5179510269353180761909733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13812027384941815365092621 5179510269353180761909733)
      ·
        refine ⟨971158175503721392858075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5179510269353180761909733 971158175503721392858075)
        ·
          refine ⟨1456737263255582089287113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971158175503721392858075 1456737263255582089287113)
          ·
            refine ⟨1092552947441686566965335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1456737263255582089287113 1092552947441686566965335)
            ·
              refine ⟨1638829421162529850448003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092552947441686566965335 1638829421162529850448003)
              ·
                refine ⟨2458244131743794775672005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1638829421162529850448003 2458244131743794775672005)
                ·
                  refine ⟨460920774701961520438501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458244131743794775672005 460920774701961520438501)
                  ·
                    rfl

theorem cell20_1009845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 4].length) (baseStart_1009845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009845 prefixEnd_1009845 := by exact prefixLift 1009845
  have htrace : WordTrace (prefixWord ++ tailWord_1009845) baseStart_1009845 baseEnd_1009845 := by
    simpa [prefixWord, tailWord_1009845, baseEnd_1009845] using wordTrace_append hprefix tailTrace_1009845
  have hstable : (prefixWord ++ tailWord_1009845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009845).length < 2 ^ (prefixWord ++ tailWord_1009845).sum := by decide
  have hdescent : baseEnd_1009845 < baseStart_1009845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009856 : List Nat := [2, 1, 1, 2, 5, 2, 2, 5]
def baseStart_1009856 : Nat := 118140960795 + 1009856 * 2 ^ 59
def prefixEnd_1009856 : Nat := 4983230072969 + 3 ^ 40 * 1009856 * 2
def baseEnd_1009856 : Nat := 153641931800564790357263

theorem tailTrace_1009856 : CollatzResearch.WordTrace tailWord_1009856 prefixEnd_1009856 153641931800564790357263 := by
  unfold tailWord_1009856
  simp only [CollatzResearch.WordTrace]
  refine ⟨18416237114735828259448711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24554982819647771012598281 18416237114735828259448711)
  ·
    refine ⟨27624355672103742389173067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18416237114735828259448711 27624355672103742389173067)
    ·
      refine ⟨41436533508155613583759601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27624355672103742389173067 41436533508155613583759601)
      ·
        refine ⟨31077400131116710187819701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41436533508155613583759601 31077400131116710187819701)
        ·
          refine ⟨2913506262292191580108097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31077400131116710187819701 2913506262292191580108097)
          ·
            refine ⟨2185129696719143685081073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913506262292191580108097 2185129696719143685081073)
            ·
              refine ⟨1638847272539357763810805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2185129696719143685081073 1638847272539357763810805)
              ·
                refine ⟨153641931800564790357263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1638847272539357763810805 153641931800564790357263)
                ·
                  rfl

theorem cell20_1009856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 5].length) (baseStart_1009856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009856 prefixEnd_1009856 := by exact prefixLift 1009856
  have htrace : WordTrace (prefixWord ++ tailWord_1009856) baseStart_1009856 baseEnd_1009856 := by
    simpa [prefixWord, tailWord_1009856, baseEnd_1009856] using wordTrace_append hprefix tailTrace_1009856
  have hstable : (prefixWord ++ tailWord_1009856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009856).length < 2 ^ (prefixWord ++ tailWord_1009856).sum := by decide
  have hdescent : baseEnd_1009856 < baseStart_1009856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009887 : List Nat := [1, 1, 2, 3, 2, 1, 1, 7, 2]
def baseStart_1009887 : Nat := 118140960795 + 1009887 * 2 ^ 59
def prefixEnd_1009887 : Nat := 4983230072969 + 3 ^ 40 * 1009887 * 2
def baseEnd_1009887 : Nat := 460939944646396041038329

theorem tailTrace_1009887 : CollatzResearch.WordTrace tailWord_1009887 prefixEnd_1009887 460939944646396041038329 := by
  unfold tailWord_1009887
  simp only [CollatzResearch.WordTrace]
  refine ⟨36833604892359348813275915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24555736594906232542183943 36833604892359348813275915)
  ·
    refine ⟨55250407338539023219913873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36833604892359348813275915 55250407338539023219913873)
    ·
      refine ⟨41437805503904267414935405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55250407338539023219913873 41437805503904267414935405)
      ·
        refine ⟨15539177063964100280600777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41437805503904267414935405 15539177063964100280600777)
        ·
          refine ⟨11654382797973075210450583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15539177063964100280600777 11654382797973075210450583)
          ·
            refine ⟨17481574196959612815675875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11654382797973075210450583 17481574196959612815675875)
            ·
              refine ⟨26222361295439419223513813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17481574196959612815675875 26222361295439419223513813)
              ·
                refine ⟨614586592861861388051105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26222361295439419223513813 614586592861861388051105)
                ·
                  refine ⟨460939944646396041038329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614586592861861388051105 460939944646396041038329)
                  ·
                    rfl

theorem cell20_1009887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2].length) (baseStart_1009887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009887 prefixEnd_1009887 := by exact prefixLift 1009887
  have htrace : WordTrace (prefixWord ++ tailWord_1009887) baseStart_1009887 baseEnd_1009887 := by
    simpa [prefixWord, tailWord_1009887, baseEnd_1009887] using wordTrace_append hprefix tailTrace_1009887
  have hstable : (prefixWord ++ tailWord_1009887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009887).length < 2 ^ (prefixWord ++ tailWord_1009887).sum := by decide
  have hdescent : baseEnd_1009887 < baseStart_1009887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009890 : List Nat := [3, 3, 4, 1, 1, 8]
def baseStart_1009890 : Nat := 118140960795 + 1009890 * 2 ^ 59
def prefixEnd_1009890 : Nat := 4983230072969 + 3 ^ 40 * 1009890 * 2
def baseEnd_1009890 : Nat := 17071900515857087553271

theorem tailTrace_1009890 : CollatzResearch.WordTrace tailWord_1009890 prefixEnd_1009890 17071900515857087553271 := by
  unfold tailWord_1009890
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208428577837120081408781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24555809540898986883756749 9208428577837120081408781)
  ·
    refine ⟨3453160716688920030528293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9208428577837120081408781 3453160716688920030528293)
    ·
      refine ⟨647467634379172505724055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3453160716688920030528293 647467634379172505724055)
      ·
        refine ⟨971201451568758758586083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647467634379172505724055 971201451568758758586083)
        ·
          refine ⟨1456802177353138137879125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971201451568758758586083 1456802177353138137879125)
          ·
            refine ⟨17071900515857087553271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1456802177353138137879125 17071900515857087553271)
            ·
              rfl

theorem cell20_1009890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 8].length) (baseStart_1009890 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009890 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009890 prefixEnd_1009890 := by exact prefixLift 1009890
  have htrace : WordTrace (prefixWord ++ tailWord_1009890) baseStart_1009890 baseEnd_1009890 := by
    simpa [prefixWord, tailWord_1009890, baseEnd_1009890] using wordTrace_append hprefix tailTrace_1009890
  have hstable : (prefixWord ++ tailWord_1009890).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009890).length < 2 ^ (prefixWord ++ tailWord_1009890).sum := by decide
  have hdescent : baseEnd_1009890 < baseStart_1009890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009918 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1009918 : Nat := 118140960795 + 1009918 * 2 ^ 59
def prefixEnd_1009918 : Nat := 4983230072969 + 3 ^ 40 * 1009918 * 2
def baseEnd_1009918 : Nat := 460954093891097711004869

theorem tailTrace_1009918 : CollatzResearch.WordTrace tailWord_1009918 prefixEnd_1009918 460954093891097711004869 := by
  unfold tailWord_1009918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604341944405880138456801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24556490370164694071769605 4604341944405880138456801)
  ·
    refine ⟨3453256458304410103842601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4604341944405880138456801 3453256458304410103842601)
    ·
      refine ⟨2589942343728307577881951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453256458304410103842601 2589942343728307577881951)
      ·
        refine ⟨3884913515592461366822927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589942343728307577881951 3884913515592461366822927)
        ·
          refine ⟨5827370273388692050234391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3884913515592461366822927 5827370273388692050234391)
          ·
            refine ⟨8741055410083038075351587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5827370273388692050234391 8741055410083038075351587)
            ·
              refine ⟨13111583115124557113027381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8741055410083038075351587 13111583115124557113027381)
              ·
                refine ⟨1229210917042927229346317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13111583115124557113027381 1229210917042927229346317)
                ·
                  refine ⟨460954093891097711004869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229210917042927229346317 460954093891097711004869)
                  ·
                    rfl

theorem cell20_1009918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1009918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009918 prefixEnd_1009918 := by exact prefixLift 1009918
  have htrace : WordTrace (prefixWord ++ tailWord_1009918) baseStart_1009918 baseEnd_1009918 := by
    simpa [prefixWord, tailWord_1009918, baseEnd_1009918] using wordTrace_append hprefix tailTrace_1009918
  have hstable : (prefixWord ++ tailWord_1009918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009918).length < 2 ^ (prefixWord ++ tailWord_1009918).sum := by decide
  have hdescent : baseEnd_1009918 < baseStart_1009918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009932 : List Nat := [2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_1009932 : Nat := 118140960795 + 1009932 * 2 ^ 59
def prefixEnd_1009932 : Nat := 4983230072969 + 3 ^ 40 * 1009932 * 2
def baseEnd_1009932 : Nat := 153653494624191961512715

theorem tailTrace_1009932 : CollatzResearch.WordTrace tailWord_1009932 prefixEnd_1009932 153653494624191961512715 := by
  unfold tailWord_1009932
  simp only [CollatzResearch.WordTrace]
  refine ⟨18417623088598160749332025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24556830784797547665776033 18417623088598160749332025)
  ·
    refine ⟨13813217316448620561999019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18417623088598160749332025 13813217316448620561999019)
    ·
      refine ⟨20719825974672930842998529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13813217316448620561999019 20719825974672930842998529)
      ·
        refine ⟨15539869481004698132248897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20719825974672930842998529 15539869481004698132248897)
        ·
          refine ⟨11654902110753523599186673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15539869481004698132248897 11654902110753523599186673)
          ·
            refine ⟨8741176583065142699390005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11654902110753523599186673 8741176583065142699390005)
            ·
              refine ⟨819485304662357128067813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8741176583065142699390005 819485304662357128067813)
              ·
                refine ⟨153653494624191961512715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 819485304662357128067813 153653494624191961512715)
                ·
                  rfl

theorem cell20_1009932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_1009932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009932 prefixEnd_1009932 := by exact prefixLift 1009932
  have htrace : WordTrace (prefixWord ++ tailWord_1009932) baseStart_1009932 baseEnd_1009932 := by
    simpa [prefixWord, tailWord_1009932, baseEnd_1009932] using wordTrace_append hprefix tailTrace_1009932
  have hstable : (prefixWord ++ tailWord_1009932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009932).length < 2 ^ (prefixWord ++ tailWord_1009932).sum := by decide
  have hdescent : baseEnd_1009932 < baseStart_1009932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009956 : List Nat := [2, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_1009956 : Nat := 118140960795 + 1009956 * 2 ^ 59
def prefixEnd_1009956 : Nat := 4983230072969 + 3 ^ 40 * 1009956 * 2
def baseEnd_1009956 : Nat := 460971438126538467738047

theorem tailTrace_1009956 : CollatzResearch.WordTrace tailWord_1009956 prefixEnd_1009956 460971438126538467738047 := by
  unfold tailWord_1009956
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418060764554686798768861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24557414352739582398358481 18418060764554686798768861)
  ·
    refine ⟨6906772786708007549538323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18418060764554686798768861 6906772786708007549538323)
    ·
      refine ⟨10360159180062011324307485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6906772786708007549538323 10360159180062011324307485)
      ·
        refine ⟨3885059692523254246615307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10360159180062011324307485 3885059692523254246615307)
        ·
          refine ⟨5827589538784881369922961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885059692523254246615307 5827589538784881369922961)
          ·
            refine ⟨4370692154088661027442221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827589538784881369922961 4370692154088661027442221)
            ·
              refine ⟨1639009557783247885290833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4370692154088661027442221 1639009557783247885290833)
              ·
                refine ⟨1229257168337435913968125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639009557783247885290833 1229257168337435913968125)
                ·
                  refine ⟨460971438126538467738047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229257168337435913968125 460971438126538467738047)
                  ·
                    rfl

theorem cell20_1009956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_1009956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009956 prefixEnd_1009956 := by exact prefixLift 1009956
  have htrace : WordTrace (prefixWord ++ tailWord_1009956) baseStart_1009956 baseEnd_1009956 := by
    simpa [prefixWord, tailWord_1009956, baseEnd_1009956] using wordTrace_append hprefix tailTrace_1009956
  have hstable : (prefixWord ++ tailWord_1009956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009956).length < 2 ^ (prefixWord ++ tailWord_1009956).sum := by decide
  have hdescent : baseEnd_1009956 < baseStart_1009956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1009991 : List Nat := [1, 1, 4, 1, 2, 2, 3, 6]
def baseStart_1009991 : Nat := 118140960795 + 1009991 * 2 ^ 59
def prefixEnd_1009991 : Nat := 4983230072969 + 3 ^ 40 * 1009991 * 2
def baseEnd_1009991 : Nat := 153662471026744633857079

theorem tailTrace_1009991 : CollatzResearch.WordTrace tailWord_1009991 prefixEnd_1009991 153662471026744633857079 := by
  unfold tailWord_1009991
  simp only [CollatzResearch.WordTrace]
  refine ⟨36837398083982574575061827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24558265389321716383374551 36837398083982574575061827)
  ·
    refine ⟨55256097125973861862592741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36837398083982574575061827 55256097125973861862592741)
    ·
      refine ⟨10360518211120099099236139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55256097125973861862592741 10360518211120099099236139)
      ·
        refine ⟨15540777316680148648854209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10360518211120099099236139 15540777316680148648854209)
        ·
          refine ⟨11655582987510111486640657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15540777316680148648854209 11655582987510111486640657)
          ·
            refine ⟨8741687240632583614980493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11655582987510111486640657 8741687240632583614980493)
            ·
              refine ⟨3278132715237218855617685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8741687240632583614980493 3278132715237218855617685)
              ·
                refine ⟨153662471026744633857079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3278132715237218855617685 153662471026744633857079)
                ·
                  rfl

theorem cell20_1009991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 6].length) (baseStart_1009991 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1009991 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1009991 prefixEnd_1009991 := by exact prefixLift 1009991
  have htrace : WordTrace (prefixWord ++ tailWord_1009991) baseStart_1009991 baseEnd_1009991 := by
    simpa [prefixWord, tailWord_1009991, baseEnd_1009991] using wordTrace_append hprefix tailTrace_1009991
  have hstable : (prefixWord ++ tailWord_1009991).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1009991).length < 2 ^ (prefixWord ++ tailWord_1009991).sum := by decide
  have hdescent : baseEnd_1009991 < baseStart_1009991 := by decide
  rcases family_descends (prefixWord ++ tailWord_1009991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010018 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 4]
def baseStart_1010018 : Nat := 118140960795 + 1010018 * 2 ^ 59
def prefixEnd_1010018 : Nat := 4983230072969 + 3 ^ 40 * 1010018 * 2
def baseEnd_1010018 : Nat := 460999736615941807671127

theorem tailTrace_1010018 : CollatzResearch.WordTrace tailWord_1010018 prefixEnd_1010018 460999736615941807671127 := by
  unfold tailWord_1010018
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209595713721189546573677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24558921903256505457529805 9209595713721189546573677)
  ·
    refine ⟨3453598392645446079965129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9209595713721189546573677 3453598392645446079965129)
    ·
      refine ⟨2590198794484084559973847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453598392645446079965129 2590198794484084559973847)
      ·
        refine ⟨3885298191726126839960771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590198794484084559973847 3885298191726126839960771)
        ·
          refine ⟨5827947287589190259941157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885298191726126839960771 5827947287589190259941157)
          ·
            refine ⟨1092740116422973173738967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5827947287589190259941157 1092740116422973173738967)
            ·
              refine ⟨1639110174634459760608451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092740116422973173738967 1639110174634459760608451)
              ·
                refine ⟨2458665261951689640912677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639110174634459760608451 2458665261951689640912677)
                ·
                  refine ⟨460999736615941807671127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458665261951689640912677 460999736615941807671127)
                  ·
                    rfl

theorem cell20_1010018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_1010018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010018 prefixEnd_1010018 := by exact prefixLift 1010018
  have htrace : WordTrace (prefixWord ++ tailWord_1010018) baseStart_1010018 baseEnd_1010018 := by
    simpa [prefixWord, tailWord_1010018, baseEnd_1010018] using wordTrace_append hprefix tailTrace_1010018
  have hstable : (prefixWord ++ tailWord_1010018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010018).length < 2 ^ (prefixWord ++ tailWord_1010018).sum := by decide
  have hdescent : baseEnd_1010018 < baseStart_1010018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010028 : List Nat := [2, 2, 1, 1, 7, 1, 2, 1, 3]
def baseStart_1010028 : Nat := 118140960795 + 1010028 * 2 ^ 59
def prefixEnd_1010028 : Nat := 4983230072969 + 3 ^ 40 * 1010028 * 2
def baseEnd_1010028 : Nat := 461004300888426217337753

theorem tailTrace_1010028 : CollatzResearch.WordTrace tailWord_1010028 prefixEnd_1010028 461004300888426217337753 := by
  unfold tailWord_1010028
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419373792424264947079369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24559165056565686596105825 18419373792424264947079369)
  ·
    refine ⟨13814530344318198710309527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18419373792424264947079369 13814530344318198710309527)
    ·
      refine ⟨20721795516477298065464291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814530344318198710309527 20721795516477298065464291)
      ·
        refine ⟨31082693274715947098196437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20721795516477298065464291 31082693274715947098196437)
        ·
          refine ⟨728500623626155010113979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 31082693274715947098196437 728500623626155010113979)
          ·
            refine ⟨1092750935439232515170969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728500623626155010113979 1092750935439232515170969)
            ·
              refine ⟨819563201579424386378227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092750935439232515170969 819563201579424386378227)
              ·
                refine ⟨1229344802369136579567341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819563201579424386378227 1229344802369136579567341)
                ·
                  refine ⟨461004300888426217337753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229344802369136579567341 461004300888426217337753)
                  ·
                    rfl

theorem cell20_1010028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 1, 3].length) (baseStart_1010028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010028 prefixEnd_1010028 := by exact prefixLift 1010028
  have htrace : WordTrace (prefixWord ++ tailWord_1010028) baseStart_1010028 baseEnd_1010028 := by
    simpa [prefixWord, tailWord_1010028, baseEnd_1010028] using wordTrace_append hprefix tailTrace_1010028
  have hstable : (prefixWord ++ tailWord_1010028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010028).length < 2 ^ (prefixWord ++ tailWord_1010028).sum := by decide
  have hdescent : baseEnd_1010028 < baseStart_1010028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010032 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 3]
def baseStart_1010032 : Nat := 118140960795 + 1010032 * 2 ^ 59
def prefixEnd_1010032 : Nat := 4983230072969 + 3 ^ 40 * 1010032 * 2
def baseEnd_1010032 : Nat := 461006126597419981204403

theorem tailTrace_1010032 : CollatzResearch.WordTrace tailWord_1010032 prefixEnd_1010032 461006126597419981204403 := by
  unfold tailWord_1010032
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419446738417019288652175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24559262317889359051536233 18419446738417019288652175)
  ·
    refine ⟨27629170107625528932978263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18419446738417019288652175 27629170107625528932978263)
    ·
      refine ⟨41443755161438293399467395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27629170107625528932978263 41443755161438293399467395)
      ·
        refine ⟨62165632742157440099201093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41443755161438293399467395 62165632742157440099201093)
        ·
          refine ⟨11656056139154520018600205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62165632742157440099201093 11656056139154520018600205)
          ·
            refine ⟨4371021052182945006975077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11656056139154520018600205 4371021052182945006975077)
            ·
              refine ⟨819566447284302188807827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4371021052182945006975077 819566447284302188807827)
              ·
                refine ⟨1229349670926453283211741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819566447284302188807827 1229349670926453283211741)
                ·
                  refine ⟨461006126597419981204403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229349670926453283211741 461006126597419981204403)
                  ·
                    rfl

theorem cell20_1010032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 3].length) (baseStart_1010032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010032 prefixEnd_1010032 := by exact prefixLift 1010032
  have htrace : WordTrace (prefixWord ++ tailWord_1010032) baseStart_1010032 baseEnd_1010032 := by
    simpa [prefixWord, tailWord_1010032, baseEnd_1010032] using wordTrace_append hprefix tailTrace_1010032
  have hstable : (prefixWord ++ tailWord_1010032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010032).length < 2 ^ (prefixWord ++ tailWord_1010032).sum := by decide
  have hdescent : baseEnd_1010032 < baseStart_1010032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010098 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_1010098 : Nat := 118140960795 + 1010098 * 2 ^ 59
def prefixEnd_1010098 : Nat := 4983230072969 + 3 ^ 40 * 1010098 * 2
def baseEnd_1010098 : Nat := 461036250795817085004133

theorem tailTrace_1010098 : CollatzResearch.WordTrace tailWord_1010098 prefixEnd_1010098 461036250795817085004133 := by
  unfold tailWord_1010098
  simp only [CollatzResearch.WordTrace]
  refine ⟨9210325173648732962301737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24560867129729954566137965 9210325173648732962301737)
  ·
    refine ⟨6907743880236549721726303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9210325173648732962301737 6907743880236549721726303)
    ·
      refine ⟨10361615820354824582589455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907743880236549721726303 10361615820354824582589455)
      ·
        refine ⟨15542423730532236873884183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10361615820354824582589455 15542423730532236873884183)
        ·
          refine ⟨23313635595798355310826275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15542423730532236873884183 23313635595798355310826275)
          ·
            refine ⟨34970453393697532966239413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23313635595798355310826275 34970453393697532966239413)
            ·
              refine ⟨3278480005659143715584945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34970453393697532966239413 3278480005659143715584945)
              ·
                refine ⟨2458860004244357786688709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278480005659143715584945 2458860004244357786688709)
                ·
                  refine ⟨461036250795817085004133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2458860004244357786688709 461036250795817085004133)
                  ·
                    rfl

theorem cell20_1010098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_1010098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010098 prefixEnd_1010098 := by exact prefixLift 1010098
  have htrace : WordTrace (prefixWord ++ tailWord_1010098) baseStart_1010098 baseEnd_1010098 := by
    simpa [prefixWord, tailWord_1010098, baseEnd_1010098] using wordTrace_append hprefix tailTrace_1010098
  have hstable : (prefixWord ++ tailWord_1010098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010098).length < 2 ^ (prefixWord ++ tailWord_1010098).sum := by decide
  have hdescent : baseEnd_1010098 < baseStart_1010098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010101 : List Nat := [1, 3, 3, 2, 3, 1, 3, 4]
def baseStart_1010101 : Nat := 118140960795 + 1010101 * 2 ^ 59
def prefixEnd_1010101 : Nat := 4983230072969 + 3 ^ 40 * 1010101 * 2
def baseEnd_1010101 : Nat := 153679206692520802634707

theorem tailTrace_1010101 : CollatzResearch.WordTrace tailWord_1010101 prefixEnd_1010101 153679206692520802634707 := by
  unfold tailWord_1010101
  simp only [CollatzResearch.WordTrace]
  refine ⟨36841410113584063361566157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24560940075722708907710771 36841410113584063361566157)
  ·
    refine ⟨13815528792594023760587309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36841410113584063361566157 13815528792594023760587309)
    ·
      refine ⟨5180823297222758910220241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13815528792594023760587309 5180823297222758910220241)
      ·
        refine ⟨3885617472917069182665181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5180823297222758910220241 3885617472917069182665181)
        ·
          refine ⟨1457106552343900943499443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3885617472917069182665181 1457106552343900943499443)
          ·
            refine ⟨2185659828515851415249165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457106552343900943499443 2185659828515851415249165)
            ·
              refine ⟨819622435693444280718437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2185659828515851415249165 819622435693444280718437)
              ·
                refine ⟨153679206692520802634707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 819622435693444280718437 153679206692520802634707)
                ·
                  rfl

theorem cell20_1010101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 4].length) (baseStart_1010101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010101 prefixEnd_1010101 := by exact prefixLift 1010101
  have htrace : WordTrace (prefixWord ++ tailWord_1010101) baseStart_1010101 baseEnd_1010101 := by
    simpa [prefixWord, tailWord_1010101, baseEnd_1010101] using wordTrace_append hprefix tailTrace_1010101
  have hstable : (prefixWord ++ tailWord_1010101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010101).length < 2 ^ (prefixWord ++ tailWord_1010101).sum := by decide
  have hdescent : baseEnd_1010101 < baseStart_1010101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010112 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_1010112 : Nat := 118140960795 + 1010112 * 2 ^ 59
def prefixEnd_1010112 : Nat := 4983230072969 + 3 ^ 40 * 1010112 * 2
def baseEnd_1010112 : Nat := 461042640777295258537409

theorem tailTrace_1010112 : CollatzResearch.WordTrace tailWord_1010112 prefixEnd_1010112 461042640777295258537409 := by
  unfold tailWord_1010112
  simp only [CollatzResearch.WordTrace]
  refine ⟨18420905658272106120108295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24561207544362808160144393 18420905658272106120108295)
  ·
    refine ⟨27631358487408159180162443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18420905658272106120108295 27631358487408159180162443)
    ·
      refine ⟨41447037731112238770243665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27631358487408159180162443 41447037731112238770243665)
      ·
        refine ⟨31085278298334179077682749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41447037731112238770243665 31085278298334179077682749)
        ·
          refine ⟨11656979361875317154131031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31085278298334179077682749 11656979361875317154131031)
          ·
            refine ⟨17485469042812975731196547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11656979361875317154131031 17485469042812975731196547)
            ·
              refine ⟨26228203564219463596794821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17485469042812975731196547 26228203564219463596794821)
              ·
                refine ⟨4917788168291149424399029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26228203564219463596794821 4917788168291149424399029)
                ·
                  refine ⟨461042640777295258537409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4917788168291149424399029 461042640777295258537409)
                  ·
                    rfl

theorem cell20_1010112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_1010112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010112 prefixEnd_1010112 := by exact prefixLift 1010112
  have htrace : WordTrace (prefixWord ++ tailWord_1010112) baseStart_1010112 baseEnd_1010112 := by
    simpa [prefixWord, tailWord_1010112, baseEnd_1010112] using wordTrace_append hprefix tailTrace_1010112
  have hstable : (prefixWord ++ tailWord_1010112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010112).length < 2 ^ (prefixWord ++ tailWord_1010112).sum := by decide
  have hdescent : baseEnd_1010112 < baseStart_1010112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010132 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_1010132 : Nat := 118140960795 + 1010132 * 2 ^ 59
def prefixEnd_1010132 : Nat := 4983230072969 + 3 ^ 40 * 1010132 * 2
def baseEnd_1010132 : Nat := 461051769322264077870661

theorem tailTrace_1010132 : CollatzResearch.WordTrace tailWord_1010132 prefixEnd_1010132 461051769322264077870661 := by
  unfold tailWord_1010132
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421270388235877827972325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24561693850981170437296433 18421270388235877827972325)
  ·
    refine ⟨3453988197794227092744811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18421270388235877827972325 3453988197794227092744811)
    ·
      refine ⟨5180982296691340639117217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453988197794227092744811 5180982296691340639117217)
      ·
        refine ⟨3885736722518505479337913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5180982296691340639117217 3885736722518505479337913)
        ·
          refine ⟨2914302541888879109503435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3885736722518505479337913 2914302541888879109503435)
          ·
            refine ⟨4371453812833318664255153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914302541888879109503435 4371453812833318664255153)
            ·
              refine ⟨3278590359624988998191365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4371453812833318664255153 3278590359624988998191365)
              ·
                refine ⟨614735692429685437160881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3278590359624988998191365 614735692429685437160881)
                ·
                  refine ⟨461051769322264077870661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614735692429685437160881 461051769322264077870661)
                  ·
                    rfl

theorem cell20_1010132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_1010132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010132 prefixEnd_1010132 := by exact prefixLift 1010132
  have htrace : WordTrace (prefixWord ++ tailWord_1010132) baseStart_1010132 baseEnd_1010132 := by
    simpa [prefixWord, tailWord_1010132, baseEnd_1010132] using wordTrace_append hprefix tailTrace_1010132
  have hstable : (prefixWord ++ tailWord_1010132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010132).length < 2 ^ (prefixWord ++ tailWord_1010132).sum := by decide
  have hdescent : baseEnd_1010132 < baseStart_1010132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010226 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_1010226 : Nat := 118140960795 + 1010226 * 2 ^ 59
def prefixEnd_1010226 : Nat := 4983230072969 + 3 ^ 40 * 1010226 * 2
def baseEnd_1010226 : Nat := 461094673483617528736943

theorem tailTrace_1010226 : CollatzResearch.WordTrace tailWord_1010226 prefixEnd_1010226 461094673483617528736943 := by
  unfold tailWord_1010226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9211492309532802427466633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24563979492087473139911021 9211492309532802427466633)
  ·
    refine ⟨6908619232149601820599975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9211492309532802427466633 6908619232149601820599975)
    ·
      refine ⟨10362928848224402730899963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6908619232149601820599975 10362928848224402730899963)
      ·
        refine ⟨15544393272336604096349945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10362928848224402730899963 15544393272336604096349945)
        ·
          refine ⟨11658294954252453072262459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15544393272336604096349945 11658294954252453072262459)
          ·
            refine ⟨17487442431378679608393689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11658294954252453072262459 17487442431378679608393689)
            ·
              refine ⟨13115581823534009706295267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17487442431378679608393689 13115581823534009706295267)
              ·
                refine ⟨19673372735301014559442901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13115581823534009706295267 19673372735301014559442901)
                ·
                  refine ⟨461094673483617528736943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19673372735301014559442901 461094673483617528736943)
                  ·
                    rfl

theorem cell20_1010226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_1010226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010226 prefixEnd_1010226 := by exact prefixLift 1010226
  have htrace : WordTrace (prefixWord ++ tailWord_1010226) baseStart_1010226 baseEnd_1010226 := by
    simpa [prefixWord, tailWord_1010226, baseEnd_1010226] using wordTrace_append hprefix tailTrace_1010226
  have hstable : (prefixWord ++ tailWord_1010226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010226).length < 2 ^ (prefixWord ++ tailWord_1010226).sum := by decide
  have hdescent : baseEnd_1010226 < baseStart_1010226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010229 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 2]
def baseStart_1010229 : Nat := 118140960795 + 1010229 * 2 ^ 59
def prefixEnd_1010229 : Nat := 4983230072969 + 3 ^ 40 * 1010229 * 2
def baseEnd_1010229 : Nat := 461096042765362851636931

theorem tailTrace_1010229 : CollatzResearch.WordTrace tailWord_1010229 prefixEnd_1010229 461096042765362851636931 := by
  unfold tailWord_1010229
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846078657120341222225741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24564052438080227481483827 36846078657120341222225741)
  ·
    refine ⟨13817279496420127958334653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36846078657120341222225741 13817279496420127958334653)
    ·
      refine ⟨5181479811157547984375495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13817279496420127958334653 5181479811157547984375495)
      ·
        refine ⟨7772219716736321976563243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5181479811157547984375495 7772219716736321976563243)
        ·
          refine ⟨11658329575104482964844865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7772219716736321976563243 11658329575104482964844865)
          ·
            refine ⟨8743747181328362223633649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11658329575104482964844865 8743747181328362223633649)
            ·
              refine ⟨6557810385996271667725237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8743747181328362223633649 6557810385996271667725237)
              ·
                refine ⟨614794723687150468849241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6557810385996271667725237 614794723687150468849241)
                ·
                  refine ⟨461096042765362851636931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614794723687150468849241 461096042765362851636931)
                  ·
                    rfl

theorem cell20_1010229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_1010229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010229 prefixEnd_1010229 := by exact prefixLift 1010229
  have htrace : WordTrace (prefixWord ++ tailWord_1010229) baseStart_1010229 baseEnd_1010229 := by
    simpa [prefixWord, tailWord_1010229, baseEnd_1010229] using wordTrace_append hprefix tailTrace_1010229
  have hstable : (prefixWord ++ tailWord_1010229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010229).length < 2 ^ (prefixWord ++ tailWord_1010229).sum := by decide
  have hdescent : baseEnd_1010229 < baseStart_1010229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010253 : List Nat := [1, 6, 1, 1, 2, 3, 1, 5]
def baseStart_1010253 : Nat := 118140960795 + 1010253 * 2 ^ 59
def prefixEnd_1010253 : Nat := 4983230072969 + 3 ^ 40 * 1010253 * 2
def baseEnd_1010253 : Nat := 153702332339775144945611

theorem tailTrace_1010253 : CollatzResearch.WordTrace tailWord_1010253 prefixEnd_1010253 153702332339775144945611 := by
  unfold tailWord_1010253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36846954009033393321099413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24564636006022262214066275 36846954009033393321099413)
  ·
    refine ⟨1727200969173440311926535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36846954009033393321099413 1727200969173440311926535)
    ·
      refine ⟨2590801453760160467889803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727200969173440311926535 2590801453760160467889803)
      ·
        refine ⟨3886202180640240701834705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2590801453760160467889803 3886202180640240701834705)
        ·
          refine ⟨2914651635480180526376029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3886202180640240701834705 2914651635480180526376029)
          ·
            refine ⟨1092994363305067697391011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2914651635480180526376029 1092994363305067697391011)
            ·
              refine ⟨1639491544957601546086517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092994363305067697391011 1639491544957601546086517)
              ·
                refine ⟨153702332339775144945611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1639491544957601546086517 153702332339775144945611)
                ·
                  rfl

theorem cell20_1010253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 5].length) (baseStart_1010253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010253 prefixEnd_1010253 := by exact prefixLift 1010253
  have htrace : WordTrace (prefixWord ++ tailWord_1010253) baseStart_1010253 baseEnd_1010253 := by
    simpa [prefixWord, tailWord_1010253, baseEnd_1010253] using wordTrace_append hprefix tailTrace_1010253
  have hstable : (prefixWord ++ tailWord_1010253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010253).length < 2 ^ (prefixWord ++ tailWord_1010253).sum := by decide
  have hdescent : baseEnd_1010253 < baseStart_1010253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010257 : List Nat := [1, 2, 2, 1, 3, 3, 3, 5]
def baseStart_1010257 : Nat := 118140960795 + 1010257 * 2 ^ 59
def prefixEnd_1010257 : Nat := 4983230072969 + 3 ^ 40 * 1010257 * 2
def baseEnd_1010257 : Nat := 153702940909439732901161

theorem tailTrace_1010257 : CollatzResearch.WordTrace tailWord_1010257 prefixEnd_1010257 153702940909439732901161 := by
  unfold tailWord_1010257
  simp only [CollatzResearch.WordTrace]
  refine ⟨36847099901018902004245025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24564733267345934669496683 36847099901018902004245025)
  ·
    refine ⟨27635324925764176503183769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36847099901018902004245025 27635324925764176503183769)
    ·
      refine ⟨20726493694323132377387827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27635324925764176503183769 20726493694323132377387827)
      ·
        refine ⟨31089740541484698566081741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20726493694323132377387827 31089740541484698566081741)
        ·
          refine ⟨11658652703056761962280653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31089740541484698566081741 11658652703056761962280653)
          ·
            refine ⟨4371994763646285735855245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11658652703056761962280653 4371994763646285735855245)
            ·
              refine ⟨1639498036367357150945717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4371994763646285735855245 1639498036367357150945717)
              ·
                refine ⟨153702940909439732901161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1639498036367357150945717 153702940909439732901161)
                ·
                  rfl

theorem cell20_1010257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 5].length) (baseStart_1010257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010257 prefixEnd_1010257 := by exact prefixLift 1010257
  have htrace : WordTrace (prefixWord ++ tailWord_1010257) baseStart_1010257 baseEnd_1010257 := by
    simpa [prefixWord, tailWord_1010257, baseEnd_1010257] using wordTrace_append hprefix tailTrace_1010257
  have hstable : (prefixWord ++ tailWord_1010257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010257).length < 2 ^ (prefixWord ++ tailWord_1010257).sum := by decide
  have hdescent : baseEnd_1010257 < baseStart_1010257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010294 : List Nat := [5, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_1010294 : Nat := 118140960795 + 1010294 * 2 ^ 59
def prefixEnd_1010294 : Nat := 4983230072969 + 3 ^ 40 * 1010294 * 2
def baseEnd_1010294 : Nat := 461125710536511514469999

theorem tailTrace_1010294 : CollatzResearch.WordTrace tailWord_1010294 prefixEnd_1010294 461125710536511514469999 := by
  unfold tailWord_1010294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303028087617803582708871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24565632934589904882227957 2303028087617803582708871)
  ·
    refine ⟨3454542131426705374063307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303028087617803582708871 3454542131426705374063307)
    ·
      refine ⟨5181813197140058061094961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3454542131426705374063307 5181813197140058061094961)
      ·
        refine ⟨3886359897855043545821221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5181813197140058061094961 3886359897855043545821221)
        ·
          refine ⟨728692480847820664841479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3886359897855043545821221 728692480847820664841479)
          ·
            refine ⟨1093038721271730997262219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728692480847820664841479 1093038721271730997262219)
            ·
              refine ⟨1639558081907596495893329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093038721271730997262219 1639558081907596495893329)
              ·
                refine ⟨1229668561430697371919997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639558081907596495893329 1229668561430697371919997)
                ·
                  refine ⟨461125710536511514469999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229668561430697371919997 461125710536511514469999)
                  ·
                    rfl

theorem cell20_1010294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_1010294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010294 prefixEnd_1010294 := by exact prefixLift 1010294
  have htrace : WordTrace (prefixWord ++ tailWord_1010294) baseStart_1010294 baseEnd_1010294 := by
    simpa [prefixWord, tailWord_1010294, baseEnd_1010294] using wordTrace_append hprefix tailTrace_1010294
  have hstable : (prefixWord ++ tailWord_1010294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010294).length < 2 ^ (prefixWord ++ tailWord_1010294).sum := by decide
  have hdescent : baseEnd_1010294 < baseStart_1010294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010305 : List Nat := [1, 2, 4, 2, 1, 1, 1, 6, 2]
def baseStart_1010305 : Nat := 118140960795 + 1010305 * 2 ^ 59
def prefixEnd_1010305 : Nat := 4983230072969 + 3 ^ 40 * 1010305 * 2
def baseEnd_1010305 : Nat := 461130731236244365103287

theorem tailTrace_1010305 : CollatzResearch.WordTrace tailWord_1010305 prefixEnd_1010305 461130731236244365103287 := by
  unfold tailWord_1010305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36848850604845006201992369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24565900403230004134661579 36848850604845006201992369)
  ·
    refine ⟨27636637953633754651494277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36848850604845006201992369 27636637953633754651494277)
    ·
      refine ⟨5181869616306328997155177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27636637953633754651494277 5181869616306328997155177)
      ·
        refine ⟨3886402212229746747866383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5181869616306328997155177 3886402212229746747866383)
        ·
          refine ⟨5829603318344620121799575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3886402212229746747866383 5829603318344620121799575)
          ·
            refine ⟨8744404977516930182699363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829603318344620121799575 8744404977516930182699363)
            ·
              refine ⟨13116607466275395274049045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744404977516930182699363 13116607466275395274049045)
              ·
                refine ⟨614840974981659153471049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13116607466275395274049045 614840974981659153471049)
                ·
                  refine ⟨461130731236244365103287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614840974981659153471049 461130731236244365103287)
                  ·
                    rfl

theorem cell20_1010305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_1010305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010305 prefixEnd_1010305 := by exact prefixLift 1010305
  have htrace : WordTrace (prefixWord ++ tailWord_1010305) baseStart_1010305 baseEnd_1010305 := by
    simpa [prefixWord, tailWord_1010305, baseEnd_1010305] using wordTrace_append hprefix tailTrace_1010305
  have hstable : (prefixWord ++ tailWord_1010305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010305).length < 2 ^ (prefixWord ++ tailWord_1010305).sum := by decide
  have hdescent : baseEnd_1010305 < baseStart_1010305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010340 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1010340 : Nat := 118140960795 + 1010340 * 2 ^ 59
def prefixEnd_1010340 : Nat := 4983230072969 + 3 ^ 40 * 1010340 * 2
def baseEnd_1010340 : Nat := 461146706189939798936477

theorem tailTrace_1010340 : CollatzResearch.WordTrace tailWord_1010340 prefixEnd_1010340 461146706189939798936477 := by
  unfold tailWord_1010340
  simp only [CollatzResearch.WordTrace]
  refine ⟨18425063579859103589758237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24566751439812138119677649 18425063579859103589758237)
  ·
    refine ⟨6909398842447163846159339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18425063579859103589758237 6909398842447163846159339)
    ·
      refine ⟨10364098263670745769239009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6909398842447163846159339 10364098263670745769239009)
      ·
        refine ⟨7773073697753059326929257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10364098263670745769239009 7773073697753059326929257)
        ·
          refine ⟨5829805273314794495196943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7773073697753059326929257 5829805273314794495196943)
          ·
            refine ⟨8744707909972191742795415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5829805273314794495196943 8744707909972191742795415)
            ·
              refine ⟨13117061864958287614193123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8744707909972191742795415 13117061864958287614193123)
              ·
                refine ⟨19675592797437431421289685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13117061864958287614193123 19675592797437431421289685)
                ·
                  refine ⟨461146706189939798936477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19675592797437431421289685 461146706189939798936477)
                  ·
                    rfl

theorem cell20_1010340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1010340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010340 prefixEnd_1010340 := by exact prefixLift 1010340
  have htrace : WordTrace (prefixWord ++ tailWord_1010340) baseStart_1010340 baseEnd_1010340 := by
    simpa [prefixWord, tailWord_1010340, baseEnd_1010340] using wordTrace_append hprefix tailTrace_1010340
  have hstable : (prefixWord ++ tailWord_1010340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010340).length < 2 ^ (prefixWord ++ tailWord_1010340).sum := by decide
  have hdescent : baseEnd_1010340 < baseStart_1010340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010346 : List Nat := [3, 1, 5, 2, 2, 1, 6]
def baseStart_1010346 : Nat := 118140960795 + 1010346 * 2 ^ 59
def prefixEnd_1010346 : Nat := 4983230072969 + 3 ^ 40 * 1010346 * 2
def baseEnd_1010346 : Nat := 51238827194825604970717

theorem tailTrace_1010346 : CollatzResearch.WordTrace tailWord_1010346 prefixEnd_1010346 51238827194825604970717 := by
  unfold tailWord_1010346
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212586499424117551058723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24566897331797646802823261 9212586499424117551058723)
  ·
    refine ⟨13818879749136176326588085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9212586499424117551058723 13818879749136176326588085)
    ·
      refine ⟨1295519976481516530617633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13818879749136176326588085 1295519976481516530617633)
      ·
        refine ⟨971639982361137397963225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1295519976481516530617633 971639982361137397963225)
        ·
          refine ⟨728729986770853048472419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971639982361137397963225 728729986770853048472419)
          ·
            refine ⟨1093094980156279572708629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728729986770853048472419 1093094980156279572708629)
            ·
              refine ⟨51238827194825604970717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1093094980156279572708629 51238827194825604970717)
              ·
                rfl

theorem cell20_1010346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 6].length) (baseStart_1010346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010346 prefixEnd_1010346 := by exact prefixLift 1010346
  have htrace : WordTrace (prefixWord ++ tailWord_1010346) baseStart_1010346 baseEnd_1010346 := by
    simpa [prefixWord, tailWord_1010346, baseEnd_1010346] using wordTrace_append hprefix tailTrace_1010346
  have hstable : (prefixWord ++ tailWord_1010346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010346).length < 2 ^ (prefixWord ++ tailWord_1010346).sum := by decide
  have hdescent : baseEnd_1010346 < baseStart_1010346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010350 : List Nat := [4, 1, 4, 1, 1, 1, 8]
def baseStart_1010350 : Nat := 118140960795 + 1010350 * 2 ^ 59
def prefixEnd_1010350 : Nat := 4983230072969 + 3 ^ 40 * 1010350 * 2
def baseEnd_1010350 : Nat := 51239030051380467622567

theorem tailTrace_1010350 : CollatzResearch.WordTrace tailWord_1010350 prefixEnd_1010350 51239030051380467622567 := by
  unfold tailWord_1010350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606311486210247360922563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24566994593121319258253669 4606311486210247360922563)
  ·
    refine ⟨6909467229315371041383845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4606311486210247360922563 6909467229315371041383845)
    ·
      refine ⟨1295525105496632070259471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6909467229315371041383845 1295525105496632070259471)
      ·
        refine ⟨1943287658244948105389207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295525105496632070259471 1943287658244948105389207)
        ·
          refine ⟨2914931487367422158083811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943287658244948105389207 2914931487367422158083811)
          ·
            refine ⟨4372397231051133237125717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914931487367422158083811 4372397231051133237125717)
            ·
              refine ⟨51239030051380467622567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4372397231051133237125717 51239030051380467622567)
              ·
                rfl

theorem cell20_1010350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 8].length) (baseStart_1010350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010350 prefixEnd_1010350 := by exact prefixLift 1010350
  have htrace : WordTrace (prefixWord ++ tailWord_1010350) baseStart_1010350 baseEnd_1010350 := by
    simpa [prefixWord, tailWord_1010350, baseEnd_1010350] using wordTrace_append hprefix tailTrace_1010350
  have hstable : (prefixWord ++ tailWord_1010350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010350).length < 2 ^ (prefixWord ++ tailWord_1010350).sum := by decide
  have hdescent : baseEnd_1010350 < baseStart_1010350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010357 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1010357 : Nat := 118140960795 + 1010357 * 2 ^ 59
def prefixEnd_1010357 : Nat := 4983230072969 + 3 ^ 40 * 1010357 * 2
def baseEnd_1010357 : Nat := 461154465453163295369741

theorem tailTrace_1010357 : CollatzResearch.WordTrace tailWord_1010357 prefixEnd_1010357 461154465453163295369741 := by
  unfold tailWord_1010357
  simp only [CollatzResearch.WordTrace]
  refine ⟨36850747200656619082885325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24567164800437746055256883 36850747200656619082885325)
  ·
    refine ⟨13819030200246232156081997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36850747200656619082885325 13819030200246232156081997)
    ·
      refine ⟨5182136325092337058530749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13819030200246232156081997 5182136325092337058530749)
      ·
        refine ⟨1943301121909626396949031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5182136325092337058530749 1943301121909626396949031)
        ·
          refine ⟨2914951682864439595423547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943301121909626396949031 2914951682864439595423547)
          ·
            refine ⟨4372427524296659393135321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2914951682864439595423547 4372427524296659393135321)
            ·
              refine ⟨3279320643222494544851491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4372427524296659393135321 3279320643222494544851491)
              ·
                refine ⟨4918980964833741817277237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279320643222494544851491 4918980964833741817277237)
                ·
                  refine ⟨461154465453163295369741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4918980964833741817277237 461154465453163295369741)
                  ·
                    rfl

theorem cell20_1010357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1010357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010357 prefixEnd_1010357 := by exact prefixLift 1010357
  have htrace : WordTrace (prefixWord ++ tailWord_1010357) baseStart_1010357 baseEnd_1010357 := by
    simpa [prefixWord, tailWord_1010357, baseEnd_1010357] using wordTrace_append hprefix tailTrace_1010357
  have hstable : (prefixWord ++ tailWord_1010357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010357).length < 2 ^ (prefixWord ++ tailWord_1010357).sum := by decide
  have hdescent : baseEnd_1010357 < baseStart_1010357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010385 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 6]
def baseStart_1010385 : Nat := 118140960795 + 1010385 * 2 ^ 59
def prefixEnd_1010385 : Nat := 4983230072969 + 3 ^ 40 * 1010385 * 2
def baseEnd_1010385 : Nat := 461167245416119642436293

theorem tailTrace_1010385 : CollatzResearch.WordTrace tailWord_1010385 prefixEnd_1010385 461167245416119642436293 := by
  unfold tailWord_1010385
  simp only [CollatzResearch.WordTrace]
  refine ⟨36851768444555179864904609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24567845629703453243269739 36851768444555179864904609)
  ·
    refine ⟨27638826333416384898678457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36851768444555179864904609 27638826333416384898678457)
    ·
      refine ⟨20729119750062288674008843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27638826333416384898678457 20729119750062288674008843)
      ·
        refine ⟨31093679625093433011013265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729119750062288674008843 31093679625093433011013265)
        ·
          refine ⟨23320259718820074758259949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31093679625093433011013265 23320259718820074758259949)
          ·
            refine ⟨8745097394557528034347481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23320259718820074758259949 8745097394557528034347481)
            ·
              refine ⟨6558823045918146025760611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8745097394557528034347481 6558823045918146025760611)
              ·
                refine ⟨9838234568877219038640917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6558823045918146025760611 9838234568877219038640917)
                ·
                  refine ⟨461167245416119642436293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9838234568877219038640917 461167245416119642436293)
                  ·
                    rfl

theorem cell20_1010385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 6].length) (baseStart_1010385 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010385 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010385 prefixEnd_1010385 := by exact prefixLift 1010385
  have htrace : WordTrace (prefixWord ++ tailWord_1010385) baseStart_1010385 baseEnd_1010385 := by
    simpa [prefixWord, tailWord_1010385, baseEnd_1010385] using wordTrace_append hprefix tailTrace_1010385
  have hstable : (prefixWord ++ tailWord_1010385).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010385).length < 2 ^ (prefixWord ++ tailWord_1010385).sum := by decide
  have hdescent : baseEnd_1010385 < baseStart_1010385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010423 : List Nat := [1, 1, 3, 1, 1, 1, 3, 5, 4]
def baseStart_1010423 : Nat := 118140960795 + 1010423 * 2 ^ 59
def prefixEnd_1010423 : Nat := 4983230072969 + 3 ^ 40 * 1010423 * 2
def baseEnd_1010423 : Nat := 461184589651560399169471

theorem tailTrace_1010423 : CollatzResearch.WordTrace tailWord_1010423 prefixEnd_1010423 461184589651560399169471 := by
  unfold tailWord_1010423
  simp only [CollatzResearch.WordTrace]
  refine ⟨36853154418417512354787923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24568769612278341569858615 36853154418417512354787923)
  ·
    refine ⟨55279731627626268532181885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36853154418417512354787923 55279731627626268532181885)
    ·
      refine ⟨20729899360359850699568207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55279731627626268532181885 20729899360359850699568207)
      ·
        refine ⟨31094849040539776049352311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20729899360359850699568207 31094849040539776049352311)
        ·
          refine ⟨46642273560809664074028467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31094849040539776049352311 46642273560809664074028467)
          ·
            refine ⟨69963410341214496111042701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46642273560809664074028467 69963410341214496111042701)
            ·
              refine ⟨26236278877955436041641013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69963410341214496111042701 26236278877955436041641013)
              ·
                refine ⟨2459651144808322128903845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26236278877955436041641013 2459651144808322128903845)
                ·
                  refine ⟨461184589651560399169471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459651144808322128903845 461184589651560399169471)
                  ·
                    rfl

theorem cell20_1010423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 5, 4].length) (baseStart_1010423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010423 prefixEnd_1010423 := by exact prefixLift 1010423
  have htrace : WordTrace (prefixWord ++ tailWord_1010423) baseStart_1010423 baseEnd_1010423 := by
    simpa [prefixWord, tailWord_1010423, baseEnd_1010423] using wordTrace_append hprefix tailTrace_1010423
  have hstable : (prefixWord ++ tailWord_1010423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010423).length < 2 ^ (prefixWord ++ tailWord_1010423).sum := by decide
  have hdescent : baseEnd_1010423 < baseStart_1010423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010440 : List Nat := [2, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_1010440 : Nat := 118140960795 + 1010440 * 2 ^ 59
def prefixEnd_1010440 : Nat := 4983230072969 + 3 ^ 40 * 1010440 * 2
def baseEnd_1010440 : Nat := 461192348914783895602735

theorem tailTrace_1010440 : CollatzResearch.WordTrace tailWord_1010440 prefixEnd_1010440 461192348914783895602735 := by
  unfold tailWord_1010440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426887229677962129078387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24569182972903949505437849 18426887229677962129078387)
  ·
    refine ⟨27640330844516943193617581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18426887229677962129078387 27640330844516943193617581)
    ·
      refine ⟨10365124066693853697606593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27640330844516943193617581 10365124066693853697606593)
      ·
        refine ⟨7773843050020390273204945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10365124066693853697606593 7773843050020390273204945)
        ·
          refine ⟨5830382287515292704903709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7773843050020390273204945 5830382287515292704903709)
          ·
            refine ⟨2186393357818234764338891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5830382287515292704903709 2186393357818234764338891)
            ·
              refine ⟨3279590036727352146508337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186393357818234764338891 3279590036727352146508337)
              ·
                refine ⟨2459692527545514109881253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3279590036727352146508337 2459692527545514109881253)
                ·
                  refine ⟨461192348914783895602735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459692527545514109881253 461192348914783895602735)
                  ·
                    rfl

theorem cell20_1010440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_1010440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010440 prefixEnd_1010440 := by exact prefixLift 1010440
  have htrace : WordTrace (prefixWord ++ tailWord_1010440) baseStart_1010440 baseEnd_1010440 := by
    simpa [prefixWord, tailWord_1010440, baseEnd_1010440] using wordTrace_append hprefix tailTrace_1010440
  have hstable : (prefixWord ++ tailWord_1010440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010440).length < 2 ^ (prefixWord ++ tailWord_1010440).sum := by decide
  have hdescent : baseEnd_1010440 < baseStart_1010440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010447 : List Nat := [1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_1010447 : Nat := 118140960795 + 1010447 * 2 ^ 59
def prefixEnd_1010447 : Nat := 4983230072969 + 3 ^ 40 * 1010447 * 2
def baseEnd_1010447 : Nat := 153731847968507660789791

theorem tailTrace_1010447 : CollatzResearch.WordTrace tailWord_1010447 prefixEnd_1010447 153731847968507660789791 := by
  unfold tailWord_1010447
  simp only [CollatzResearch.WordTrace]
  refine ⟨36854029770330564453661595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24569353180220376302441063 36854029770330564453661595)
  ·
    refine ⟨55281044655495846680492393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36854029770330564453661595 55281044655495846680492393)
    ·
      refine ⟨41460783491621885010369295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55281044655495846680492393 41460783491621885010369295)
      ·
        refine ⟨62191175237432827515553943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41460783491621885010369295 62191175237432827515553943)
        ·
          refine ⟨93286762856149241273330915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62191175237432827515553943 93286762856149241273330915)
          ·
            refine ⟨139930144284223861909996373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93286762856149241273330915 139930144284223861909996373)
            ·
              refine ⟨819903189165374190878885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 139930144284223861909996373 819903189165374190878885)
              ·
                refine ⟨153731847968507660789791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 819903189165374190878885 153731847968507660789791)
                ·
                  rfl

theorem cell20_1010447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_1010447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010447 prefixEnd_1010447 := by exact prefixLift 1010447
  have htrace : WordTrace (prefixWord ++ tailWord_1010447) baseStart_1010447 baseEnd_1010447 := by
    simpa [prefixWord, tailWord_1010447, baseEnd_1010447] using wordTrace_append hprefix tailTrace_1010447
  have hstable : (prefixWord ++ tailWord_1010447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010447).length < 2 ^ (prefixWord ++ tailWord_1010447).sum := by decide
  have hdescent : baseEnd_1010447 < baseStart_1010447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010474 : List Nat := [3, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_1010474 : Nat := 118140960795 + 1010474 * 2 ^ 59
def prefixEnd_1010474 : Nat := 4983230072969 + 3 ^ 40 * 1010474 * 2
def baseEnd_1010474 : Nat := 461207867441230888469263

theorem tailTrace_1010474 : CollatzResearch.WordTrace tailWord_1010474 prefixEnd_1010474 461207867441230888469263 := by
  unfold tailWord_1010474
  simp only [CollatzResearch.WordTrace]
  refine ⟨9213753635308187016223619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24570009694155165376596317 9213753635308187016223619)
  ·
    refine ⟨13820630452962280524335429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9213753635308187016223619 13820630452962280524335429)
    ·
      refine ⟨2591368209930427598312893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13820630452962280524335429 2591368209930427598312893)
      ·
        refine ⟨971763078723910349367335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2591368209930427598312893 971763078723910349367335)
        ·
          refine ⟨1457644618085865524051003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971763078723910349367335 1457644618085865524051003)
          ·
            refine ⟨2186466927128798286076505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457644618085865524051003 2186466927128798286076505)
            ·
              refine ⟨1639850195346598714557379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186466927128798286076505 1639850195346598714557379)
              ·
                refine ⟨2459775293019898071836069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639850195346598714557379 2459775293019898071836069)
                ·
                  refine ⟨461207867441230888469263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459775293019898071836069 461207867441230888469263)
                  ·
                    rfl

theorem cell20_1010474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_1010474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010474 prefixEnd_1010474 := by exact prefixLift 1010474
  have htrace : WordTrace (prefixWord ++ tailWord_1010474) baseStart_1010474 baseEnd_1010474 := by
    simpa [prefixWord, tailWord_1010474, baseEnd_1010474] using wordTrace_append hprefix tailTrace_1010474
  have hstable : (prefixWord ++ tailWord_1010474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010474).length < 2 ^ (prefixWord ++ tailWord_1010474).sum := by decide
  have hdescent : baseEnd_1010474 < baseStart_1010474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010499 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_1010499 : Nat := 118140960795 + 1010499 * 2 ^ 59
def prefixEnd_1010499 : Nat := 4983230072969 + 3 ^ 40 * 1010499 * 2
def baseEnd_1010499 : Nat := 461219278122441912635827

theorem tailTrace_1010499 : CollatzResearch.WordTrace tailWord_1010499 prefixEnd_1010499 461219278122441912635827 := by
  unfold tailWord_1010499
  simp only [CollatzResearch.WordTrace]
  refine ⟨36855926366142177334554551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24570617577428118223036367 36855926366142177334554551)
  ·
    refine ⟨55283889549213266001831827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36855926366142177334554551 55283889549213266001831827)
    ·
      refine ⟨82925834323819899002747741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55283889549213266001831827 82925834323819899002747741)
      ·
        refine ⟨31097187871432462126030403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82925834323819899002747741 31097187871432462126030403)
        ·
          refine ⟨46645781807148693189045605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31097187871432462126030403 46645781807148693189045605)
          ·
            refine ⟨8746084088840379972946051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46645781807148693189045605 8746084088840379972946051)
            ·
              refine ⟨13119126133260569959419077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8746084088840379972946051 13119126133260569959419077)
              ·
                refine ⟨2459836149986356867391077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13119126133260569959419077 2459836149986356867391077)
                ·
                  refine ⟨461219278122441912635827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2459836149986356867391077 461219278122441912635827)
                  ·
                    rfl

theorem cell20_1010499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_1010499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010499 prefixEnd_1010499 := by exact prefixLift 1010499
  have htrace : WordTrace (prefixWord ++ tailWord_1010499) baseStart_1010499 baseEnd_1010499 := by
    simpa [prefixWord, tailWord_1010499, baseEnd_1010499] using wordTrace_append hprefix tailTrace_1010499
  have hstable : (prefixWord ++ tailWord_1010499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010499).length < 2 ^ (prefixWord ++ tailWord_1010499).sum := by decide
  have hdescent : baseEnd_1010499 < baseStart_1010499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010544 : List Nat := [2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_1010544 : Nat := 118140960795 + 1010544 * 2 ^ 59
def prefixEnd_1010544 : Nat := 4983230072969 + 3 ^ 40 * 1010544 * 2
def baseEnd_1010544 : Nat := 153746605782873918711881

theorem tailTrace_1010544 : CollatzResearch.WordTrace tailWord_1010544 prefixEnd_1010544 153746605782873918711881 := by
  unfold tailWord_1010544
  simp only [CollatzResearch.WordTrace]
  refine ⟨18428783825489575009971343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24571711767319433346628457 18428783825489575009971343)
  ·
    refine ⟨27643175738234362514957015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18428783825489575009971343 27643175738234362514957015)
    ·
      refine ⟨41464763607351543772435523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27643175738234362514957015 41464763607351543772435523)
      ·
        refine ⟨62197145411027315658653285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41464763607351543772435523 62197145411027315658653285)
        ·
          refine ⟨11661964764567621685997491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62197145411027315658653285 11661964764567621685997491)
          ·
            refine ⟨17492947146851432528996237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11661964764567621685997491 17492947146851432528996237)
            ·
              refine ⟨6559855180069287198373589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17492947146851432528996237 6559855180069287198373589)
              ·
                refine ⟨153746605782873918711881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6559855180069287198373589 153746605782873918711881)
                ·
                  rfl

theorem cell20_1010544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_1010544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010544 prefixEnd_1010544 := by exact prefixLift 1010544
  have htrace : WordTrace (prefixWord ++ tailWord_1010544) baseStart_1010544 baseEnd_1010544 := by
    simpa [prefixWord, tailWord_1010544, baseEnd_1010544] using wordTrace_append hprefix tailTrace_1010544
  have hstable : (prefixWord ++ tailWord_1010544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010544).length < 2 ^ (prefixWord ++ tailWord_1010544).sum := by decide
  have hdescent : baseEnd_1010544 < baseStart_1010544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010547 : List Nat := [1, 1, 1, 2, 2, 1, 8, 1, 3]
def baseStart_1010547 : Nat := 118140960795 + 1010547 * 2 ^ 59
def prefixEnd_1010547 : Nat := 4983230072969 + 3 ^ 40 * 1010547 * 2
def baseEnd_1010547 : Nat := 461241186630367079035631

theorem tailTrace_1010547 : CollatzResearch.WordTrace tailWord_1010547 prefixEnd_1010547 461241186630367079035631 := by
  unfold tailWord_1010547
  simp only [CollatzResearch.WordTrace]
  refine ⟨36857677069968281532301895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24571784713312187688201263 36857677069968281532301895)
  ·
    refine ⟨55286515604952422298452843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36857677069968281532301895 55286515604952422298452843)
    ·
      refine ⟨82929773407428633447679265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55286515604952422298452843 82929773407428633447679265)
      ·
        refine ⟨62197330055571475085759449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82929773407428633447679265 62197330055571475085759449)
        ·
          refine ⟨46647997541678606314319587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62197330055571475085759449 46647997541678606314319587)
          ·
            refine ⟨69971996312517909471479381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46647997541678606314319587 69971996312517909471479381)
            ·
              refine ⟨819984331787319251618899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 69971996312517909471479381 819984331787319251618899)
              ·
                refine ⟨1229976497680978877428349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819984331787319251618899 1229976497680978877428349)
                ·
                  refine ⟨461241186630367079035631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229976497680978877428349 461241186630367079035631)
                  ·
                    rfl

theorem cell20_1010547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 8, 1, 3].length) (baseStart_1010547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010547 prefixEnd_1010547 := by exact prefixLift 1010547
  have htrace : WordTrace (prefixWord ++ tailWord_1010547) baseStart_1010547 baseEnd_1010547 := by
    simpa [prefixWord, tailWord_1010547, baseEnd_1010547] using wordTrace_append hprefix tailTrace_1010547
  have hstable : (prefixWord ++ tailWord_1010547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010547).length < 2 ^ (prefixWord ++ tailWord_1010547).sum := by decide
  have hdescent : baseEnd_1010547 < baseStart_1010547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010578 : List Nat := [3, 2, 3, 2, 3, 7]
def baseStart_1010578 : Nat := 118140960795 + 1010578 * 2 ^ 59
def prefixEnd_1010578 : Nat := 4983230072969 + 3 ^ 40 * 1010578 * 2
def baseEnd_1010578 : Nat := 17083530958335879592673

theorem tailTrace_1010578 : CollatzResearch.WordTrace tailWord_1010578 prefixEnd_1010578 17083530958335879592673 := by
  unfold tailWord_1010578
  simp only [CollatzResearch.WordTrace]
  refine ⟨9214701933213993456670097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24572538488570649217786925 9214701933213993456670097)
  ·
    refine ⟨6911026449910495092502573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9214701933213993456670097 6911026449910495092502573)
    ·
      refine ⟨2591634918716435659688465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6911026449910495092502573 2591634918716435659688465)
      ·
        refine ⟨1943726189037326744766349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2591634918716435659688465 1943726189037326744766349)
        ·
          refine ⟨728897320888997529287381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1943726189037326744766349 728897320888997529287381)
          ·
            refine ⟨17083530958335879592673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 728897320888997529287381 17083530958335879592673)
            ·
              rfl

theorem cell20_1010578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 7].length) (baseStart_1010578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010578 prefixEnd_1010578 := by exact prefixLift 1010578
  have htrace : WordTrace (prefixWord ++ tailWord_1010578) baseStart_1010578 baseEnd_1010578 := by
    simpa [prefixWord, tailWord_1010578, baseEnd_1010578] using wordTrace_append hprefix tailTrace_1010578
  have hstable : (prefixWord ++ tailWord_1010578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010578).length < 2 ^ (prefixWord ++ tailWord_1010578).sum := by decide
  have hdescent : baseEnd_1010578 < baseStart_1010578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010588 : List Nat := [2, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_1010588 : Nat := 118140960795 + 1010588 * 2 ^ 59
def prefixEnd_1010588 : Nat := 4983230072969 + 3 ^ 40 * 1010588 * 2
def baseEnd_1010588 : Nat := 461259900147553158668797

theorem tailTrace_1010588 : CollatzResearch.WordTrace tailWord_1010588 prefixEnd_1010588 461259900147553158668797 := by
  unfold tailWord_1010588
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429586231409872767272209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24572781641879830356362945 18429586231409872767272209)
  ·
    refine ⟨13822189673557404575454157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18429586231409872767272209 13822189673557404575454157)
    ·
      refine ⟨5183321127584026715795309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13822189673557404575454157 5183321127584026715795309)
      ·
        refine ⟨1943745422844010018423241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5183321127584026715795309 1943745422844010018423241)
        ·
          refine ⟨1457809067133007513817431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1943745422844010018423241 1457809067133007513817431)
          ·
            refine ⟨2186713600699511270726147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457809067133007513817431 2186713600699511270726147)
            ·
              refine ⟨3280070401049266906089221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186713600699511270726147 3280070401049266906089221)
              ·
                refine ⟨615013200196737544891729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3280070401049266906089221 615013200196737544891729)
                ·
                  refine ⟨461259900147553158668797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615013200196737544891729 461259900147553158668797)
                  ·
                    rfl

theorem cell20_1010588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_1010588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010588 prefixEnd_1010588 := by exact prefixLift 1010588
  have htrace : WordTrace (prefixWord ++ tailWord_1010588) baseStart_1010588 baseEnd_1010588 := by
    simpa [prefixWord, tailWord_1010588, baseEnd_1010588] using wordTrace_append hprefix tailTrace_1010588
  have hstable : (prefixWord ++ tailWord_1010588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010588).length < 2 ^ (prefixWord ++ tailWord_1010588).sum := by decide
  have hdescent : baseEnd_1010588 < baseStart_1010588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010627 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_1010627 : Nat := 118140960795 + 1010627 * 2 ^ 59
def prefixEnd_1010627 : Nat := 4983230072969 + 3 ^ 40 * 1010627 * 2
def baseEnd_1010627 : Nat := 461277700810242356368637

theorem tailTrace_1010627 : CollatzResearch.WordTrace tailWord_1010627 prefixEnd_1010627 461277700810242356368637 := by
  unfold tailWord_1010627
  simp only [CollatzResearch.WordTrace]
  refine ⟨36860594909678455195214135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24573729939785636796809423 36860594909678455195214135)
  ·
    refine ⟨55290892364517682792821203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36860594909678455195214135 55290892364517682792821203)
    ·
      refine ⟨82936338546776524189231805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55290892364517682792821203 82936338546776524189231805)
      ·
        refine ⟨31101126955041196570961927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82936338546776524189231805 31101126955041196570961927)
        ·
          refine ⟨46651690432561794856442891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31101126955041196570961927 46651690432561794856442891)
          ·
            refine ⟨69977535648842692284664337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46651690432561794856442891 69977535648842692284664337)
            ·
              refine ⟨52483151736632019213498253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69977535648842692284664337 52483151736632019213498253)
              ·
                refine ⟨19681181901237007205061845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52483151736632019213498253 19681181901237007205061845)
                ·
                  refine ⟨461277700810242356368637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19681181901237007205061845 461277700810242356368637)
                  ·
                    rfl

theorem cell20_1010627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_1010627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010627 prefixEnd_1010627 := by exact prefixLift 1010627
  have htrace : WordTrace (prefixWord ++ tailWord_1010627) baseStart_1010627 baseEnd_1010627 := by
    simpa [prefixWord, tailWord_1010627, baseEnd_1010627] using wordTrace_append hprefix tailTrace_1010627
  have hstable : (prefixWord ++ tailWord_1010627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010627).length < 2 ^ (prefixWord ++ tailWord_1010627).sum := by decide
  have hdescent : baseEnd_1010627 < baseStart_1010627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010696 : List Nat := [2, 1, 3, 2, 1, 3, 8]
def baseStart_1010696 : Nat := 118140960795 + 1010696 * 2 ^ 59
def prefixEnd_1010696 : Nat := 4983230072969 + 3 ^ 40 * 1010696 * 2
def baseEnd_1010696 : Nat := 51256577143376087007595

theorem tailTrace_1010696 : CollatzResearch.WordTrace tailWord_1010696 prefixEnd_1010696 51256577143376087007595 := by
  unfold tailWord_1010696
  simp only [CollatzResearch.WordTrace]
  refine ⟨18431555773214239989737971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24575407697618986652983961 18431555773214239989737971)
  ·
    refine ⟨27647333659821359984606957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18431555773214239989737971 27647333659821359984606957)
    ·
      refine ⟨10367750122433009994227609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27647333659821359984606957 10367750122433009994227609)
      ·
        refine ⟨7775812591824757495670707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10367750122433009994227609 7775812591824757495670707)
        ·
          refine ⟨11663718887737136243506061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7775812591824757495670707 11663718887737136243506061)
          ·
            refine ⟨4373894582901426091314773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11663718887737136243506061 4373894582901426091314773)
            ·
              refine ⟨51256577143376087007595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4373894582901426091314773 51256577143376087007595)
              ·
                rfl

theorem cell20_1010696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_1010696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010696 prefixEnd_1010696 := by exact prefixLift 1010696
  have htrace : WordTrace (prefixWord ++ tailWord_1010696) baseStart_1010696 baseEnd_1010696 := by
    simpa [prefixWord, tailWord_1010696, baseEnd_1010696] using wordTrace_append hprefix tailTrace_1010696
  have hstable : (prefixWord ++ tailWord_1010696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010696).length < 2 ^ (prefixWord ++ tailWord_1010696).sum := by decide
  have hdescent : baseEnd_1010696 < baseStart_1010696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010702 : List Nat := [4, 1, 1, 2, 2, 3, 3, 2, 2]
def baseStart_1010702 : Nat := 118140960795 + 1010702 * 2 ^ 59
def prefixEnd_1010702 : Nat := 4983230072969 + 3 ^ 40 * 1010702 * 2
def baseEnd_1010702 : Nat := 461311932853875428868331

theorem tailTrace_1010702 : CollatzResearch.WordTrace tailWord_1010702 prefixEnd_1010702 461311932853875428868331 := by
  unfold tailWord_1010702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607916298050842875524295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24575553589604495336129573 4607916298050842875524295)
  ·
    refine ⟨6911874447076264313286443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4607916298050842875524295 6911874447076264313286443)
    ·
      refine ⟨10367811670614396469929665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6911874447076264313286443 10367811670614396469929665)
      ·
        refine ⟨7775858752960797352447249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10367811670614396469929665 7775858752960797352447249)
        ·
          refine ⟨5831894064720598014335437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7775858752960797352447249 5831894064720598014335437)
          ·
            refine ⟨2186960274270224255375789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5831894064720598014335437 2186960274270224255375789)
            ·
              refine ⟨820110102851334095765921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2186960274270224255375789 820110102851334095765921)
              ·
                refine ⟨615082577138500571824441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820110102851334095765921 615082577138500571824441)
                ·
                  refine ⟨461311932853875428868331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615082577138500571824441 461311932853875428868331)
                  ·
                    rfl

theorem cell20_1010702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_1010702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010702 prefixEnd_1010702 := by exact prefixLift 1010702
  have htrace : WordTrace (prefixWord ++ tailWord_1010702) baseStart_1010702 baseEnd_1010702 := by
    simpa [prefixWord, tailWord_1010702, baseEnd_1010702] using wordTrace_append hprefix tailTrace_1010702
  have hstable : (prefixWord ++ tailWord_1010702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010702).length < 2 ^ (prefixWord ++ tailWord_1010702).sum := by decide
  have hdescent : baseEnd_1010702 < baseStart_1010702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010789 : List Nat := [1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_1010789 : Nat := 118140960795 + 1010789 * 2 ^ 59
def prefixEnd_1010789 : Nat := 4983230072969 + 3 ^ 40 * 1010789 * 2
def baseEnd_1010789 : Nat := 153783880674829930989325

theorem tailTrace_1010789 : CollatzResearch.WordTrace tailWord_1010789 prefixEnd_1010789 153783880674829930989325 := by
  unfold tailWord_1010789
  simp only [CollatzResearch.WordTrace]
  refine ⟨36866503535091556862611421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24577669023394371241740947 36866503535091556862611421)
  ·
    refine ⟨13824938825659333823479283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36866503535091556862611421 13824938825659333823479283)
    ·
      refine ⟨20737408238489000735218925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13824938825659333823479283 20737408238489000735218925)
      ·
        refine ⟨7776528089433375275707097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20737408238489000735218925 7776528089433375275707097)
        ·
          refine ⟨5832396067075031456780323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7776528089433375275707097 5832396067075031456780323)
          ·
            refine ⟨8748594100612547185170485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832396067075031456780323 8748594100612547185170485)
            ·
              refine ⟨820180696932426298609733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8748594100612547185170485 820180696932426298609733)
              ·
                refine ⟨153783880674829930989325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820180696932426298609733 153783880674829930989325)
                ·
                  rfl

theorem cell20_1010789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_1010789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010789 prefixEnd_1010789 := by exact prefixLift 1010789
  have htrace : WordTrace (prefixWord ++ tailWord_1010789) baseStart_1010789 baseEnd_1010789 := by
    simpa [prefixWord, tailWord_1010789, baseEnd_1010789] using wordTrace_append hprefix tailTrace_1010789
  have hstable : (prefixWord ++ tailWord_1010789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010789).length < 2 ^ (prefixWord ++ tailWord_1010789).sum := by decide
  have hdescent : baseEnd_1010789 < baseStart_1010789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010820 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_1010820 : Nat := 118140960795 + 1010820 * 2 ^ 59
def prefixEnd_1010820 : Nat := 4983230072969 + 3 ^ 40 * 1010820 * 2
def baseEnd_1010820 : Nat := 461365791269191462934515

theorem tailTrace_1010820 : CollatzResearch.WordTrace tailWord_1010820 prefixEnd_1010820 461365791269191462934515 := by
  unfold tailWord_1010820
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433817098989624578494957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24578422798652832771326609 18433817098989624578494957)
  ·
    refine ⟨6912681412121109216935609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18433817098989624578494957 6912681412121109216935609)
    ·
      refine ⟨5184511059090831912701707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6912681412121109216935609 5184511059090831912701707)
      ·
        refine ⟨7776766588636247869052561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184511059090831912701707 7776766588636247869052561)
        ·
          refine ⟨5832574941477185901789421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7776766588636247869052561 5832574941477185901789421)
          ·
            refine ⟨2187215603053944713171033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5832574941477185901789421 2187215603053944713171033)
            ·
              refine ⟨1640411702290458534878275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187215603053944713171033 1640411702290458534878275)
              ·
                refine ⟨2460617553435687802317413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640411702290458534878275 2460617553435687802317413)
                ·
                  refine ⟨461365791269191462934515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2460617553435687802317413 461365791269191462934515)
                  ·
                    rfl

theorem cell20_1010820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_1010820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010820 prefixEnd_1010820 := by exact prefixLift 1010820
  have htrace : WordTrace (prefixWord ++ tailWord_1010820) baseStart_1010820 baseEnd_1010820 := by
    simpa [prefixWord, tailWord_1010820, baseEnd_1010820] using wordTrace_append hprefix tailTrace_1010820
  have hstable : (prefixWord ++ tailWord_1010820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010820).length < 2 ^ (prefixWord ++ tailWord_1010820).sum := by decide
  have hdescent : baseEnd_1010820 < baseStart_1010820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010830 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_1010830 : Nat := 118140960795 + 1010830 * 2 ^ 59
def prefixEnd_1010830 : Nat := 4983230072969 + 3 ^ 40 * 1010830 * 2
def baseEnd_1010830 : Nat := 461370355541675872601141

theorem tailTrace_1010830 : CollatzResearch.WordTrace tailWord_1010830 prefixEnd_1010830 461370355541675872601141 := by
  unfold tailWord_1010830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608499865992877608106743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24578665951962013909902629 4608499865992877608106743)
  ·
    refine ⟨6912749798989316412160115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608499865992877608106743 6912749798989316412160115)
    ·
      refine ⟨10369124698483974618240173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6912749798989316412160115 10369124698483974618240173)
      ·
        refine ⟨3888421761931490481840065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10369124698483974618240173 3888421761931490481840065)
        ·
          refine ⟨2916316321448617861380049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3888421761931490481840065 2916316321448617861380049)
          ·
            refine ⟨2187237241086463396035037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916316321448617861380049 2187237241086463396035037)
            ·
              refine ⟨820213965407423773513139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2187237241086463396035037 820213965407423773513139)
              ·
                refine ⟨1230320948111135660269709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820213965407423773513139 1230320948111135660269709)
                ·
                  refine ⟨461370355541675872601141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1230320948111135660269709 461370355541675872601141)
                  ·
                    rfl

theorem cell20_1010830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_1010830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010830 prefixEnd_1010830 := by exact prefixLift 1010830
  have htrace : WordTrace (prefixWord ++ tailWord_1010830) baseStart_1010830 baseEnd_1010830 := by
    simpa [prefixWord, tailWord_1010830, baseEnd_1010830] using wordTrace_append hprefix tailTrace_1010830
  have hstable : (prefixWord ++ tailWord_1010830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010830).length < 2 ^ (prefixWord ++ tailWord_1010830).sum := by decide
  have hdescent : baseEnd_1010830 < baseStart_1010830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1010844 : List Nat := [2, 2, 3, 2, 1, 4, 2, 4]
def baseStart_1010844 : Nat := 118140960795 + 1010844 * 2 ^ 59
def prefixEnd_1010844 : Nat := 4983230072969 + 3 ^ 40 * 1010844 * 2
def baseEnd_1010844 : Nat := 153792248507718015378139

theorem tailTrace_1010844 : CollatzResearch.WordTrace tailWord_1010844 prefixEnd_1010844 153792248507718015378139 := by
  unfold tailWord_1010844
  simp only [CollatzResearch.WordTrace]
  refine ⟨18434254774946150627931793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24579006366594867503909057 18434254774946150627931793)
  ·
    refine ⟨13825691081209612970948845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18434254774946150627931793 13825691081209612970948845)
    ·
      refine ⟨5184634155453604864105817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13825691081209612970948845 5184634155453604864105817)
      ·
        refine ⟨3888475616590203648079363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5184634155453604864105817 3888475616590203648079363)
        ·
          refine ⟨5832713424885305472119045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888475616590203648079363 5832713424885305472119045)
          ·
            refine ⟨1093633767165994776022321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5832713424885305472119045 1093633767165994776022321)
            ·
              refine ⟨820225325374496082016741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093633767165994776022321 820225325374496082016741)
              ·
                refine ⟨153792248507718015378139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 820225325374496082016741 153792248507718015378139)
                ·
                  rfl

theorem cell20_1010844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_1010844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_1010844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_1010844 prefixEnd_1010844 := by exact prefixLift 1010844
  have htrace : WordTrace (prefixWord ++ tailWord_1010844) baseStart_1010844 baseEnd_1010844 := by
    simpa [prefixWord, tailWord_1010844, baseEnd_1010844] using wordTrace_append hprefix tailTrace_1010844
  have hstable : (prefixWord ++ tailWord_1010844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1010844).length < 2 ^ (prefixWord ++ tailWord_1010844).sum := by decide
  have hdescent : baseEnd_1010844 < baseStart_1010844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1010844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
